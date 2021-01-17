/// Functions to compute algebras of subobjects and perform operations on them.
[<RequireQualifiedAccess>]
module Subobject

/// Subobject functor.
let sub (cat: Category<'A>)
        : GenericFunctor<(Presheaf<'A, 'S> -> Set<Presheaf<'A, 'S>>), Morphism<'A, 'S, 'T> -> Map<Presheaf<'A, 'T>, Presheaf<'A, 'S>>> =
    let name = Name.ofString "Sub"

    // Gives a descriptive name for a subpresheaf with the specified objects and arrow maps.
    let nameSubpresheaf (i: int) (F: Presheaf<'A, 'S>) (ob: Map<'A, Set<'S>>) (ar: Map<Arrow<'A>, Map<'S, 'S>>): Name =
        if F.Ob = ob && F.Ar = ar then Name.sub F.Name Name.top
        else if Map.exists (fun _ X -> X <> Set.empty) ob then Name.sub F.Name (Name.ofInt i)
        else Name.sub F.Name Name.bot

    let ob (F: Presheaf<'A, 'S>): Set<Presheaf<'A, 'S>> =
        let presheaves =
            [ for A in Map.dom F.Ob do
                [ for X in Set.powerset F.Ob.[A] do
                    (A, X) ] ]
            |> List.listProduct
            |> List.map map
            |> List.map (fun ob ->
                ob,
                map [ for a in Map.dom F.Ar do
                          (a, Map.restrict F.Ar.[a] ob.[a.Cod]) ])
            |> List.filter (fun (ob, ar) -> Presheaf.isPresheaf cat ob ar)
            |> List.mapi (fun i (ob, ar) ->
                let name = nameSubpresheaf i F ob ar
                let presheaf = { Name = name; Ob = ob; Ar = ar }
                presheaf)
            |> set

        presheaves

    let ar (n: Morphism<'A, 'S, 'T>): Map<Presheaf<'A, 'T>, Presheaf<'A, 'S>> =
        map [ for S in ob n.Cod do
                  let inclusion = Morphism.inc S n.Cod
                  let pb = Presheaf.pullback n inclusion
                  let proj = (Morphism.proj1 pb).Cod
                  (S, proj) ]

    { Name = name; Object = ob; Arrow = ar }

/// Determines if F is a subpresheaf of G.
let isSubobject (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'S>): bool =
    [ for A in F.Ob |> Map.dom do
        [ for x in Set.exp F.Ob.[A] G.Ob.[A] do
            (A, x) ] ]
    |> List.listProduct
    |> List.exists (fun ls -> // Note: the order of conjunctions impacts performance due to short-circuiting.
        let map = map ls

        (map |> Map.forall (fun _ -> Map.isInjective))
        && Morphism.isMorphism F G map)

/// Determines if F is a strict subpresheaf of G.
let isStrictSubpresheaf (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'S>): bool =
    F.Ar
    |> Map.dom // Note this cannot be `nonidArrows`.
    |> Set.forall (fun a -> Map.isSubmap F.Ar.[a] G.Ar.[a])

/// Gives the subobjects of a presheaf.
let subobjects (cat: Category<'A>) (F: Presheaf<'A, 'S>): Set<Presheaf<'A, 'S>> = F |> (sub cat).Object

/// Gives the subalgebra of a presheaf.
let subalgebra (cat: Category<'A>) (F: Presheaf<'A, 'S>): Subalgebra<'A, 'S> =
    let top =
        let name = Name.sub F.Name Name.top
        { F with Name = name }

    let bot =
        let B = Presheaf.zero cat
        let name = Name.sub F.Name Name.bot
        { B with Name = name }

    let subobjects = subobjects cat F

    let lessEq =
        [ for (G, H) in Set.square subobjects do
            ((G, H), isStrictSubpresheaf G H) ]
        |> Relation.ofList

    { Top = top
      Bot = bot
      Subobjects = subobjects
      LessEq = lessEq }

/// Join of subobjects in a heyting algebra.
let join (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let name = Name.join F.Name G.Name

    let ob =
        map [ for A in Map.dom F.Ob do
                  let X = Set.union F.Ob.[A] G.Ob.[A]
                  (A, X) ]

    let ar =
        map [ for a in Map.dom F.Ar do
                  let x = Map.union F.Ar.[a] G.Ar.[a]
                  (a, x) ]

    { Name = name; Ob = ob; Ar = ar }

/// Join set of subobjects in a heyting algebra.
let joinMany (alg: Subalgebra<'A, 'S>) (Fs: Set<Presheaf<'A, 'S>>): Presheaf<'A, 'S> = Fs |> Set.fold join alg.Bot

/// Meet of subobjects  in a heyting algebra.
let meet (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let name = Name.meet F.Name G.Name

    let ob =
        map [ for A in Map.dom F.Ob do
                  let X = Set.intersect F.Ob.[A] G.Ob.[A]
                  (A, X) ]

    let ar =
        map [ for a in Map.dom F.Ar do
                  let x = Map.intersect F.Ar.[a] G.Ar.[a]
                  (a, x) ]

    { Name = name; Ob = ob; Ar = ar }

/// Meet set of subobjects in a heyting algebra.
let meetMany (alg: Subalgebra<'A, 'S>) (Fs: Set<Presheaf<'A, 'S>>): Presheaf<'A, 'S> = Fs |> Set.fold meet alg.Top

/// Implication in a heyting algebra.
let imply (alg: Subalgebra<'A, 'S>) (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let H =
        alg.Subobjects
        |> Set.filter (fun H -> alg.LessEq.[meet H F, G])
        |> joinMany alg

    let name = Name.imply F.Name G.Name
    H |> Presheaf.rename name

/// Subtraction in a coheyting algebra.
let minus (alg: Subalgebra<'A, 'S>) (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let H =
        alg.Subobjects
        |> Set.filter (fun H -> alg.LessEq.[F, join G H])
        |> meetMany alg

    let name = Name.minus F.Name G.Name
    H |> Presheaf.rename name

/// Negation in a heyting algebra.
let negate (alg: Subalgebra<'A, 'S>) (F: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let H = imply alg F alg.Bot
    let name = Name.negate F.Name
    H |> Presheaf.rename name

/// Supplement in a coheyting algebra.
let supplement (alg: Subalgebra<'A, 'S>) (F: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let H = minus alg alg.Top F
    let name = Name.supplement F.Name
    H |> Presheaf.rename name

/// Coboundary in a heyting algebra.
let coboundary (alg: Subalgebra<'A, 'S>) (F: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let name = Name.coboundary F.Name
    join F (negate alg F) |> Presheaf.rename name

/// Boundary in a coheyting algebra.
let boundary (alg: Subalgebra<'A, 'S>) (F: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let name = Name.boundary F.Name
    meet (supplement alg F) F |> Presheaf.rename name

/// Square in a biheyting algebra.
/// todo
/// Diamond in a biheyting algebra.
/// todo
