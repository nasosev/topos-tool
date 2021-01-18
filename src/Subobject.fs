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

    let ar (f: Morphism<'A, 'S, 'T>): Map<Presheaf<'A, 'T>, Presheaf<'A, 'S>> =
        map [ for S in ob f.Cod do
                  let inclusion = Morphism.inc S f.Cod
                  let pb = Presheaf.pullback f inclusion
                  let proj = (Morphism.proj1 pb).Cod
                  (S, proj) ]

    { Name = name; Object = ob; Arrow = ar }

/// Determines if F is a subpresheaf of G.
let isSubobject (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'S>): bool =
    Morphism.hom F G |> Set.exists Morphism.isMono

/// Determines if F is a strict subpresheaf of G.
let isStrictSubobject (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'S>): bool =
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
            ((G, H), isStrictSubobject G H) ]
        |> Relation.ofList

    { Top = top
      Bot = bot
      Subobjects = subobjects
      LessEq = lessEq }

/// Join of subobjects in a heyting algebra of subobjects.
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

/// Join set of subobjects in a heyting algebra of subobjects.
let joinMany (alg: Subalgebra<'A, 'S>) (Fs: Set<Presheaf<'A, 'S>>): Presheaf<'A, 'S> = Fs |> Set.fold join alg.Bot

/// Meet of subobjects  in a heyting algebra of subobjects.
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

/// Meet set of subobjects in a heyting algebra of subobjects.
let meetMany (alg: Subalgebra<'A, 'S>) (Fs: Set<Presheaf<'A, 'S>>): Presheaf<'A, 'S> = Fs |> Set.fold meet alg.Top

/// Implication in a heyting algebra of subobjects.
let imply (alg: Subalgebra<'A, 'S>) (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let H =
        alg.Subobjects
        |> Set.filter (fun H -> alg.LessEq.[meet H F, G])
        |> joinMany alg

    let name = Name.imply F.Name G.Name
    H |> Presheaf.rename name

/// Subtraction in a coheyting algebra of subobjects.
let minus (alg: Subalgebra<'A, 'S>) (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let H =
        alg.Subobjects
        |> Set.filter (fun H -> alg.LessEq.[F, join G H])
        |> meetMany alg

    let name = Name.minus F.Name G.Name
    H |> Presheaf.rename name

/// Negation in a heyting algebra of subobjects.
let negate (alg: Subalgebra<'A, 'S>) (F: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let H = imply alg F alg.Bot
    let name = Name.negate F.Name
    H |> Presheaf.rename name

/// Supplement in a coheyting algebra of subobjects.
let supplement (alg: Subalgebra<'A, 'S>) (F: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let H = minus alg alg.Top F
    let name = Name.supplement F.Name
    H |> Presheaf.rename name

/// Coboundary in a heyting algebra of subobjects.
let coboundary (alg: Subalgebra<'A, 'S>) (F: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let name = Name.coboundary F.Name
    join F (negate alg F) |> Presheaf.rename name

/// Boundary in a coheyting algebra of subobjects.
let boundary (alg: Subalgebra<'A, 'S>) (F: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let name = Name.boundary F.Name
    meet (supplement alg F) F |> Presheaf.rename name

/// Preimage.
let preimage (cat: Category<'A>) (f: Morphism<'A, 'S, 'T>): Map<Presheaf<'A, 'T>, Presheaf<'A, 'S>> =
    let cod = subalgebra cat f.Cod

    map [ for T in cod.Subobjects do
              let pre_f =
                  let inc = Morphism.inc T cod.Top

                  (Presheaf.pullback inc f |> Morphism.proj2).Cod
                  |> Presheaf.rename (Name.preimage f.Name T.Name)

              (T, pre_f) ]

/// Existential quantification.
let exists (cat: Category<'A>) (f: Morphism<'A, 'S, 'T>): Map<Presheaf<'A, 'S>, Presheaf<'A, 'T>> =
    let dom = subobjects cat f.Dom

    map [ for S in dom do
              let ex_f =
                  Morphism.apply f S
                  |> Presheaf.rename (Name.exists f.Name S.Name)

              (S, ex_f) ]

/// Universal quantification.
let forall (cat: Category<'A>) (f: Morphism<'A, 'S, 'T>): Map<Presheaf<'A, 'S>, Presheaf<'A, 'T>> =
    let dom = subobjects cat f.Dom

    map [ for S in dom do
              let fa_f =
                  let name = Name.forall f.Name S.Name

                  let ob =
                      let filter A t =
                          cat.Objects
                          |> Set.forall (fun B ->
                              cat.Hom.[B, A]
                              |> Set.forall (fun a ->
                                  f.Dom.Ob.[B]
                                  |> Set.forall (fun s ->
                                      f.Mapping.[B].[s] = f.Cod.Ar.[a].[t]
                                      => Set.contains s S.Ob.[B])))

                      map [ for A in cat.Objects do
                                let X = f.Cod.Ob.[A] |> Set.filter (filter A)
                                (A, X) ]

                  let ar =
                      map [ for a in cat.Arrows do
                                let x = Map.restrict f.Cod.Ar.[a] ob.[a.Cod]
                                (a, x) ]

                  { Name = name; Ob = ob; Ar = ar }

              (S, fa_f) ]

/// Square, Diamond in a biheyting algebra of subobjects. (see Reyes: Bi-heyting algebras, toposes and modalities)
/// todo
