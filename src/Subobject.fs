/// Functions to compute algebras of subobjects and perform operations on them.
[<RequireQualifiedAccess>]
module Subobject

/// Subobject functor.
// Todo: resolve genericity problems with this definition.
let sub (_cat: Category<'A>)
        : {| Ar: Morphism<'A, 'a, 'b> -> Map<Presheaf<'A, 'b>, Presheaf<'A, 'a>>
             Name: Name
             Ob: Presheaf<'A, 'c> -> Set<Presheaf<'A, 'c>> |} =
    let name = Name.subobject

    // Gives a descriptive name for a subpresheaf with the specified objects and arrow maps.
    let nameSubpresheaf (i: int) (F: Presheaf<'A, 'S>) (ob: Map<'A, Set<'S>>) (ar: Map<Arrow<'A>, Map<'S, 'S>>): Name =
        if F.Ob = ob && F.Ar = ar then Name.sub F.Name Name.top
        else if Map.exists (fun _ X -> X <> Set.empty) ob then Name.sub F.Name (Name.ofInt i)
        else Name.sub F.Name Name.bot

    let ob (F: Presheaf<'A, 'S>): Set<Presheaf<'A, 'S>> =
        let subobjects =
            [ for A in F.Cat.Objects do
                [ for X in Set.powerset F.Ob.[A] do
                    (A, X) ] ]
            |> List.listProduct
            |> Seq.map (fun ls ->
                let ob = Map ls

                ob,
                Map [ for a in F.Cat.Arrows do
                          (a, Map.restrict ob.[a.Cod] F.Ar.[a]) ])
            |> Seq.filter (fun (ob, ar) -> Presheaf.isWellDefined F.Cat ob ar)
            |> Seq.mapi (fun i (ob, ar) ->
                let name = nameSubpresheaf i F ob ar

                let presheaf =
                    { Name = name
                      Ob = ob
                      Ar = ar
                      Cat = F.Cat }

                presheaf)
            |> set

        subobjects

    let ar (f: Morphism<'A, 'S, 'T>): Map<Presheaf<'A, 'T>, Presheaf<'A, 'S>> =
        Map [ for S in ob f.Cod do
                  let inclusion = Morphism.inc S f.Cod
                  let pb = Presheaf.pullback f inclusion
                  let proj = (pb |> Morphism.proj1).Cod
                  (S, proj) ]

    {| Name = name; Ob = ob; Ar = ar |}

/// Determines if F is a subpresheaf of G.
let isSubobject (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'S>): bool =
    Morphism.hom F G |> Set.exists Morphism.isMono

/// Determines if U is a strict subobject of V.
let lessEq (U: Presheaf<'A, 'S>) (V: Presheaf<'A, 'S>): bool =
    U.Cat.Arrows // Note this cannot be `nonidArrows`.
    |> Set.forall (fun a -> Map.isSubmap U.Ar.[a] V.Ar.[a])

/// Gives the subobjects of a presheaf.
let subobjects (F: Presheaf<'A, 'S>): Set<Presheaf<'A, 'S>> = F |> (sub F.Cat).Ob

/// Gives the algebra of a presheaf.
let algebra (F: Presheaf<'A, 'S>): Algebra<'A, 'S> =
    let top =
        let name = Name.sub F.Name Name.top
        { F with Name = name }

    let bot =
        let B = Presheaf.zero F.Cat
        let name = Name.sub F.Name Name.bot
        { B with Name = name }

    let subobjects = subobjects F

    let lessEq =
        [ for G in subobjects do
            for H in subobjects do
                ((G, H), lessEq G H) ]
        |> Relation.ofList

    { Top = top
      Bot = bot
      Subobjects = subobjects
      LessEq = lessEq }

/// Join of subobjects in a Heyting algebra of subobjects.
let join (U: Presheaf<'A, 'S>) (V: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let name = Name.join U.Name V.Name

    let ob =
        Map [ for A in U.Cat.Objects do
                  let X = Set.union U.Ob.[A] V.Ob.[A]

                  (A, X) ]

    let ar =
        Map [ for a in U.Cat.Arrows do
                  let x = Map.union U.Ar.[a] V.Ar.[a]

                  (a, x) ]

    { Name = name
      Ob = ob
      Ar = ar
      Cat = U.Cat }

/// Join set of subobjects in a Heyting algebra of subobjects.
let joinMany (alg: Algebra<'A, 'S>) (Us: Set<Presheaf<'A, 'S>>): Presheaf<'A, 'S> = Us |> Set.fold join alg.Bot

/// Meet of subobjects in a Heyting algebra of subobjects.
let meet (U: Presheaf<'A, 'S>) (V: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let name = Name.meet U.Name V.Name

    let ob =
        Map [ for A in U.Cat.Objects do
                  let X = Set.intersect U.Ob.[A] V.Ob.[A]

                  (A, X) ]

    let ar =
        Map [ for a in U.Cat.Arrows do
                  let x = Map.intersect U.Ar.[a] V.Ar.[a]

                  (a, x) ]

    { Name = name
      Ob = ob
      Ar = ar
      Cat = U.Cat }

/// Meet set of subobjects in a Heyting algebra of subobjects.
let meetMany (alg: Algebra<'A, 'S>) (Us: Set<Presheaf<'A, 'S>>): Presheaf<'A, 'S> = Us |> Set.fold meet alg.Top

/// Implication in a Heyting algebra of subobjects.
let imply (alg: Algebra<'A, 'S>) (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let H =
        alg.Subobjects
        |> Set.filter (fun H -> alg.LessEq.[meet H F, G])
        |> joinMany alg

    let name = Name.imply F.Name G.Name
    H |> Presheaf.rename name

/// Subtraction in a coHeyting algebra of subobjects.
let minus (alg: Algebra<'A, 'S>) (U: Presheaf<'A, 'S>) (V: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let H =
        alg.Subobjects
        |> Set.filter (fun H -> alg.LessEq.[U, join V H])
        |> meetMany alg

    let name = Name.minus U.Name V.Name
    H |> Presheaf.rename name

/// Negation in a Heyting algebra of subobjects.
let negate (alg: Algebra<'A, 'S>) (U: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let H = imply alg U alg.Bot
    let name = Name.negate U.Name
    H |> Presheaf.rename name

/// Supplement in a coHeyting algebra of subobjects.
let supplement (alg: Algebra<'A, 'S>) (U: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let H = minus alg alg.Top U
    let name = Name.supplement U.Name
    H |> Presheaf.rename name

/// Coboundary in a Heyting algebra of subobjects.
let coboundary (alg: Algebra<'A, 'S>) (U: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let name = Name.coboundary U.Name
    join U (negate alg U) |> Presheaf.rename name

/// Boundary in a coHeyting algebra of subobjects.
let boundary (alg: Algebra<'A, 'S>) (U: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let name = Name.boundary U.Name
    meet (supplement alg U) U |> Presheaf.rename name

/// Preimage.
let preimage (f: Morphism<'A, 'S, 'T>): Map<Presheaf<'A, 'T>, Presheaf<'A, 'S>> =
    let cod = algebra f.Cod

    Map [ for T in cod.Subobjects do
              let pre_f =
                  let inc = Morphism.inc T cod.Top
                  let pb = Presheaf.pullback f inc
                  let proj = (pb |> Morphism.proj1).Cod

                  proj
                  |> Presheaf.rename (Name.preimage f.Name T.Name)

              (T, pre_f) ]

/// Existential quantification.
let exists (f: Morphism<'A, 'S, 'T>): Map<Presheaf<'A, 'S>, Presheaf<'A, 'T>> =
    let dom = subobjects f.Dom

    Map [ for S in dom do
              let ex_f =
                  Morphism.apply f S
                  |> Presheaf.rename (Name.exists f.Name S.Name)

              (S, ex_f) ]

/// Universal quantification.
let forall (f: Morphism<'A, 'S, 'T>): Map<Presheaf<'A, 'S>, Presheaf<'A, 'T>> =
    let dom = subobjects f.Dom

    Map [ for S in dom do
              let fa_f =
                  let name = Name.forall f.Name S.Name

                  let ob =
                      let filter A t =
                          f.Cat.Objects
                          |> Set.forall (fun B ->
                              f.Cat.Hom.[B, A]
                              |> Set.forall (fun a ->
                                  f.Dom.Ob.[B]
                                  |> Set.forall (fun s ->
                                      f.Map.[B].[s] = f.Cod.Ar.[a].[t]
                                      => Set.contains s S.Ob.[B])))

                      Map [ for A in f.Cat.Objects do
                                let X = f.Cod.Ob.[A] |> Set.filter (filter A)
                                (A, X) ]

                  let ar =
                      Map [ for a in f.Cat.Arrows do
                                let x = Map.restrict ob.[a.Cod] f.Cod.Ar.[a]
                                (a, x) ]

                  { Name = name
                    Ob = ob
                    Ar = ar
                    Cat = f.Cat }

              (S, fa_f) ]

/// Necessity (square): the largest complemented subobject contained in `U`. (p33, Reyes & Zolfaghari, Bi-Heyting algebras, toposes and modalities.)
let necessity (alg: Algebra<'A, 'S>) (U: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let name = Name.necessity U.Name
    let iterate (V: Presheaf<'A, 'S>): Presheaf<'A, 'S> = V |> supplement alg |> negate alg

    let rec recurse (V: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
        if V = iterate V then V else V |> iterate |> recurse

    recurse U |> Presheaf.rename name

/// Possibility (diamond): the largest complemented subobject containing `U`. (p33, Reyes & Zolfaghari, Bi-Heyting algebras, toposes and modalities.)
let possibility (alg: Algebra<'A, 'S>) (U: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let name = Name.possibility U.Name
    let iterate (V: Presheaf<'A, 'S>): Presheaf<'A, 'S> = V |> negate alg |> supplement alg

    let rec recurse (V: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
        if V = iterate V then V else V |> iterate |> recurse

    recurse U |> Presheaf.rename name
