/// Functions specific to the `Presheaf` type.
[<RequireQualifiedAccess>]
module Presheaf

/// Determines if the arrow-indexed set of maps is functorial.
let isFunctorial (cat: Category<'A>) (ar: Map<Arrow<'A>, Map<'S, 'S>>): bool =
    cat.Compose
    |> Map.forall (fun (g, f) gf -> Map.compose ar.[f] ar.[g] = ar.[gf])

/// Determines if the object-indexed sets and arrow-indexed set of maps are well-defined
let isWellDefined (cat: Category<'A>) (ob: Map<'A, Set<'S>>) (ar: Map<Arrow<'A>, Map<'S, 'S>>): bool =
    cat.NonidArrows
    |> Set.forall (fun a ->
        ob.[a.Cod]
        |> Set.forall (fun s -> Set.contains ar.[a].[s] ob.[a.Dom]))

/// Determines if the object-indexed sets and arrow-indexed set of maps determines a presheaf.
let isPresheaf (cat: Category<'A>) (ob: Map<'A, Set<'S>>) (ar: Map<Arrow<'A>, Map<'S, 'S>>): bool =
    isWellDefined cat ob ar && isFunctorial cat ar

/// Helper to create a presheaf from supplied category, object map and nontrivial arrow map.
let make (nameString: string)
         (cat: Category<'A>)
         (ob: Map<'A, Set<'S>>)
         (nonidAr: Map<Arrow<'A>, Map<'S, 'S>>)
         : Presheaf<'A, 'S> =

    let name = Name.ofString nameString

    let ar =
        let idArrow =
            Map [ for A in cat.Objects do
                      let x = Map.id ob.[A]
                      (cat.Id.[A], x) ]

        Map.union idArrow nonidAr

    if not (isPresheaf cat ob ar) then failwith Error.makePresheaf

    { Name = name
      Ob = ob
      Ar = ar
      Cat = cat }

/// Initial presheaf.
let zero (cat: Category<'A>): Presheaf<'A, 'S> =
    let ob =
        Map [ for A in cat.Objects do
                  (A, Set.empty) ]

    let ar =
        Map [ for a in cat.Arrows do
                  (a, Map.empty) ]

    { Name = Name.ofInt 0
      Ob = ob
      Ar = ar
      Cat = cat }

/// Terminal presheaf.
let one (cat: Category<'A>): Presheaf<'A, unit> = Morphism.presheafOne cat

/// Binary product of presheaves.
let product (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'T>): Presheaf<'A, 'S * 'T> = Morphism.presheafProduct F G

/// Binary sum of presheaves.
let sum (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'T>): Presheaf<'A, Choice<'S, 'T>> = Morphism.presheafSum F G

/// Equaliser of presheaves, i.e. limit of the diagram
/// F --f--> G
///   --g->
let equaliser (f: Morphism<'A, 'S, 'T>) (g: Morphism<'A, 'S, 'T>): Presheaf<'A, 'S> =
    if f.Dom <> g.Dom then failwith Error.domainMismatch
    else if f.Cod <> g.Cod then failwith Error.codomainMismatch

    let name = Name.equaliser f.Name g.Name

    let ob =
        Map [ for A in f.Cat.Objects do
                  let X = Map.equaliser f.Map.[A] g.Map.[A]

                  (A, X) ]

    let ar =
        Map [ for a in f.Cat.Arrows do
                  let x = Map.restrict ob.[a.Cod] f.Dom.Ar.[a]
                  (a, x) ]

    { Name = name
      Ob = ob
      Ar = ar
      Cat = f.Cat }

/// Pullback of presheaves, i.e. limit of the diagram
/// F --f--> H <--g-- G
let pullback (f: Morphism<'A, 'S, 'U>) (g: Morphism<'A, 'T, 'U>): Presheaf<'A, 'S * 'T> =
    if f.Cod <> g.Cod then failwith Error.codomainMismatch

    let name =
        Name.pullback f.Dom.Name f.Cod.Name g.Dom.Name

    let ob =
        Map [ for A in f.Cat.Objects do
                  let X = Map.pullback f.Map.[A] g.Map.[A]
                  (A, X) ]

    let ar =
        let FG = product f.Dom g.Dom

        Map [ for a in f.Cat.Arrows do
                  let x = Map.restrict ob.[a.Cod] FG.Ar.[a]
                  (a, x) ]

    { Name = name
      Ob = ob
      Ar = ar
      Cat = f.Cat }

/// Coequaliser of presheaves, i.e. colimit of the diagram
/// F --f--> G
///   --g-->
let coequaliser (f: Morphism<'A, 'S, 'T>) (g: Morphism<'A, 'S, 'T>): Presheaf<'A, Set<'T>> =
    if f.Dom <> g.Dom then failwith Error.domainMismatch
    else if f.Cod <> g.Cod then failwith Error.codomainMismatch

    let name = Name.coequaliser f.Name g.Name

    let ob =
        Map [ for A in f.Cat.Objects do
                  let X =
                      Map.coequaliser f.Map.[A] g.Map.[A] f.Cod.Ob.[A]

                  (A, X) ]

    let ar =
        Map [ for a in f.Cat.Arrows do
                  let x =
                      Map [ for R in ob.[a.Cod] do
                                let rep = R |> Seq.item 0 // R is inhabited.
                                let imageRep = f.Cod.Ar.[a].[rep]

                                let imageClass =
                                    Seq.find (fun X -> Set.contains imageRep X) ob.[a.Dom]

                                (R, imageClass) ]

                  (a, x) ]

    { Name = name
      Ob = ob
      Ar = ar
      Cat = f.Cat }

/// Pushout of presheaves, i.e. colimit of the diagram
/// F <--f-- H --g--> G
let pushout (f: Morphism<'A, 'U, 'S>) (g: Morphism<'A, 'U, 'T>): Presheaf<'A, Set<Choice<'S, 'T>>> =
    if f.Dom <> g.Dom then failwith Error.domainMismatch

    let name =
        Name.pushout f.Cod.Name f.Dom.Name g.Cod.Name

    let ob =
        Map [ for A in f.Cat.Objects do
                  let X =
                      Map.pushout f.Cod.Ob.[A] f.Map.[A] g.Map.[A] g.Cod.Ob.[A]

                  (A, X) ]

    let ar =
        Map [ for a in f.Cat.Arrows do
                  let x =
                      Map [ for R in ob.[a.Cod] do
                                let rep = R |> Seq.item 0 // R is inhabited.

                                let imageRep =
                                    rep
                                    |> (function
                                    | Choice1Of2 s -> Choice1Of2 f.Cod.Ar.[a].[s]
                                    | Choice2Of2 t -> Choice2Of2 g.Cod.Ar.[a].[t])

                                let imageClass =
                                    Seq.find (fun X -> Set.contains imageRep X) ob.[a.Dom]

                                (R, imageClass) ]

                  (a, x) ]

    { Name = name
      Ob = ob
      Ar = ar
      Cat = f.Cat }

/// Exponential of presheaves G^F.
let exp (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'T>): Presheaf<'A, Morphism<'A, Arrow<'A> * 'S, 'T>> =
    let name = Name.exp F.Name G.Name
    let yo = Yoneda.yo F.Cat

    let ob =
        Map [ for A in F.Cat.Objects do
                  let X = Morphism.hom (product (yo.Ob.[A]) F) G
                  (A, X) ]

    let ar =
        Map [ for a in F.Cat.Arrows do
                  let x =
                      Map [ for f in ob.[a.Cod] do
                                let g =
                                    Morphism.compose f (Morphism.product (yo.Ar.[a]) (Morphism.id F))

                                (f, g) ]

                  (a, x) ]

    { Name = name
      Ob = ob
      Ar = ar
      Cat = F.Cat }

/// Renames the input presheaf with a name of an identical element in the simplification set.
let identify (targetSet: Set<Presheaf<'A, 'S>>) (input: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    input
    |> fun F -> (F, Seq.tryFind ((=) F) targetSet)
    |> fun (F, optionG) ->
        match optionG with
        | Some G -> G
        | None -> F

/// Renames a presheaf.
let rename (name: Name) (F: Presheaf<'A, 'S>): Presheaf<'A, 'S> = { F with Name = name }

/// Given a presheaf of type `F` returns an isomorphic presheaf whose figures are of type `int` numbered 0..[size - 1].
let simplify (F: Presheaf<'A, 'S>): Presheaf<'A, int> =
    let figureToInt X s = List.findIndex ((=) s) (Set.toList X)

    let ob =
        Map [ for A in F.Cat.Objects do
                  let X =
                      F.Ob.[A] |> Set.map (figureToInt F.Ob.[A])

                  (A, X) ]

    let ar =
        Map [ for a in F.Cat.Arrows do
                  let x =
                      F.Ar.[a]
                      |> Seq.map (fun (KeyValue (k, v)) -> (figureToInt F.Ob.[a.Cod] k, figureToInt F.Ob.[a.Dom] v))
                      |> Map

                  (a, x) ]

    { Name = F.Name
      Ob = ob
      Ar = ar
      Cat = F.Cat }

/// Determines if two presheaves are isomorphic.
let isIso (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'T>): bool =
    let F, G = simplify F, simplify G // Simplifying improves performance.

    [ for A in F.Cat.Objects do
        [ for x in Map.iso F.Ob.[A] G.Ob.[A] do
            (A, x) ] ]
    |> List.listProduct
    |> Seq.exists (Map >> Morphism.isNatural F G)

/// Precompose a presheaf with a functor.
let compose (F: Presheaf<'B, 'S>) (P: SmallFunctor<'A, 'B>): Presheaf<'A, 'S> =
    let name = Name.compose F.Name P.Name
    let cat = P.Dom

    let ob =
        Map [ for A in cat.Objects do
                  (A, F.Ob.[P.Ob.[A]]) ]

    let ar =
        Map [ for a in cat.Arrows do
                  (a, F.Ar.[P.Ar.[a]]) ]

    { Name = name
      Ob = ob
      Ar = ar
      Cat = cat }

/// External product of presheaves.
let externalProduct (F: Presheaf<'A, 'S>) (G: Presheaf<'B, 'T>): Presheaf<'A * 'B, 'S * 'T> =
    let cat = Category.product F.Cat G.Cat

    let name = Name.product F.Name G.Name

    let ob =
        Map [ for (A, B) in cat.Objects do
                  let X = Set.product F.Ob.[A] G.Ob.[B]
                  ((A, B), X) ]

    let ar =
        Map [ for ab in cat.Arrows do
                  let x =
                      Map.product F.Ar.[Arrow.proj1 ab] G.Ar.[Arrow.proj2 ab]

                  (ab, x) ]

    { Name = name
      Ob = ob
      Ar = ar
      Cat = cat }
