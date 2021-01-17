/// Functions specific to the 'Presheaf' type.
[<RequireQualifiedAccess>]
module Presheaf

/// Determines if the object-indexed sets and arrow-indexed set of maps determines a presheaf.
let isPresheaf (cat: Category<'A>) (ob: Map<'A, Set<'S>>) (ar: Map<Arrow<'A>, Map<'S, 'S>>): bool =
    cat.NonidArrows
    |> Set.forall (fun a ->
        ob.[a.Cod]
        |> Set.forall (fun x -> Set.contains ar.[a].[x] ob.[a.Dom]))

/// Helper to create a presheaf from supplied category, object map and nontrivial arrow map.
let make (nameString: string)
         (cat: Category<'A>)
         (ob: Map<'A, Set<'S>>)
         (nonidArrows: Map<Arrow<'A>, Map<'S, 'S>>)
         : Presheaf<'A, 'S> =
    if not (isPresheaf cat ob nonidArrows) then failwith "That is not a presheaf."
    let name = Name.ofString nameString

    let ar =
        let idArrow =
            map [ for A in cat.Objects do
                      let x = Map.id ob.[A]
                      (cat.Id.[A], x) ]

        Map.union idArrow nonidArrows

    { Name = name; Ob = ob; Ar = ar }

/// Initial presheaf.
let zero (cat: Category<'A>): Presheaf<'A, 'S> =
    let ob =
        map [ for A in cat.Objects do
                  (A, Set.empty) ]

    let ar =
        map [ for a in cat.Arrows do
                  (a, Map.empty) ]

    { Name = Name.ofString "0"
      Ob = ob
      Ar = ar }

/// Terminal presheaf.
let one (cat: Category<'A>): Presheaf<'A, unit> =
    let ob =
        map [ for A in cat.Objects do
                  (A, set [ () ]) ]

    let ar =
        map [ for a in cat.Arrows do
                  (a, map [ (), () ]) ]

    { Name = Name.ofString "1"
      Ob = ob
      Ar = ar }

/// Binary product of presheaves.
let product (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'T>): Presheaf<'A, 'S * 'T> = Morphism.presheafProduct F G

/// Binary sum of presheaves.
let sum (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'T>): Presheaf<'A, Choice<'S, 'T>> = Morphism.presheafSum F G

/// Equaliser of presheaves, i.e. limit of the diagram
/// F --n--> G
///   --m-->
/// WARNING: does not check that domains and codomains of n and m match.
let equaliser (n: Morphism<'A, 'S, 'T>) (m: Morphism<'A, 'S, 'T>): Presheaf<'A, 'S> =
    let name = Name.equaliser n.Name m.Name

    let ob =
        map [ for A in Map.dom n.Dom.Ob do
                  let X =
                      Map.equaliser n.Mapping.[A] m.Mapping.[A]

                  (A, X) ]

    let ar =
        map [ for a in Map.dom n.Dom.Ar do
                  let x = Map.restrict n.Dom.Ar.[a] ob.[a.Cod]
                  (a, x) ]

    { Name = name; Ob = ob; Ar = ar }

/// Pullback of presheaves, i.e. limit of the diagram
/// F --n--> H <--m-- G
/// WARNING: does not check that codomains of n and m match.
let pullback (n: Morphism<'A, 'S, 'U>) (m: Morphism<'A, 'T, 'U>): Presheaf<'A, 'S * 'T> =
    let name =
        Name.pullback n.Dom.Name n.Cod.Name m.Dom.Name

    let ob =
        map [ for A in Map.dom n.Cod.Ob do
                  let X = Map.pullback n.Mapping.[A] m.Mapping.[A]
                  (A, X) ]

    let ar =
        let FG = product n.Dom m.Dom

        map [ for a in Map.dom n.Cod.Ar do
                  let x = Map.restrict FG.Ar.[a] ob.[a.Cod]
                  (a, x) ]

    { Name = name; Ob = ob; Ar = ar }

/// Coequaliser of presheaves, i.e. colimit of the diagram
/// F --n--> G
///   --m-->
/// WARNING: does not check that domains and codomains of n and m match.
let coequaliser (n: Morphism<'A, 'S, 'T>) (m: Morphism<'A, 'S, 'T>): Presheaf<'A, Set<'T>> =
    let name = Name.coequaliser n.Name m.Name

    let ob =
        map [ for A in Map.dom n.Dom.Ob do
                  let X =
                      Map.coequaliser n.Mapping.[A] m.Mapping.[A] n.Cod.Ob.[A]

                  (A, X) ]

    let ar =
        map [ for a in Map.dom n.Dom.Ar do
                  let x =
                      map [ for R in ob.[a.Cod] do
                                let rep = R |> Seq.item 0
                                let imageRep = n.Cod.Ar.[a].[rep]

                                let imageClass =
                                    Seq.find (fun X -> Set.contains imageRep X) ob.[a.Dom]

                                (R, imageClass) ]

                  (a, x) ]

    { Name = name; Ob = ob; Ar = ar }

/// Pushout of presheaves, i.e. colimit of the diagram
/// F <--n-- H --m--> G
/// WARNING: does not check that domains of n and m match.
let pushout (n: Morphism<'A, 'U, 'S>) (m: Morphism<'A, 'U, 'T>): Presheaf<'A, Set<Choice<'S, 'T>>> =
    let name =
        Name.pushout n.Cod.Name n.Dom.Name m.Cod.Name

    let ob =
        map [ for A in Map.dom n.Dom.Ob do
                  let X =
                      Map.pushout n.Cod.Ob.[A] n.Mapping.[A] m.Mapping.[A] m.Cod.Ob.[A]

                  (A, X) ]

    let ar =
        map [ for a in Map.dom n.Dom.Ar do
                  let x =
                      map [ for R in ob.[a.Cod] do
                                let rep = R |> Seq.item 0

                                let imageRep =
                                    rep
                                    |> (function
                                    | Choice1Of2 s -> Choice1Of2 n.Cod.Ar.[a].[s]
                                    | Choice2Of2 t -> Choice2Of2 m.Cod.Ar.[a].[t])

                                let imageClass =
                                    Seq.find (fun X -> Set.contains imageRep X) ob.[a.Dom]

                                (R, imageClass) ]

                  (a, x) ]

    { Name = name; Ob = ob; Ar = ar }

/// Exponential of presheaves G^F.
let exp (cat: Category<'A>) (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'T>): Presheaf<'A, Morphism<'A, Arrow<'A> * 'S, 'T>> =
    let name = Name.exp F.Name G.Name
    let yo = Yoneda.yo cat

    let ob =
        map [ for A in Map.dom F.Ob do
                  let X = Morphism.hom (product (yo.Object A) F) G
                  (A, X) ]

    let ar =
        map [ for a in Map.dom F.Ar do
                  let x =
                      map [ for n in Morphism.hom (product (yo.Object a.Cod) F) G do
                                let m =
                                    Morphism.compose n (Morphism.product (yo.Arrow a) (Morphism.id F))

                                (n, m) ]

                  (a, x) ]

    { Name = name; Ob = ob; Ar = ar }

/// Determines if two presheaves are isomorphic.
/// Note: doesn't use some constructs from `Morphism` for performance reasons. Can probably be improved more.
let isIso (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'T>): bool =
    [ for A in Map.dom F.Ob do
        [ for x in Set.exp F.Ob.[A] G.Ob.[A] do
            (A, x) ] ]
    |> List.listProduct
    |> List.exists (fun ls -> // Note: the order of conjunctions impacts performance due to short-circuiting.
        let mapping = map ls

        (mapping
         |> Map.forall (fun A x -> Map.isSurjective x G.Ob.[A] && Map.isInjective x))
        && Morphism.isMorphism F G mapping)


/// Renames the input presheaf with a name of an identical element in the simplification set.
let simplify (targetSet: Set<Presheaf<'A, 'S>>) (input: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    input
    |> fun F -> (F, Seq.tryFind ((=) F) targetSet)
    |> fun (F, optionG) ->
        match optionG with
        | Some G -> G
        | None -> F

/// Renames a presheaf.
let rename (name: Name) (F: Presheaf<'A, 'S>): Presheaf<'A, 'S> = { F with Name = name }
