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

    { Name = name
      Ob = ob
      Ar = ar
      Category = cat }

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
      Ar = ar
      Category = cat }

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
      Ar = ar
      Category = cat }

/// Binary product of presheaves.
let product (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'T>): Presheaf<'A, 'S * 'T> = Morphism.presheafProduct F G

/// Binary sum of presheaves.
let sum (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'T>): Presheaf<'A, Choice<'S, 'T>> = Morphism.presheafSum F G

/// Equaliser of presheaves, i.e. limit of the diagram
/// F --n--> G
///   --m-->
/// WARNING: does not check that domains and codomains of f and g match.
let equaliser (f: Morphism<'A, 'S, 'T>) (g: Morphism<'A, 'S, 'T>): Presheaf<'A, 'S> =
    let name = Name.equaliser f.Name g.Name

    let ob =
        map [ for A in Map.dom f.Dom.Ob do
                  let X =
                      Map.equaliser f.Mapping.[A] g.Mapping.[A]

                  (A, X) ]

    let ar =
        map [ for a in Map.dom f.Dom.Ar do
                  let x = Map.restrict f.Dom.Ar.[a] ob.[a.Cod]
                  (a, x) ]

    { Name = name
      Ob = ob
      Ar = ar
      Category = f.Category }

/// Pullback of presheaves, i.e. limit of the diagram
/// F --n--> H <--m-- G
/// WARNING: does not check that codomains of f and g match.
let pullback (f: Morphism<'A, 'S, 'U>) (g: Morphism<'A, 'T, 'U>): Presheaf<'A, 'S * 'T> =
    let name =
        Name.pullback f.Dom.Name f.Cod.Name g.Dom.Name

    let ob =
        map [ for A in Map.dom f.Cod.Ob do
                  let X = Map.pullback f.Mapping.[A] g.Mapping.[A]
                  (A, X) ]

    let ar =
        let FG = product f.Dom g.Dom

        map [ for a in Map.dom f.Cod.Ar do
                  let x = Map.restrict FG.Ar.[a] ob.[a.Cod]
                  (a, x) ]

    { Name = name
      Ob = ob
      Ar = ar
      Category = f.Category }

/// Coequaliser of presheaves, i.e. colimit of the diagram
/// F --n--> G
///   --m-->
/// WARNING: does not check that domains and codomains of f and g match.
let coequaliser (f: Morphism<'A, 'S, 'T>) (g: Morphism<'A, 'S, 'T>): Presheaf<'A, Set<'T>> =
    let name = Name.coequaliser f.Name g.Name

    let ob =
        map [ for A in Map.dom f.Dom.Ob do
                  let X =
                      Map.coequaliser f.Mapping.[A] g.Mapping.[A] f.Cod.Ob.[A]

                  (A, X) ]

    let ar =
        map [ for a in Map.dom f.Dom.Ar do
                  let x =
                      map [ for R in ob.[a.Cod] do
                                let rep = R |> Seq.item 0 // R is inhabited.
                                let imageRep = f.Cod.Ar.[a].[rep]

                                let imageClass =
                                    Seq.find (fun X -> Set.contains imageRep X) ob.[a.Dom]

                                (R, imageClass) ]

                  (a, x) ]

    { Name = name
      Ob = ob
      Ar = ar
      Category = f.Category }

/// Pushout of presheaves, i.e. colimit of the diagram
/// F <--n-- H --m--> G
/// WARNING: does not check that domains of f and g match.
let pushout (f: Morphism<'A, 'U, 'S>) (g: Morphism<'A, 'U, 'T>): Presheaf<'A, Set<Choice<'S, 'T>>> =
    let name =
        Name.pushout f.Cod.Name f.Dom.Name g.Cod.Name

    let ob =
        map [ for A in Map.dom f.Dom.Ob do
                  let X =
                      Map.pushout f.Cod.Ob.[A] f.Mapping.[A] g.Mapping.[A] g.Cod.Ob.[A]

                  (A, X) ]

    let ar =
        map [ for a in Map.dom f.Dom.Ar do
                  let x =
                      map [ for R in ob.[a.Cod] do
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
      Category = f.Category }

/// Exponential of presheaves G^F.
let exp (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'T>): Presheaf<'A, Morphism<'A, Arrow<'A> * 'S, 'T>> =
    let name = Name.exp F.Name G.Name
    let yo = Yoneda.yo F.Category

    let ob =
        map [ for A in Map.dom F.Ob do
                  let X = Morphism.hom (product (yo.Object A) F) G
                  (A, X) ]

    let ar =
        map [ for a in Map.dom F.Ar do
                  let x =
                      map [ for f in Morphism.hom (product (yo.Object a.Cod) F) G do
                                let g =
                                    Morphism.compose f (Morphism.product (yo.Arrow a) (Morphism.id F))

                                (f, g) ]

                  (a, x) ]

    { Name = name
      Ob = ob
      Ar = ar
      Category = F.Category }

/// Determines if two presheaves are isomorphic.
let isIso (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'T>): bool =
    [ for A in Map.dom F.Ob do
        [ for x in Map.iso F.Ob.[A] G.Ob.[A] do
            (A, x) ] ]
    |> List.listProduct
    |> List.exists (map >> Morphism.isMorphism F G)

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
