/// Functions specific to the 'Morphism' type.
[<RequireQualifiedAccess>]
module Morphism

/// Determines if the map of presheaves is a morphism.
let isMorphism (dom: Presheaf<'A, 'S>) (cod: Presheaf<'A, 'T>) (mapping: Map<'A, Map<'S, 'T>>): bool =
    Map.dom mapping = dom.Category.Objects // Check the mapping is defined on all objects.
    && dom.Category.NonidArrows
       |> Set.forall (fun a ->
           dom.Ob.[a.Cod]
           |> Set.forall (fun x -> mapping.[a.Dom].[dom.Ar.[a].[x]] = cod.Ar.[a].[mapping.[a.Cod].[x]]))

/// Helper function to make a morphism.
let make (nameString: string)
         (dom: Presheaf<'A, 'S>)
         (cod: Presheaf<'A, 'T>)
         (mapping: Map<'A, Map<'S, 'T>>)
         : Morphism<'A, 'S, 'T> =
    if not (isMorphism dom cod mapping)
       || not (dom.Category = cod.Category) then
        failwith "That is not a morphism."

    let name = Name.ofString nameString

    { Name = name
      Mapping = mapping
      Dom = dom
      Cod = cod
      Category = dom.Category }

/// Determines if the morphism is mono.
let isMono (f: Morphism<'A, 'S, 'T>): bool =
    f.Mapping |> Map.forall (fun _ -> Map.isInjective)

/// Determines if the morphism is epi.
let isEpi (f: Morphism<'A, 'S, 'T>): bool =
    f.Mapping
    |> Map.forall (fun A x -> Map.isSurjective f.Cod.Ob.[A] x)

/// Determines if the morphism is an isomorphism.
// Note: the order of conjunctions impacts performance due to short-circuiting.
let isIso (f: Morphism<'A, 'S, 'T>): bool = isEpi f && isMono f

/// External hom of presheaves.
let hom (dom: Presheaf<'A, 'S>) (cod: Presheaf<'A, 'T>): Set<Morphism<'A, 'S, 'T>> =
    [ for A in dom.Category.Objects do
        [ for x in Map.exp dom.Ob.[A] cod.Ob.[A] do
            (A, x) ] ]
    |> List.listProduct
    |> List.filter (Map >> isMorphism dom cod)
    |> List.mapi (fun i ls ->
        let name =
            Name.sub (Name.hom dom.Name cod.Name) (Name.ofString $"{i}")

        let mapping = Map ls

        { Name = name
          Mapping = mapping
          Dom = dom
          Cod = cod
          Category = dom.Category })
    |> set

/// Gives the set of isomorphisms between two presheaves.
let iso (dom: Presheaf<'A, 'S>) (cod: Presheaf<'A, 'T>): Set<Morphism<'A, 'S, 'T>> =
    [ for A in dom.Category.Objects do
        [ for x in Map.iso dom.Ob.[A] cod.Ob.[A] do
            (A, x) ] ]
    |> List.listProduct
    |> List.filter (Map >> isMorphism dom cod)
    |> List.mapi (fun i ls ->
        let name =
            Name.sub (Name.hom dom.Name cod.Name) (Name.ofString $"{i}")

        let mapping = Map ls

        { Name = name
          Mapping = mapping
          Dom = dom
          Cod = cod
          Category = dom.Category })
    |> set

/// Applies a morphism to a presheaf.
let apply (f: Morphism<'A, 'S, 'T>) (dom: Presheaf<'A, 'S>): Presheaf<'A, 'T> =
    let name = Name.apply f.Name dom.Name

    let ob =
        Map [ for A in f.Category.Objects do
                  let X =
                      Set.map (fun x -> f.Mapping.[A].[x]) dom.Ob.[A]

                  (A, X) ]

    let ar =
        Map [ for a in f.Category.Arrows do
                  let x =
                      Map [ for x in dom.Ob.[a.Cod] do
                                (f.Mapping.[a.Cod].[x], f.Mapping.[a.Dom].[dom.Ar.[a].[x]]) ]

                  (a, x) ]

    { Name = name
      Ob = ob
      Ar = ar
      Category = dom.Category }

/// Image of a morphism.
let image (f: Morphism<'A, 'S, 'T>): Presheaf<'A, 'T> = apply f f.Dom

/// Composition of morphisms.
let compose (g: Morphism<'A, 'T, 'U>) (f: Morphism<'A, 'S, 'T>): Morphism<'A, 'S, 'U> =
    let name = Name.compose g.Name f.Name

    let mapping =
        Map [ for A in g.Category.Objects do
                  let x = Map.compose g.Mapping.[A] f.Mapping.[A]
                  (A, x) ]

    { Name = name
      Mapping = mapping
      Dom = f.Dom
      Cod = g.Cod
      Category = f.Category }

/// Lifts a function to a morphism.
let lift (name: Name) (dom: Presheaf<'A, 'S>) (cod: Presheaf<'A, 'T>) (f: 'S -> 'T): Morphism<'A, 'S, 'T> =
    let mapping =
        Map [ for A in dom.Category.Objects do
                  let x =
                      Map [ for y in dom.Ob.[A] do
                                (y, f y) ]

                  (A, x) ]

    { Name = name
      Mapping = mapping
      Dom = dom
      Cod = cod
      Category = dom.Category }

/// Gives the inclusion morphism on a presheaf and codomain.
let inc (dom: Presheaf<'A, 'S>) (cod: Presheaf<'A, 'S>): Morphism<'A, 'S, 'S> =
    let name = Name.id dom.Name
    lift name dom cod id

/// Gives the identity morphism on a presheaf.
let id (dom: Presheaf<'A, 'S>): Morphism<'A, 'S, 'S> =
    let name = Name.id dom.Name
    lift name dom dom id

/// Gives the first projection morphism from a binary product presheaf.
let proj1 (dom: Presheaf<'A, 'S * 'T>): Morphism<'A, 'S * 'T, 'S> =
    let name = Name.proj 1 Name.empty

    let cod =
        let name = Name.proj 1 dom.Name

        let ob =
            dom.Ob |> Map.map (fun _ X -> Set.map fst X)

        let ar =
            dom.Ar
            |> Map.map (fun _ x -> x |> Map.doubleMap fst fst)

        { Name = name
          Ob = ob
          Ar = ar
          Category = dom.Category }

    lift name dom cod fst

/// Gives the second projection morphism from a binary product presheaf.
let proj2 (dom: Presheaf<'A, 'S * 'T>): Morphism<'A, 'S * 'T, 'T> =
    let name = Name.proj 2 Name.empty

    let cod =
        let name = Name.proj 2 dom.Name

        let ob =
            dom.Ob |> Map.map (fun _ X -> Set.map snd X)

        let ar =
            dom.Ar
            |> Map.map (fun _ x -> x |> Map.doubleMap snd snd)

        { Name = name
          Ob = ob
          Ar = ar
          Category = dom.Category }

    lift name dom cod snd

/// Binary product of presheaves. This is here because Morphism.product depends on it and the Presheaf module is later.
let internal presheafProduct (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'T>): Presheaf<'A, 'S * 'T> =
    let name = Name.product F.Name G.Name

    let ob =
        Map [ for A in F.Category.Objects do
                  let X = Set.product F.Ob.[A] G.Ob.[A]
                  (A, X) ]

    let ar =
        Map [ for a in F.Category.Arrows do
                  let x = Map.product F.Ar.[a] G.Ar.[a]
                  (a, x) ]

    { Name = name
      Ob = ob
      Ar = ar
      Category = F.Category }

/// Binary sum of presheaves. This is here because Morphism.sum depends on it and the Presheaf module is later.
let internal presheafSum (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'T>): Presheaf<'A, Choice<'S, 'T>> =
    let name = Name.sum F.Name G.Name

    let ob =
        Map [ for A in F.Category.Objects do
                  let X = Set.sum F.Ob.[A] G.Ob.[A]
                  (A, X) ]

    let ar =
        Map [ for a in F.Category.Arrows do
                  let x = Map.sum F.Ar.[a] G.Ar.[a]
                  (a, x) ]

    { Name = name
      Ob = ob
      Ar = ar
      Category = F.Category }

/// Binary product of morphisms.
let product (f: Morphism<'A, 'S, 'T>) (g: Morphism<'A, 'U, 'D>): Morphism<'A, ('S * 'U), ('T * 'D)> =
    let name = Name.product f.Name g.Name

    let mapping =
        Map [ for A in f.Category.Objects do
                  let x = Map.product f.Mapping.[A] g.Mapping.[A]
                  (A, x) ]

    let dom = presheafProduct f.Dom g.Dom
    let cod = presheafProduct f.Cod g.Cod

    { Name = name
      Mapping = mapping
      Dom = dom
      Cod = cod
      Category = dom.Category }

/// Binary sum of morphisms.
let sum (f: Morphism<'A, 'S, 'T>) (g: Morphism<'A, 'U, 'D>): Morphism<'A, Choice<'S, 'U>, Choice<'T, 'D>> =
    let name = Name.sum f.Name g.Name

    let mapping =
        Map [ for A in f.Category.Objects do
                  let x = Map.sum f.Mapping.[A] g.Mapping.[A]
                  (A, x) ]

    let dom = presheafSum f.Dom g.Dom
    let cod = presheafSum f.Cod g.Cod

    { Name = name
      Mapping = mapping
      Dom = dom
      Cod = cod
      Category = dom.Category }

/// Tuple of morphisms.
let tuple (f: Morphism<'A, 'S, 'T>) (g: Morphism<'A, 'S, 'U>): Morphism<'A, 'S, ('T * 'U)> =
    if f.Dom <> g.Dom
    then failwith "Cannot tuple morphisms with different domains."

    let name = Name.tuple f.Name g.Name

    let mapping =
        Map [ for A in f.Category.Objects do
                  let x = Map.tuple f.Mapping.[A] g.Mapping.[A]
                  (A, x) ]

    let dom = f.Dom
    let cod = presheafProduct f.Cod g.Cod

    { Name = name
      Mapping = mapping
      Dom = dom
      Cod = cod
      Category = dom.Category }

/// Cotuple of morphisms.
let cotuple (f: Morphism<'A, 'T, 'S>) (g: Morphism<'A, 'U, 'S>): Morphism<'A, Choice<'T, 'U>, 'S> =
    if f.Cod <> g.Cod
    then failwith "Cannot cotuple morphisms with different codomains."

    let name = Name.cotuple f.Name g.Name

    let mapping =
        Map [ for A in f.Category.Objects do
                  let x = Map.cotuple f.Mapping.[A] g.Mapping.[A]
                  (A, x) ]

    let dom = presheafSum f.Dom g.Dom
    let cod = f.Cod

    { Name = name
      Mapping = mapping
      Dom = dom
      Cod = cod
      Category = dom.Category }

/// Evaluation map of the exponential.
// todo
let eval (exp: Presheaf<'A, Morphism<'A, Arrow<'A> * 'S, 'T>>) (arg: Presheaf<'A, Arrow<'S>>): Presheaf<'A, 'T> =
    failwith "todo"

/// Terminal presheaf here because it is relied on by Morphism.one.
let internal presheafOne (cat: Category<'A>): Presheaf<'A, unit> =
    let ob =
        Map [ for A in cat.Objects do
                  (A, set [ () ]) ]

    let ar =
        Map [ for a in cat.Arrows do
                  (a, Map [ (), () ]) ]

    { Name = Name.ofInt 1
      Ob = ob
      Ar = ar
      Category = cat }

/// Morphism to the terminal object.
let one (cat: Category<'A>) (dom: Presheaf<'A, 'S>): Morphism<'A, 'S, unit> =
    let name = Name.one

    let mapping =
        Map [ for A in cat.Objects do
                  let x = Map.constant dom.Ob.[A] ()
                  (A, x) ]

    let dom = dom
    let cod = presheafOne cat

    { Name = name
      Mapping = mapping
      Dom = dom
      Cod = cod
      Category = dom.Category }
