/// Functions specific to the 'Morphism' type.
[<RequireQualifiedAccess>]
module Morphism

/// Determines if the map of presheaves is a morphism.
let isMorphism (dom: Presheaf<'A, 'S>) (cod: Presheaf<'A, 'T>) (mapping: Map<'A, Map<'S, 'T>>): bool =
    Map.dom mapping = Map.dom dom.Ob // Check the mapping is defined on all objects.
    && dom.Ar // Then check naturality.
       |> Map.dom
       |> Set.forall (fun a ->
           dom.Ob.[a.Cod]
           |> Set.forall (fun x -> mapping.[a.Dom].[dom.Ar.[a].[x]] = cod.Ar.[a].[mapping.[a.Cod].[x]]))

/// Helper function to make a morphism.
let make (nameString: string)
         (dom: Presheaf<'A, 'S>)
         (cod: Presheaf<'A, 'T>)
         (mapping: Map<'A, Map<'S, 'T>>)
         : Morphism<'A, 'S, 'T> =
    if not (isMorphism dom cod mapping) then failwith "That is not a morphism."
    let name = Name.ofString nameString
    { Name = name; Mapping = mapping }

/// Determines if the morphism is mono.
let isMono (n: Morphism<'A, 'S, 'T>): bool =
    n.Mapping |> Map.forall (fun _ -> Map.isInjective)

/// Determines if the morphism is epi.
let isEpi (cod: Presheaf<'A, 'T>) (n: Morphism<'A, 'S, 'T>): bool =
    n.Mapping
    |> Map.forall (fun A x -> Map.isSurjective x cod.Ob.[A])

/// Determines if the morphism is an isomorphism.
// Note: the order of conjunctions impacts performance due to short-circuiting.
let isIso (cod: Presheaf<'A, 'T>) (n: Morphism<'A, 'S, 'T>): bool = isEpi cod n && isMono n

/// External hom of presheaves.
let hom (F: Presheaf<'A, 'S>) (G: Presheaf<'A, 'T>): Set<Morphism<'A, 'S, 'T>> =
    [ for A in Map.dom F.Ob do
        [ for x in Set.exp F.Ob.[A] G.Ob.[A] do
            (A, x) ] ]
    |> List.listProduct
    |> List.map map
    |> List.filter (isMorphism F G)
    |> List.mapi (fun i mapping ->
        let name =
            Name.sub (Name.hom F.Name G.Name) (Name.ofString $"{i}")

        { Name = name; Mapping = mapping })
    |> set

/// Gives the set of isomorphisms between two presheaves.
let iso (dom: Presheaf<'A, 'S>) (cod: Presheaf<'A, 'T>): Set<Morphism<'A, 'S, 'T>> =
    hom dom cod |> Set.filter (isIso cod)

/// Applies a morphism to a presheaf.
let apply (n: Morphism<'A, 'S, 'T>) (dom: Presheaf<'A, 'S>): Presheaf<'A, 'T> =
    let name = Name.compose n.Name dom.Name

    let ob =
        map [ for A in Map.dom dom.Ob do
                  let X =
                      Set.map (fun x -> n.Mapping.[A].[x]) dom.Ob.[A]

                  (A, X) ]

    let ar =
        map [ for a in Map.dom dom.Ar do
                  let x =
                      map [ for x in dom.Ob.[a.Cod] do
                                (n.Mapping.[a.Cod].[x], n.Mapping.[a.Dom].[dom.Ar.[a].[x]]) ]

                  (a, x) ]

    { Name = name; Ob = ob; Ar = ar }

/// Composition of morphisms.
let compose (n: Morphism<'A, 'T, 'U>) (m: Morphism<'A, 'S, 'T>): Morphism<'A, 'S, 'U> =
    let name = Name.compose n.Name m.Name

    let mapping =
        map [ for A in Map.dom n.Mapping do
                  let x = Map.compose n.Mapping.[A] m.Mapping.[A]
                  (A, x) ]

    { Name = name; Mapping = mapping }

/// Lifts a function to a morphism.
let lift (F: Presheaf<'A, 'S>) (f: 'S -> 'T) (name: Name): Morphism<'A, 'S, 'T> =
    let mapping =
        map [ for A in Map.dom F.Ob do
                  let x =
                      map [ for y in F.Ob.[A] do
                                (y, f y) ]

                  (A, x) ]

    { Name = name; Mapping = mapping }

/// Gives the identity morphism on a presheaf.
/// Note: conflates with an inclusion as the data of the codomain is not part of the encoding of functions as `Map`
/// types.
let id (dom: Presheaf<'A, 'S>): Morphism<'A, 'S, 'S> =
    let name = Name.id dom.Name
    lift dom id name

/// Gives the first projection morphism from a binary product presheaf.
let proj1 (dom: Presheaf<'A, 'S * 'T>): Morphism<'A, 'S * 'T, 'S> =
    let name = Name.sub Name.pi (Name.ofInt 1)
    lift dom fst name

/// Gives the second projection morphism from a binary product presheaf.
let proj2 (dom: Presheaf<'A, 'S * 'T>): Morphism<'A, 'S * 'T, 'T> =
    let name = Name.sub Name.pi (Name.ofInt 2)
    lift dom snd name

/// Binary product of morphisms.
let product (n: Morphism<'A, 'S, 'T>) (m: Morphism<'A, 'U, 'D>): Morphism<'A, ('S * 'U), ('T * 'D)> =
    let name = Name.product n.Name m.Name

    let mapping =
        map [ for A in Map.dom n.Mapping do
                  let x = Map.product n.Mapping.[A] m.Mapping.[A]
                  (A, x) ]

    { Name = name; Mapping = mapping }

/// Binary sum of morphisms.
let sum (n: Morphism<'A, 'S, 'T>) (m: Morphism<'A, 'U, 'D>): Morphism<'A, Choice<'S, 'U>, Choice<'T, 'D>> =
    let name = Name.sum n.Name m.Name

    let mapping =
        map [ for A in Map.dom n.Mapping do
                  let x = Map.sum n.Mapping.[A] m.Mapping.[A]
                  (A, x) ]

    { Name = name; Mapping = mapping }

/// Evaluation map of the exponential.
// todo
let eval (exp: Presheaf<'A, Morphism<'A, Arrow<'A> * 'S, 'T>>) (arg: Presheaf<'A, Arrow<'S>>): Presheaf<'A, 'T> =
    failwith "todo"
