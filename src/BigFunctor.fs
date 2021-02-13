/// Functions specific to the `BigFunctor` type that encodes a functor from a base category to its presheaf category.
[<RequireQualifiedAccess>]
module BigFunctor

/// Determines if the arrow-indexed set of maps is functorial.
let isFunctorial (dom: Category<'I>) (ar: Map<Arrow<'I>, Morphism<'A, 'S, 'S>>): bool =
    dom.Compose
    |> Map.forall (fun (g, f) gf -> Morphism.compose ar.[g] ar.[f] = ar.[gf])

/// Helper to create a functor from supplied domain and codomain categories, object map and nontrivial arrow map.
let make (dom: Category<'I>)
         (obList: List<'I * Presheaf<'A, 'S>>)
         (nonidArList: List<Arrow<'I> * Morphism<'A, 'S, 'S>>)
         : BigFunctor<'I, 'A, 'S> =

    if List.length obList = 0 then failwith Error.emptyInput
    let cat = (obList |> Seq.item 0 |> snd).Cat
    let name = dom.Name

    let ob = Map obList
    let nonidAr = Map nonidArList

    let ar =
        let idArrow =
            Map [ for I in dom.Objects do
                      (dom.Id.[I], Morphism.id ob.[I]) ]

        Map.union idArrow nonidAr

    if not (isFunctorial dom ar) then failwith Error.makeFunctor

    { Name = name
      Ob = ob
      Ar = ar
      Dom = dom
      Cat = cat }
