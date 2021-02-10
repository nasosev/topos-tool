/// Functions specific to the `Functor` type.
module Functor

/// Determines if the arrow-indexed set of maps is functorial.
let isFunctorial (dom: Category<'A>) (cod: Category<'B>) (ar: Map<Arrow<'A>, Arrow<'B>>): bool =
    dom.Compose
    |> Map.forall (fun (g, f) gf -> cod.Compose.[ar.[f], ar.[g]] = ar.[gf])

/// Helper to create a functor from supplied domain and codomain categories, object map and nontrivial arrow map.
let make (nameString: string)
         (dom: Category<'A>)
         (cod: Category<'B>)
         (ob: Map<'A, 'B>)
         (nonidAr: Map<Arrow<'A>, Arrow<'B>>)
         : Functor<'A, 'B> =

    let name = Name.ofString nameString

    let ar =
        let idArrow =
            Map [ for A in dom.Objects do
                      (dom.Id.[A], cod.Id.[ob.[A]]) ]

        Map.union idArrow nonidAr

    if not (isFunctorial dom cod ar) then failwith Error.makeFunctor

    { Name = name
      Ob = ob
      Ar = ar
      Dom = dom
      Cod = cod }

/// Constant functor on an object of the codomain.
let constant (dom: Category<'A>) (cod: Category<'B>) (B: 'B): Functor<'A, 'B> =
    let name = Name.name B

    let ob =
        Map [ for A in dom.Objects do
                  (A, B) ]

    let ar =
        Map [ for a in dom.Arrows do
                  (a, cod.Id.[B]) ]

    { Name = name
      Ob = ob
      Ar = ar
      Dom = dom
      Cod = cod }

/// Identity functor on a category.
let id (dom: Category<'A>): Functor<'A, 'A> =
    let name = Name.id dom.Name

    let ob =
        Map [ for A in dom.Objects do
                  (A, A) ]

    let ar =
        Map [ for a in dom.Arrows do
                  (a, a) ]

    { Name = name
      Ob = ob
      Ar = ar
      Dom = dom
      Cod = dom }

/// Composition of functors.
let compose (P: Functor<'B, 'C>) (Q: Functor<'A, 'B>): Functor<'A, 'C> =
    let name = Name.compose P.Name Q.Name

    let ob =
        Map [ for A in Q.Dom.Objects do
                  (A, P.Ob.[Q.Ob.[A]]) ]

    let ar =
        Map [ for a in Q.Dom.Arrows do
                  (a, P.Ar.[Q.Ar.[a]]) ]

    { Name = name
      Ob = ob
      Ar = ar
      Dom = Q.Dom
      Cod = P.Cod }

/// Applies a functor to a category.
let apply (P: Functor<'A, 'B>) (cat: Category<'A>): Category<'B> = failwith Error.todo

/// Projection from a triple product category onto the first factor.
let proj3_1 (dom: Category<'A * 'B * 'C>): Functor<'A * 'B * 'C, 'A> =
    let name = Name.proj 1 dom.Name

    let ob =
        Map [ for A in dom.Objects do
                  (A, first A) ]

    let ar =
        Map [ for a in dom.Arrows do
                  (a, Arrow.proj3_1 a) ]

    let cod =
        let name = Name.proj 1 dom.Name

        let objects = dom.Objects |> Set.map first

        let nonidArrows =
            dom.NonidArrows
            |> Set.map Arrow.proj3_1
            |> Set.filter (Arrow.isId >> not)

        let nontrivCompose =
            Map [ for a in nonidArrows do
                      for b in nonidArrows |> Set.filter (fun b -> b.Cod = a.Dom) do
                          let ab =
                              dom.Compose
                              |> Map.doubleMap (fun (c, d) -> (Arrow.proj3_1 c, Arrow.proj3_1 d)) Arrow.proj3_1
                              |> Map.filter (fun (c, d) _ -> c = a && d = b)
                              |> Map.toSeq
                              |> Seq.item 0
                              |> snd

                          ((a, b), ab) ]

        Category.makeInternal name objects nonidArrows nontrivCompose

    { Name = name
      Ob = ob
      Ar = ar
      Dom = dom
      Cod = cod }
