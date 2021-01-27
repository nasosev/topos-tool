/// Functions specific to the 'Category' type.
[<RequireQualifiedAccess>]
module Category

/// Helper function to create a category given a name, a set of objects, a set of nontrivial arrows, and map of nontrivial compositions.
let make (nameString: string)
         (objects: Set<'A>)
         (nonidArrows: Set<Arrow<'A>>)
         (nontrivCompose: Map<(Arrow<'A> * Arrow<'A>), Arrow<'A>>)
         =
    let name = Name.ofString nameString

    let id =
        Map [ for A in objects do
                  (A, Arrow.id A) ]

    let compose =
        let obIds = // Adds composites of the form 1 * 1 = 1.
            set [ for A in objects do
                      ((id.[A], id.[A]), id.[A]) ]

        let domIds = // Adds composites of the a * 1 = a.
            set [ for a in nonidArrows do
                      ((a, id.[a.Dom]), a) ]

        let codIds = // Adds composites of the form 1 * a = a.
            set [ for a in nonidArrows do
                      ((id.[a.Cod], a), a) ]

        let unspecifiedIds = // Adds composites of the form a * b = 1.
            let suppliedComps = nontrivCompose |> Map.dom

            nonidArrows
            |> Set.square
            |> Set.filter (fun (a, b) ->
                b.Cod = a.Dom
                && a.Cod = b.Dom
                && not (Set.contains (a, b) suppliedComps))
            |> Set.map (fun (a, b) -> ((a, b), id.[b.Dom]))

        [ Map.toSet nontrivCompose
          obIds
          domIds
          codIds
          unspecifiedIds ]
        |> Set.unionMany
        |> Map

    let hom =
        let homDom (compose: Map<Arrow<'A> * Arrow<'A>, Arrow<'A>>) (A: 'A): Set<Arrow<'A>> =
            compose
            |> Map.filter (fun (_, B) _ -> B = id.[A])
            |> Map.image

        let homCod (compose: Map<Arrow<'A> * Arrow<'A>, Arrow<'A>>) (A: 'A): Set<Arrow<'A>> =
            compose
            |> Map.filter (fun (B, _) _ -> B = id.[A])
            |> Map.image

        let homset (compose: Map<Arrow<'A> * Arrow<'A>, Arrow<'A>>) (A: 'A, B: 'A): Set<Arrow<'A>> =
            Set.intersect (homDom compose A) (homCod compose B)

        Map [ for A in objects do
                  for B in objects do
                      let homAB = homset compose (A, B)
                      (A, B), homAB ]

    let arrows = hom |> Map.image |> Set.unionMany

    if not
        (let pairs = Set.square arrows
         let composeDomain = Map.dom compose
         let composable (a: Arrow<'A>, b: Arrow<'A>): bool = b.Cod = a.Dom

         pairs
         |> Set.forall (fun ab -> composable ab => Set.contains ab composeDomain)) then
        failwith Error.makeCategory

    { Name = name
      Objects = objects
      Arrows = arrows
      NonidArrows = nonidArrows
      Id = id
      Hom = hom
      Compose = compose }

/// Binary product of categories.
let product (C: Category<'A>) (D: Category<'B>): Category<'A * 'B> =

    let name = Name.product C.Name D.Name

    let objects = (C.Objects, D.Objects) ||> Set.product

    let productAr (a: Arrow<'A>, b: Arrow<'B>): Arrow<'A * 'B> =
        { Name = Name.product a.Name b.Name
          Dom = (a.Dom, b.Dom)
          Cod = (a.Cod, b.Cod) }

    let nonidArrows =
        (C.Arrows, D.Arrows)
        ||> Set.product
        |> Set.filter (fun (a, b) ->
            not
                (Set.contains a (Map.image C.Id)
                 && Set.contains b (Map.image D.Id)))
        |> Set.map productAr

    let compose =
        let filterNonid (compose: Map<(Arrow<'A * 'B> * Arrow<'A * 'B>), Arrow<'A * 'B>>)
                        : Map<(Arrow<'A * 'B> * Arrow<'A * 'B>), Arrow<'A * 'B>> =
            compose
            |> Map.filter (fun (a, b) c ->
                Set.contains a nonidArrows
                && Set.contains b nonidArrows
                && Set.contains c nonidArrows)

        (Map.toSet C.Compose, Map.toSet D.Compose)
        ||> Set.product
        |> Set.map (fun (((a, a'), a''), ((b, b'), b'')) ->
            ((productAr (a, b), productAr (a', b')), productAr (a'', b'')))
        |> Map
        |> filterNonid // Todo: it would be more efficient to filter first.

    make name.String objects nonidArrows compose

/// Binary sum of categories.
let sum (C: Category<'A>) (D: Category<'B>): Category<Choice<'A, 'B>> =

    let name = Name.sum C.Name D.Name

    let coproj1 (a: Arrow<'A>): Arrow<Choice<'A, 'B>> =
        { Name = Name.coproj 1 a.Name
          Dom = Choice1Of2 a.Dom
          Cod = Choice1Of2 a.Cod }

    let coproj2 (a: Arrow<'B>): Arrow<Choice<'A, 'B>> =
        { Name = Name.coproj 2 a.Name
          Dom = Choice2Of2 a.Dom
          Cod = Choice2Of2 a.Cod }

    let objects = (C.Objects, D.Objects) ||> Set.sum

    let nonidArrows =
        (C.NonidArrows |> Set.map coproj1, D.NonidArrows |> Set.map coproj2)
        ||> Set.union

    let compose =
        let tripleMap (f: 'a -> 'b) ((a: 'a, a': 'a), a'': 'a): ('b * 'b) * 'b = ((f a, f a'), f a'')

        let liftComposeC =
            C.Compose
            |> Map.toSet
            |> Set.map (tripleMap coproj1)

        let liftComposeD =
            D.Compose
            |> Map.toSet
            |> Set.map (tripleMap coproj2)

        let filterNonid (compose: Map<(Arrow<Choice<'A, 'B>> * Arrow<Choice<'A, 'B>>), Arrow<Choice<'A, 'B>>>)
                        : Map<(Arrow<Choice<'A, 'B>> * Arrow<Choice<'A, 'B>>), Arrow<Choice<'A, 'B>>> =
            compose
            |> Map.filter (fun (a, b) c ->
                Set.contains a nonidArrows
                && Set.contains b nonidArrows
                && Set.contains c nonidArrows)

        (liftComposeC, liftComposeD)
        ||> Set.union
        |> Map
        |> filterNonid

    make name.String objects nonidArrows compose

/// Category of elements of a presheaf.
let ofElements (F: Presheaf<'A, 'S>): Category<'A * 'S> =
    let name = Name.categoryOfElements F.Name

    let objects =
        set [ for A in F.Category.Objects do
                  for X in F.Ob.[A] do
                      (A, X) ]

    let lift (X, X': 'S) (a: Arrow<'A>): Arrow<'A * 'S> =
        { Name = a.Name
          Dom = (a.Dom, X)
          Cod = (a.Cod, X') }

    let nonidArrows =
        set [ for a in F.Category.NonidArrows do
                  F.Ob.[a.Cod]
                  |> Set.filter (fun s -> Set.contains F.Ar.[a].[s] F.Ob.[a.Dom])
                  |> Set.map (fun s -> lift (F.Ar.[a].[s], s) a) ]
        |> Set.unionMany

    let compose =
        let proj1 (a: Arrow<'A * 'S>): Arrow<'A> =
            { Name = a.Name
              Dom = fst a.Dom
              Cod = fst a.Cod }

        [ for a in nonidArrows do
            for b in nonidArrows |> Set.filter (fun b -> b.Dom = a.Cod) do
                let ba =
                    let dom, cod = (snd a.Dom, snd b.Cod)
                    lift (dom, cod) (F.Category.Compose.[proj1 b, proj1 a])

                ((b, a), ba) ]
        |> List.filter (fun ((_, _), ba) -> F.Category.NonidArrows |> Set.contains (proj1 ba))
        |> Map

    make name.String objects nonidArrows compose

/// Creates a category from a poset.
let ofPoset (nameString: string) (lessEq: Relation<'A, 'A>): Category<'A> =
    let X = Relation.dom lessEq

    let singletonArrow (A: 'A, B: 'A): Arrow<'A> =
        { Name = Name.lessEq (Name.name A) (Name.name B)
          Dom = A
          Cod = B }

    let nonidArrows =
        Set.square X
        |> Set.filter (fun (A, B) -> A <> B && lessEq.[A, B])
        |> Set.map singletonArrow

    let nontrivCompose =
        Map [ for a in nonidArrows do
                  for b in nonidArrows |> Set.filter (fun b -> b.Cod = a.Dom) do
                      let ba = singletonArrow (b.Dom, a.Cod)
                      ((a, b), ba) ]

    make nameString X nonidArrows nontrivCompose
