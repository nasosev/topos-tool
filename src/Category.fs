/// Functions specific to the 'Category' type.
[<RequireQualifiedAccess>]
module Category

/// Helper function to create a category given a name, a set of objects, a set of nontrivial arrows, and map of nontrivial compositions.
let make (nameStr: string)
         (objects: Set<'A>)
         (nonidArrows: Set<Arrow<'A>>)
         (nontrivCompose: Map<(Arrow<'A> * Arrow<'A>), Arrow<'A>>)
         =
    let name = Name.ofString nameStr

    let id =
        map [ for A in objects do
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
            |> Set.filter (fun (a, b) -> b.Cod = a.Dom && a.Cod = b.Dom)
            |> Set.filter (fun ab -> Set.contains ab suppliedComps |> not)
            |> Set.map (fun (a, b) -> ((a, b), id.[b.Dom]))

        [ Map.toSet nontrivCompose
          obIds
          domIds
          codIds
          unspecifiedIds ]
        |> Set.unionMany
        |> map

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

        map [ for A in objects do
                  for B in objects do
                      let homAB = homset compose (A, B)
                      (A, B), homAB ]

    let arrows = hom |> Map.image |> Set.unionMany

    if not
        (let pairs = Set.square arrows
         let composeDomain = Map.dom compose
         let composable (a: Arrow<'A>, b: Arrow<'A>): bool = b.Cod = a.Dom

         pairs
         |> Set.forall (fun ab ->
             (not (composable ab))
             || Set.contains ab composeDomain)) then
        failwith "Not all composable pairs appear in the compose map." // Check all composable pairs appear in the composition map.

    { Name = name
      Objects = objects
      Arrows = arrows
      NonidArrows = nonidArrows
      Id = id
      Hom = hom
      Compose = compose }

/// Binary product of categories.
let product (C: Category<'A>) (D: Category<'B>): Category<'A * 'B> =
    let productAr (a: Arrow<'A>, b: Arrow<'B>): Arrow<'A * 'B> =
        { Name = Name.product a.Name b.Name
          Dom = (a.Dom, b.Dom)
          Cod = (a.Cod, b.Cod) }

    let name = Name.product C.Name D.Name
    let objects = (C.Objects, D.Objects) ||> Set.product

    let nonidArrows =
        (C.Arrows, D.Arrows)
        ||> Set.product
        |> Set.filter (fun (a, b) ->
            not
                (Set.contains a (Map.image C.Id)
                 && Set.contains b (Map.image D.Id)))
        |> Set.map productAr

    let compose =
        let filterId (compose: Map<(Arrow<'A * 'B> * Arrow<'A * 'B>), Arrow<'A * 'B>>)
                     : Map<(Arrow<'A * 'B> * Arrow<'A * 'B>), Arrow<'A * 'B>> =
            compose
            |> Map.filter (fun (a, b) c ->
                Set.contains a nonidArrows
                && Set.contains b nonidArrows
                && Set.contains c nonidArrows)

        (Map.toList C.Compose, Map.toList D.Compose)
        ||> List.product
        |> List.map (fun (((a, a'), a''), ((b, b'), b'')) ->
            ((productAr (a, b), productAr (a', b')), productAr (a'', b'')))
        |> map
        |> filterId // todo: it would be more efficient to filter first.

    make name.String objects nonidArrows compose

/// Infix version of Category.product.
let (*) product (C: Category<'A>) (D: Category<'B>): Category<'A * 'B> = product C D

/// todo: Binary sum of categories.

/// Category of elements of a presheaf.
// todo: rewrite  to use `make`
let ofElements (cat: Category<'A>) (F: Presheaf<'A, 'S>): Category<'A * 'S> =
    let name = Name.categoryOfElements F.Name

    let objects =
        set [ for A in cat.Objects do
                  for X in F.Ob.[A] do
                      (A, X) ]

    let liftAr (X, X': 'S) (a: Arrow<'A>): Arrow<'A * 'S> =
        { Name = Name.sup a.Name (Name.exp (Name.name a.Dom) (Name.name a.Cod))
          Dom = (a.Dom, X)
          Cod = (a.Cod, X') }

    let hom =
        map [ for ((A, X), (A', X')) in Set.square objects do
                  let homAXBY =
                      cat.Hom.[A, A']
                      |> Set.filter (fun a -> F.Ar.[a].[X'] = X)
                      |> Set.map (liftAr (X, X'))

                  (((A, X), (A', X')), homAXBY) ]

    let id =
        map [ for AX in objects do
                  (AX, Arrow.id AX) ]

    let compose =
        let projectAr1 (a: Arrow<'A * 'S>): Arrow<'A> =
            { Name = Name.trimSup a.Name
              Dom = fst a.Dom
              Cod = fst a.Cod }

        let projectAr2 (a: Arrow<'A * 'S>): Arrow<'S> =
            { Name = Name.ofString ""
              Dom = snd a.Dom
              Cod = snd a.Cod }

        map [ for (B, (C, D)) in Set.product objects (Set.square objects) do
                  for (b, b') in Set.product hom.[B, C] hom.[C, D] do
                      let a, a' = projectAr1 b, projectAr1 b'

                      let dom, cod =
                          ((projectAr2 b).Dom, (projectAr2 b').Cod)

                      let b'b = liftAr (dom, cod) (cat.Compose.[a', a])
                      ((b, b'), b'b) ]

    let arrows = hom |> Map.image |> Set.unionMany
    let nonidArrows = id |> Map.image |> Set.difference arrows

    { Name = name
      Objects = objects
      Arrows = arrows
      NonidArrows = nonidArrows
      Hom = hom
      Id = id
      Compose = compose }

// todo: Comma category, slice categories.

/// Creates a category from a poset.
let ofPoset (nameStr: string) (lessEq: Relation<'A, 'A>): Category<'A> =
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
        map [ for a in nonidArrows do
                  for b in nonidArrows |> Set.filter (fun b -> b.Cod = a.Dom) do
                      let ba = singletonArrow (b.Dom, a.Cod)
                      ((a, b), ba) ]

    make nameStr X nonidArrows nontrivCompose
