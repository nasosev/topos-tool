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

        (Map.toSet C.Compose, Map.toSet D.Compose)
        ||> Set.product
        |> Set.map (fun (((a, a'), a''), ((b, b'), b'')) ->
            ((productAr (a, b), productAr (a', b')), productAr (a'', b'')))
        |> map
        |> filterId // todo: it would be more efficient to filter first.

    make name.String objects nonidArrows compose

/// Infix version of Category.product.
let (*) product (C: Category<'A>) (D: Category<'B>): Category<'A * 'B> = product C D

/// todo: Binary sum of categories.

/// Category of elements of a presheaf.
let ofElements (cat: Category<'A>) (F: Presheaf<'A, 'S>): Category<'A * 'S> =
    let name = Name.categoryOfElements F.Name

    let objects =
        set [ for A in cat.Objects do
                  for X in F.Ob.[A] do
                      (A, X) ]

    let lift (X, X': 'S) (a: Arrow<'A>): Arrow<'A * 'S> =
        { Name = a.Name
          Dom = (a.Dom, X)
          Cod = (a.Cod, X') }

    let nonidArrows =
        set [ for a in cat.NonidArrows do
                  F.Ob.[a.Cod]
                  |> Set.filter (fun s -> Set.contains F.Ar.[a].[s] F.Ob.[a.Dom])
                  |> Set.map (fun s -> lift (F.Ar.[a].[s], s) a) ]
        |> Set.unionMany

    let compose =
        let proj1 (a: Arrow<'A * 'S>): Arrow<'A> =
            { Name = a.Name
              Dom = fst a.Dom
              Cod = fst a.Cod }

        map [ for a in nonidArrows do
                  for b in nonidArrows |> Set.filter (fun b -> b.Dom = a.Cod) do
                      let ba =
                          let dom, cod = (snd b.Dom, snd a.Cod)
                          lift (dom, cod) (cat.Compose.[proj1 b, proj1 a])

                      ((b, a), ba) ]

    make name.String objects nonidArrows compose

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
