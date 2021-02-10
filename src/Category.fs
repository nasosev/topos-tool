/// Functions specific to the `Category` type.
[<RequireQualifiedAccess>]
module Category

/// Helper function to create a category given a name, a set of objects, a set of nontrivial arrows, and map of nontrivial compositions.
let internal makeInternal (name: Name)
                          (objects: Set<'A>)
                          (nonidArrows: Set<Arrow<'A>>)
                          (nontrivCompose: Map<(Arrow<'A> * Arrow<'A>), Arrow<'A>>)
                          =

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

/// Helper function to create a category given a name, a set of objects, a set of nontrivial arrows, and map of nontrivial compositions, all as lists.
let make (nameString: string)
         (objectsList: List<'A>)
         (nonidArrowsList: List<Arrow<'A>>)
         (nontrivComposeList: List<(Arrow<'A> * Arrow<'A>) * Arrow<'A>>)
         =
    let name = Name.ofString nameString
    let objects = set objectsList
    let nonidArrows = set nonidArrowsList
    let nontrivCompose = Map.ofList nontrivComposeList
    makeInternal name objects nonidArrows nontrivCompose

/// Terminal category.
let one: Category<unit> =
    let name = Name.ofInt 1
    let objects = set [ () ]
    let nonidArrows = Set.empty
    let nontrivCompose = Map.empty
    makeInternal name objects nonidArrows nontrivCompose

/// Creates a category from a poset.
let ofPoset (nameString: string) (lessEq: Relation<'A, 'A>): Category<'A> =

    let name = Name.ofString nameString

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

    makeInternal name X nonidArrows nontrivCompose

/// Opposite of a category.
let op (C: Category<'A>): Category<'A> =
    let name = Name.op C.Name


    let nonidArrows = C.NonidArrows |> Set.map Arrow.flip

    let nontrivCompose =
        Map [ for a in nonidArrows do
                  for b in nonidArrows |> Set.filter (fun b -> b.Cod = a.Dom) do
                      ((a, b), Arrow.flip C.Compose.[Arrow.flip b, Arrow.flip a]) ]

    makeInternal name C.Objects nonidArrows nontrivCompose

/// Binary product of categories.
let product (C: Category<'A>) (D: Category<'B>): Category<'A * 'B> =

    let name = Name.product C.Name D.Name

    let objects = (C.Objects, D.Objects) ||> Set.product

    let productAr (a: Arrow<'A>, b: Arrow<'B>): Arrow<'A * 'B> =
        { Name = Name.tuple a.Name b.Name
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

    let nontrivCompose =
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

    makeInternal name objects nonidArrows nontrivCompose

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

    let nontrivCompose =
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

    makeInternal name objects nonidArrows nontrivCompose

/// Category of elements of a presheaf.
let ofElements (F: Presheaf<'A, 'S>): Category<'A * 'S> =
    let name = Name.categoryOfElements F.Name

    let objects =
        set [ for A in F.Cat.Objects do
                  for X in F.Ob.[A] do
                      (A, X) ]

    let lift (X, X': 'S) (a: Arrow<'A>): Arrow<'A * 'S> =
        let name =
            Name.sup a.Name (Name.exp (Name.name X) (Name.name X'))

        { Name = name
          Dom = (a.Dom, X)
          Cod = (a.Cod, X') }

    let nonidArrows =
        set [ for a in F.Cat.NonidArrows do
                  F.Ob.[a.Cod]
                  |> Set.filter (fun s -> Set.contains F.Ar.[a].[s] F.Ob.[a.Dom])
                  |> Set.map (fun s -> lift (F.Ar.[a].[s], s) a) ]
        |> Set.unionMany

    let nontrivCompose =
        let proj1 (a: Arrow<'A * 'S>): Arrow<'A> =
            let name =
                let ind = a.Name.String.IndexOf "^" // Todo: this is fragile.

                a.Name.String.Substring(1, ind - 2)
                |> Name.ofString

            { Name = name
              Dom = fst a.Dom
              Cod = fst a.Cod }

        [ for a in nonidArrows do
            for b in nonidArrows |> Set.filter (fun b -> b.Dom = a.Cod) do
                let ba =
                    let dom, cod = (snd a.Dom, snd b.Cod)
                    lift (dom, cod) (F.Cat.Compose.[proj1 b, proj1 a])

                ((b, a), ba) ]
        |> List.filter (fun ((_, _), ba) -> F.Cat.NonidArrows |> Set.contains (proj1 ba)) // Remove pairs whose composite is trivial. // Remove trivial composites.
        |> Map

    makeInternal name objects nonidArrows nontrivCompose

/// Comma category.
let comma (S: Functor<'A, 'C>) (T: Functor<'B, 'C>): Category<'A * 'B * Arrow<'C>> =
    if S.Cod <> T.Cod then failwith Error.codomainMismatch

    let name = Name.comma S.Name T.Name

    let cat = S.Cod

    let objects =
        set [ for A in S.Dom.Objects do
                  for B in T.Dom.Objects do
                      cat.Arrows
                      |> Set.filter (fun a -> a.Dom = S.Ob.[A] && a.Cod = T.Ob.[B])
                      |> Set.map (fun a -> (A, B, a)) ]
        |> Set.unionMany

    let lift (a: Arrow<'A>, b: Arrow<'B>) (dom: 'A * 'B * Arrow<'C>, cod: 'A * 'B * Arrow<'C>): Arrow<'A * 'B * Arrow<'C>> =
        let name =
            Name.sup (Name.tuple a.Name b.Name) (Name.exp (Name.name (third dom)) (Name.name (third cod)))

        { Name = name; Dom = dom; Cod = cod }

    let nonidArrows =
        let nonidArrowsPairs =
            (S.Dom.Arrows, T.Dom.Arrows)
            ||> Set.product
            |> Set.filter (fun (a, b) -> not (a = S.Dom.Id.[a.Dom] && b = T.Dom.Id.[b.Dom])) // Remove ids

        set [ for dom in objects do
                  for cod in objects do
                      nonidArrowsPairs
                      |> Set.filter (fun (a, b) ->
                          S.Ar.[a].Cod = (third cod).Dom
                          && T.Ar.[b].Dom = (third dom).Cod
                          && cat.Compose.[third cod, S.Ar.[a]] = cat.Compose.[T.Ar.[b], third dom])
                      |> Set.map (fun (a, b) -> lift (a, b) (dom, cod)) ]
        |> Set.unionMany

    let nontrivCompose =
        [ for a in nonidArrows do
            for b in nonidArrows |> Set.filter (fun b -> b.Dom = a.Cod) do
                let ba =
                    let dom, cod = (a.Dom, b.Cod)

                    let ba1 =
                        S.Dom.Compose.[Arrow.proj3_1 b, Arrow.proj3_1 a]

                    let ba2 =
                        T.Dom.Compose.[Arrow.proj3_2 b, Arrow.proj3_2 a]

                    lift (ba1, ba2) (dom, cod)

                ((b, a), ba) ]
        |> List.filter (fun ((_, _), ba) ->
            (S.Dom.NonidArrows
             |> Set.contains (Arrow.proj3_1 ba))
            || (T.Dom.NonidArrows
                |> Set.contains (Arrow.proj3_2 ba))) // Remove pairs whose composite is trivial.
        |> Map

    makeInternal name objects nonidArrows nontrivCompose

/// Arrow category.
let arrow (cat: Category<'A>): Category<Arrow<'A>> = failwith Error.todo // Todo cyclic dependency issue because we want to use Arrow.proj_31
