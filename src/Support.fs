/// Helper functions and type extensions. Auto-opened.
[<AutoOpen>]
module Support

/// Type for a binary relation between homogenous sets.
type Relation<'A, 'B when 'A: comparison and 'B: comparison> =
    | Relation of Map<'A * 'B, bool>
    member __.Item(a: 'A, b: 'B): bool =
        let (Relation m) = __
        m.[a, b]

/// Boolean logical operators
[<AutoOpen>]
module BooleanLogic =

    /// Implication.
    let (=>) (p: bool) (q: bool): bool = (not p) || q

    /// Equivalence.
    let (<=>) (p: bool) (q: bool): bool = (p && q) || ((not p) && (not q))

[<RequireQualifiedAccess>]
module List =

    /// Binary product of lists.
    let product (xs: List<'A>) (ys: List<'B>): List<'A * 'B> =
        [ for x in xs do
            for y in ys do
                (x, y) ]

    /// Cartesian product of a list of lists; elements are lists and not tuples.
    let rec listProduct: List<List<'A>> -> List<List<'A>> =
        function
        | [ zs ] -> List.fold (fun wss w -> [ w ] :: wss) [] zs
        | zs :: zss ->
            List.fold (fun yss ys ->
                (List.fold (fun zss z -> (z :: ys) :: zss) [] zs)
                @ yss) [] (listProduct zss)
        | _ -> []

    /// Permutations of a list.
    let rec permutations (xs: List<'A>) =
        if List.isEmpty xs then
            [ [] ]
        else
            [ for x in xs do
                yield!
                    xs
                    |> List.filter ((<>) x)
                    |> permutations
                    |> List.map (fun xs -> x :: xs) ]

[<RequireQualifiedAccess>]
module Set =

    /// Binary product of sets.
    let product (X: Set<'A>) (Y: Set<'B>): Set<'A * 'B> =
        (Set.toList X, Set.toList Y)
        ||> List.product
        |> set

    /// Square of sets.
    let square (X: Set<'A>): Set<'A * 'A> = product X X

    /// Binary sum of sets.
    let sum (X: Set<'A>) (Y: Set<'B>): Set<Choice<'A, 'B>> =
        Set.union (Set.map Choice1Of2 X) (Set.map Choice2Of2 Y)

    /// Binary cosquare of sets, i.e. X + X.
    let cosquare (X: Set<'A>): Set<Choice<'A, 'A>> = sum X X

    /// Set of subsets of a set.
    let rec powerset (X: Set<'A>): Set<Set<'A>> =
        set [ yield X
              for s in X do
                  yield! powerset (Set.remove s X) ]

    /// Partitions a set into equivalence classes from an equivalence relation.
    let partitionByEquivalence (equal: Relation<'A, 'A>) (X: Set<'A>): Set<Set<'A>> =
        let splitFirst (equal: Relation<'A, 'A>) (xs: List<'A>): List<'A> * List<'A> =
            match xs with
            | x :: _ as xs -> List.partition (fun y -> equal.[x, y]) xs
            | [] -> ([], [])

        let rec classes (equal: Relation<'A, 'A>) (xs: List<'A>): List<List<'A>> =
            match xs with
            | [] -> []
            | xs ->
                let (fg, rst) = splitFirst equal xs
                fg :: classes equal rst

        X
        |> Set.toList
        |> classes equal
        |> List.map set
        |> set

/// Contains operations for working with values of type `Relation`.
[<RequireQualifiedAccess>]
module Relation =

    /// Converts a relation to a `Map` type.
    let toMap (Relation m: Relation<'A, 'B>): Map<('A * 'B), bool> = m

    /// Converts a relation to a `List` type.
    let toList (Relation m: Relation<'A, 'B>): List<('A * 'B) * bool> = Map.toList m

    /// Converts a `List` type to a relation.
    let ofList (xs: List<('A * 'B) * bool>): Relation<'A, 'B> = xs |> Map |> Relation

    /// Gives the set of related pairs of a relation.
    let ofPairs (dom: Set<'A>) (cod: Set<'B>) (ps: Set<'A * 'B>): Relation<'A, 'B> =
        [ for a in dom do
            for b in cod do
                ((a, b), Set.contains (a, b) ps) ]
        |> ofList

    /// Converts a relation to the set of related pairs.
    let toPairs (Relation m: Relation<'A, 'B>): Set<'A * 'B> =
        m
        |> Map.filter (fun _ -> id)
        |> Seq.map (fun (KeyValue (k, _)) -> k) // Todo: could use Map.dom if top module were recursive.
        |> set

    /// Maps over a relation.
    let map (mapping: ('A * 'B -> bool -> bool)) (rel: Relation<'A, 'B>): Relation<'A, 'B> =
        let (Relation table) = rel
        Relation(Map.map mapping table)

    /// Filters a relation from a predicate.
    let filter (predicate: 'A * 'B -> bool -> bool) (rel: Relation<'A, 'B>): Relation<'A, 'B> =
        let (Relation table) = rel
        Relation(Map.filter predicate table)

    /// Mirror image of the relation.
    let flip (rel: Relation<'A, 'B>): Relation<'B, 'A> =
        rel
        |> toList
        |> List.map (fun ((a, b), p) -> ((b, a), p))
        |> ofList

    /// Gives the domain set of a relation.
    let dom (rel: Relation<'A, 'B>): Set<'A> =
        rel
        |> toList
        |> List.map (fun ((a, _), _) -> a)
        |> set

    /// Gives the codomain set of a relation.
    let cod (rel: Relation<'A, 'B>): Set<'B> = rel |> flip |> dom

    /// Gives the product domain of the relation.
    let relDom (rel: Relation<'A, 'B>): Set<'A * 'B> =
        let (Relation table) = rel

        table
        |> Seq.map (fun (KeyValue (k, _)) -> k)
        |> set // Todo: could use Map.dom if top module were recursive.

    /// Gives the transitive closure of a relation.
    let transitiveClosure (rel: Relation<'A, 'A>): Relation<'A, 'A> =
        let pairs = rel |> filter (fun _ -> id) |> relDom

        let resultTillNow result =
            Set.union
                (set [ for (z, w) in result do
                           for (w', v) in result do
                               if w = w' then (z, v) ])
                result

        let rec pairsClosure result =
            if result = resultTillNow result then result else pairsClosure (resultTillNow result)

        let resultPairs = pairsClosure pairs

        rel
        |> map (fun zz _ -> Set.contains zz resultPairs)

    /// Checks if a relation is transitively closed.
    let isTransitivelyClosed (rel: Relation<'A, 'A>): bool = transitiveClosure rel = rel

    /// Gives the transitive reduction of a relation.
    let transitiveReduction (rel: Relation<'A, 'A>): Relation<'A, 'A> =
        let pairs = rel |> filter (fun _ -> id) |> relDom

        let resultTillNow result =
            Set.difference
                result
                (set [ for (z, w) in result do
                           for (w', v) in result do
                               if w = w' && z <> w' && w' <> v then (z, v) ])

        let rec pairsReduce result =
            if result = resultTillNow result then result else pairsReduce (resultTillNow result)

        let resultPairs = pairsReduce pairs

        rel
        |> map (fun zz _ -> Set.contains zz resultPairs)

    /// Checks if a relation is transitively reduced.
    let isTransitivelyReduced (rel: Relation<'A, 'A>): bool = transitiveReduction rel = rel

    /// Gives the reflexive closure of a relation.
    let reflexiveClosure (rel: Relation<'A, 'A>): Relation<'A, 'A> =
        rel
        |> map (fun (z, z') v -> if z = z' then true else v)

    /// Checks if a relation is reflexively closed.
    let isReflexivelyClosed (rel: Relation<'A, 'A>): bool = reflexiveClosure rel = rel

    /// Gives the reflexive reduction of a relation.
    let reflexiveReduction (rel: Relation<'A, 'A>): Relation<'A, 'A> =
        rel
        |> map (fun (z, z') v -> if z = z' then false else v)

    /// Checks if a relation is reflexively reduced.
    let isReflexivelyReduced (rel: Relation<'A, 'A>): bool = reflexiveReduction rel = rel

    /// Gives the symmetric closure of a relation.
    let symmetricClosure (rel: Relation<'A, 'A>): Relation<'A, 'A> =
        rel
        |> map (fun (z, z') v ->
            if v then true
            else if rel.[z', z] then true
            else false)

    /// Checks if a relation is symmetrically closed.
    let isSymmetricallyClosed (rel: Relation<'A, 'A>): bool = symmetricClosure rel = rel

    /// Gives a symmetric reduction of a relation (not necessarily unique).
    let symmetricReduction (rel: Relation<'A, 'A>): Relation<'A, 'A> =
        rel
        |> map (fun (z, z') v -> if rel.[z', z] then false else v)

    /// Checks if a relation is symmetrically reduced.
    let isSymmetricallyReduced (rel: Relation<'A, 'A>): bool = symmetricReduction rel = rel

    /// Checks if a relation is an equivalence.
    let isEquivalence (rel: Relation<'A, 'A>): bool =
        isTransitivelyClosed rel
        && isReflexivelyClosed rel
        && isSymmetricallyClosed rel

    /// Creates the Hasse diagram of a poset.
    let hasseFromPoset (P: Relation<'A, 'A>): Set<'A * 'A> =
        P
        |> transitiveReduction
        |> reflexiveReduction
        |> filter (fun _ -> id)
        |> relDom

    /// Creates the poset of a Hasse diagram.
    let posetFromHasse (H: Set<'A * 'A>): Relation<'A, 'A> =
        H
        |> ofPairs (Set.map fst H) (Set.map fst H)
        |> reflexiveClosure
        |> transitiveClosure

    /// Creates a poset from a relation represented by a function and a set.
    let posetFromFun (f: 'A -> 'A -> bool) (X: Set<'A>): Relation<'A, 'A> =
        ofList [ for (x, x') in Set.square X do
                     ((x, x'), f x x') ]

[<RequireQualifiedAccess>]
module Map =

    /// Converts to a `Set` type.
    let toSet (x: Map<'A, 'B>): Set<'A * 'B> = x |> Map.toList |> set

    /// Gives the identity map on a set.
    let id (X: Set<'A>): Map<'A, 'A> = X |> Set.map (fun s -> (s, s)) |> Map

    /// Gives the constant map on a set to a given element of the codomain.
    let constant (X: Set<'A>) (t: 'B): Map<'A, 'B> = X |> Set.map (fun s -> (s, t)) |> Map

    /// Composes maps.
    let compose (x: Map<'B, 'C>) (y: Map<'A, 'B>): Map<'A, 'C> = y |> Map.map (fun _ t -> x.[t])

    /// Gives the domain of a map.
    let dom (x: Map<'A, 'B>): Set<'A> =
        x |> Seq.map (fun (KeyValue (k, _)) -> k) |> set

    /// Gives the image of a map.
    let image (x: Map<'A, 'B>): Set<'B> =
        x |> Seq.map (fun (KeyValue (_, v)) -> v) |> set

    /// Checks if a map is injective.
    let isInjective (x: Map<'A, 'B>): bool =
        x
        |> Seq.groupBy (fun (KeyValue (_, v)) -> v)
        |> Seq.forall (snd >> Seq.length >> ((>) 2))

    /// Checks if a map is surjective.
    let isSurjective (cod: Set<'B>) (x: Map<'A, 'B>): bool = image x = cod

    /// Checks if a map is bijective.
    let isBijective (cod: Set<'B>) (x: Map<'A, 'B>): bool = isSurjective cod x && isInjective x

    /// Binary product of maps.
    let product (x: Map<'A, 'C>) (y: Map<'B, 'D>): Map<'A * 'B, 'C * 'D> =
        let X = dom x
        let Y = dom y

        Map [ for z, w in Set.product X Y do
                  (z, w), (x.[z], y.[w]) ]

    /// Binary sum of maps.
    let sum (x: Map<'A, 'C>) (y: Map<'B, 'D>): Map<Choice<'A, 'B>, Choice<'C, 'D>> =
        let X = dom x
        let Y = dom y

        Map [ for z in Set.sum X Y do
                  match z with
                  | Choice1Of2 u -> (Choice1Of2 u, Choice1Of2 x.[u])
                  | Choice2Of2 v -> (Choice2Of2 v, Choice2Of2 y.[v]) ]

    /// Binary tuple of maps.
    /// WARNING: does not check domains match.
    let tuple (x: Map<'A, 'B>) (y: Map<'A, 'C>): Map<'A, 'B * 'C> =
        Map [ for a in dom x do
                  (a, (x.[a], y.[a])) ]

    /// Binary tuple of maps.
    let cotuple (x: Map<'B, 'A>) (y: Map<'C, 'A>): Map<Choice<'B, 'C>, 'A> =
        Map [ for bc in Set.sum (dom x) (dom y) do
                  let im =
                      match bc with
                      | Choice1Of2 b -> x.[b]
                      | Choice2Of2 c -> y.[c]

                  (bc, im) ]

    /// Equaliser of maps.
    let equaliser (x: Map<'A, 'C>) (y: Map<'A, 'C>): Set<'A> =
        dom x // = dom y
        |> Set.filter (fun s -> x.[s] = y.[s])

    /// Pullback of maps.
    let pullback (x: Map<'A, 'C>) (y: Map<'B, 'C>): Set<'A * 'B> =
        (dom x, dom y)
        ||> Set.product
        |> Set.filter (fun (z, w) -> x.[z] = y.[w])

    /// Coequaliser of maps.
    let coequaliser (x: Map<'C, 'A>) (y: Map<'C, 'A>) (X: Set<'A>): Set<Set<'A>> =
        let Z = dom x // = dom y

        let equal =
            [ for (r, r') in Set.square Z do
                let x', y' = x.[r], y.[r']
                (x', y') ]
            |> set
            |> Relation.ofPairs X X
            |> Relation.transitiveClosure
            |> Relation.symmetricClosure
            |> Relation.reflexiveClosure

        X |> Set.partitionByEquivalence equal

    /// Pushout of maps.
    let pushout (X: Set<'A>) (x: Map<'C, 'A>) (y: Map<'C, 'B>) (Y: Set<'B>): Set<Set<Choice<'A, 'B>>> =
        let Z = dom x // = dom y
        let XY = Set.sum X Y

        let equal =
            [ for (r, r') in Set.square Z do
                let x', y' = Choice1Of2 x.[r], Choice2Of2 y.[r']
                (x', y') ]
            |> set
            |> Relation.ofPairs XY XY
            |> Relation.transitiveClosure
            |> Relation.symmetricClosure
            |> Relation.reflexiveClosure

        XY |> Set.partitionByEquivalence equal

    /// Restricts a map to a subdomain.
    let restrict (X: Set<'A>) (x: Map<'A, 'B>): Map<'A, 'B> =
        Map.filter (fun z _ -> Set.contains z X) x

    /// Gives the union of the maps on a common domain. Note that the result may fail to be a function.
    let union (x: Map<'A, 'B>) (y: Map<'A, 'B>): Map<'A, 'B> = (toSet x, toSet y) ||> Set.union |> Map

    /// Gives the intersection of the maps on a common domain.
    let intersect (x: Map<'A, 'B>) (y: Map<'A, 'B>): Map<'A, 'B> =
        (toSet x, toSet y) ||> Set.intersect |> Map

    /// Checks if a map is submap of another.
    let isSubmap (x: Map<'A, 'B>) (y: Map<'A, 'B>): bool = (toSet x, toSet y) ||> Set.isSubset

    /// Maps functions over the keys and values of a map.
    let doubleMap (f: 'A -> 'C) (g: 'B -> 'D) (x: Map<'A, 'B>): Map<'C, 'D> =
        x
        |> Seq.map (fun (KeyValue (k, v)) -> (f k, g v))
        |> Map

    /// Exponential of sets, i.e. set of functions X -> Y.
    let exp (X: Set<'A>) (Y: Set<'B>): Set<Map<'A, 'B>> =
        if X = Set.empty then
            set [ Map.empty ]
        else
            let xs = Set.toList X
            let ys = Set.toList Y

            ys
            |> List.replicate (Set.count X)
            |> List.listProduct
            |> List.map (List.zip xs >> Map)
            |> set

    /// Set of bijections X -> Y.
    let iso (X: Set<'A>) (Y: Set<'B>): Set<Map<'A, 'B>> =
        if Set.count X <> Set.count Y then
            set []
        else
            Y
            |> Set.toList
            |> List.permutations
            |> List.map (List.zip (X |> Set.toList) >> Map)
            |> Set
