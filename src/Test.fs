/// Test suite.
[<RequireQualifiedAccess>]
module Test

open FsCheck

module Support =
    type Support =
        static member ``relational closures and reductions``(ps: Set<int * int>) =

            let dom = ps |> Set.map fst |> set
            let cod = ps |> Set.map snd |> set
            let X = Set.union dom cod
            let rel = Relation.ofPairs X X ps

            let equivClose =
                Relation.equivalenceClosure
                >> Relation.isEquivalence

            let symClose =
                Relation.symmetricClosure
                >> Relation.isSymmetricallyClosed

            let transClose =
                Relation.transitiveClosure
                >> Relation.isTransitivelyClosed

            let refClose =
                Relation.reflexiveClosure
                >> Relation.isReflexivelyClosed

            let symReduce =
                Relation.symmetricReduction
                >> Relation.isSymmetricallyReduced

            let transReduce =
                Relation.transitiveReduction
                >> Relation.isTransitivelyReduced

            let refReduce =
                Relation.reflexiveReduction
                >> Relation.isReflexivelyReduced

            equivClose rel
            && symClose rel
            && transClose rel
            && refClose rel
            && symReduce rel
            && transReduce rel
            && refReduce rel

module Deterministic =
    module Bisets =
        open Examples.Bisets

        type Bisets =
            // Reyes p47
            static member ``(2hP + 3hS) * (hP + 2hS) = 2hP + 6hS`` =
                let lhs =
                    ((hP + hP) + (hS + hS + hS)) * (hP + (hS + hS))

                let rhs =
                    (hP + hP) + (hS + hS + hS + hS + hS + hS)

                lhs == rhs

    module Bouquets =
        open Examples.Bouquets

        type Bouquets =
            // Reyes p60--62
            static member ``hV ^ hV ~= hL`` = hV ^ hV == hL
            static member ``hV ^ hL ~= hV`` = hV ^ hL == hV
            static member ``hL ^ hV ~= hL`` = hL ^ hV == hL
            static member ``hL ^ hL ~= hL`` = hL ^ hL == hL

            static member ``2hV ^ 2hV ~= 4hL`` =
                (hV + hV) ^ (hV + hV) == hL + hL + hL + hL

            // Reyes p41
            static member ``equaliser of double loops endomaps`` =
                let yo = Yoneda.yo cat
                let hV = yo.Object V
                let hL = yo.Object L
                let f = Morphism.hom hV hL |> Seq.exactlyOne
                let doubleLoop = Presheaf.pushout f f
                let endomorphisms = Morphism.hom doubleLoop doubleLoop
                let g = endomorphisms |> Seq.item 0 // Careful to get the right ones!
                let h = endomorphisms |> Seq.item 3 //
                let K = Presheaf.equaliser g h
                K == hV

            // Reyes p47
            static member ``gluing two loops at their point by coequaliser`` =
                let F = hL + hL
                let maps = Morphism.hom hV F
                let f = maps |> Seq.item 0
                let g = maps |> Seq.item 1
                let K = Presheaf.coequaliser f g

                let J =
                    let ob =
                        Map [ (V, set [ 1 ])
                              (L, set [ 1; 2 ]) ]

                    let ar = Map [ (v, Map [ (1, 1); (2, 1) ]) ]
                    Presheaf.make "J" cat ob ar

                J == K

    module Graphs =
        open Examples.Graphs

        type Graphs =

            // Reyes p39
            static member ``hV + hV ~= hV * hE`` = hV + hV == hV * hE

            // Reyes p40
            static member ``hE * hE ~= 2hV + hE`` = hE * hE == hE + (hV + hV)

            // Reyes p51
            static member ``gluing a loop to the tip of an arrow by pushout`` =
                let G =
                    let ob = Map [ (V, set [ () ]); (E, set [ () ]) ]

                    let ar =
                        Map [ (s, Map [ ((), ()) ])
                              (t, Map [ ((), ()) ]) ]

                    Presheaf.make "G" cat ob ar

                let m = Morphism.hom hV G |> Seq.exactlyOne

                let f =
                    let map =
                        (Map [ V, Map [ cat.Id.[V], t ]
                               E, Map.empty ])

                    Morphism.make "f" hV hE map

                let K = Presheaf.pushout f m

                let J =
                    let ob =
                        Map [ (V, set [ 1; 2 ])
                              (E, set [ 1; 2 ]) ]

                    let ar =
                        Map [ (s, Map [ (1, 2); (2, 1) ])
                              (t, Map [ (1, 2); (2, 2) ]) ]

                    Presheaf.make "J" cat ob ar

                J == K

            // Reyes p88
            static member Omega_Graphs =
                let F =
                    let ob =
                        Map [ V, set [ "L_V"; "T_V" ]
                              E,
                              set [ "L_A"
                                    "T_/s"
                                    "T_/t"
                                    "t_A"
                                    "T_A" ] ]

                    let nontrivAr =
                        Map [ s,
                              Map [ "L_A", "L_V"
                                    "T_/s", "T_V"
                                    "T_/t", "L_V"
                                    "t_A", "T_V"
                                    "T_A", "T_V" ]
                              t,
                              Map [ "L_A", "L_V"
                                    "T_/s", "L_V"
                                    "T_/t", "T_V"
                                    "t_A", "T_V"
                                    "T_A", "T_V" ] ]

                    Presheaf.make "F" cat ob nontrivAr

                F == Truth.omega cat

    module RGraphs =
        open Examples.ReflexiveGraphs

        type RGraphs =

            // Reyes p88
            static member Omega_RGraphs =
                let F =
                    let ob =
                        Map [ V, set [ "L_V"; "T_V" ]
                              E,
                              set [ "L_A"
                                    "T_/s"
                                    "T_/t"
                                    "t_A"
                                    "T_A" ] ]

                    let nontrivAr =
                        Map [ l, Map [ "L_V", "L_A"; "T_V", "T_A" ]
                              s,
                              Map [ "L_A", "L_V"
                                    "T_/s", "T_V"
                                    "T_/t", "L_V"
                                    "t_A", "T_V"
                                    "T_A", "T_V" ]
                              t,
                              Map [ "L_A", "L_V"
                                    "T_/s", "L_V"
                                    "T_/t", "T_V"
                                    "t_A", "T_V"
                                    "T_A", "T_V" ]
                              u,
                              Map [ "L_A", "L_A"
                                    "T_/s", "T_A"
                                    "T_/t", "L_A"
                                    "t_A", "T_A"
                                    "T_A", "T_A" ]
                              v,
                              Map [ "L_A", "L_A"
                                    "T_/s", "L_A"
                                    "T_/t", "T_A"
                                    "t_A", "T_A"
                                    "T_A", "T_A" ] ]

                    Presheaf.make "F" cat ob nontrivAr

                F == Truth.omega cat

module Random =

    /// Samples from a generator.
    let sample g = g |> Gen.sample 0 1 |> Seq.exactlyOne

    /// Generates element from a generated set.
    let genElementFromInhabitedSet X =
        X
        |> Gen.filter (Set.isEmpty >> not)
        |> sample
        |> Gen.elements

    /// Samples from a generated set.
    let sampleSet X =
        X |> genElementFromInhabitedSet |> sample

    /// Generates a representable.
    let genRepresentable cat =
        let yo = Yoneda.yo cat
        let reps = cat.Objects |> Set.map yo.Object
        reps |> Gen.elements

    /// Generates a binary product of representables.
    let genProduct cat =
        cat
        |> genRepresentable
        |> Gen.two
        |> Gen.unzip
        ||> Gen.map2 (*)

    /// Generates a morphism from a presheaf to a generated presheaf.
    let genHomFixedToGen G gH =
        (Gen.constant G, gH)
        ||> Gen.map2 Morphism.hom
        |> Gen.filter (Set.isEmpty >> not)

    /// Generates a morphism from a presheaf to a generated presheaf.
    let genHomGenToFixed gG H =
        (gG, Gen.constant H)
        ||> Gen.map2 Morphism.hom
        |> Gen.filter (Set.isEmpty >> not)

    // Generates a coproduct of representables.
    let genRepCoproduct cat =
        cat
        |> genRepresentable
        |> Gen.two
        |> Gen.unzip
        ||> Gen.map2 (+)

    // Generates a pullback of coproducts of representables.
    let genPullback cat =
        let (gG, gH, gI) =
            cat |> genRepresentable |> Gen.three |> Gen.unzip3

        let I = gI |> sample

        let f =
            (gG, I)
            ||> genHomGenToFixed
            |> genElementFromInhabitedSet
            |> sample
            |> Gen.constant

        let g =
            (gH, I)
            ||> genHomGenToFixed
            |> genElementFromInhabitedSet
            |> sample
            |> Gen.constant

        let pb = (f, g) ||> Gen.map2 Presheaf.pullback
        (pb, f, g)

    // Generates a pushout of coproducts representables.
    let genPushout cat =
        let (gG, gH, gI) =
            cat |> genRepresentable |> Gen.three |> Gen.unzip3

        let I = gI |> sample

        let f =
            (I, gG)
            ||> genHomFixedToGen
            |> genElementFromInhabitedSet
            |> sample
            |> Gen.constant

        let g =
            (I, gH)
            ||> genHomFixedToGen
            |> genElementFromInhabitedSet
            |> sample
            |> Gen.constant

        let po = (f, g) ||> Gen.map2 Presheaf.pushout
        (po, f, g)

    // Generates a pushout of coproducts representables.
    let genSmallPushout cat =
        let (gG, gH, gI) =
            cat |> genRepresentable |> Gen.three |> Gen.unzip3

        let I = gI |> sample

        let f =
            (I, gG)
            ||> genHomFixedToGen
            |> genElementFromInhabitedSet
            |> sample
            |> Gen.constant

        let g =
            (I, gH)
            ||> genHomFixedToGen
            |> genElementFromInhabitedSet
            |> sample
            |> Gen.constant

        let po = (f, g) ||> Gen.map2 Presheaf.pushout
        (po, f, g)

    /// Samples a random a morphism between.
    let randomHom cat =
        cat
        |> genSmallPushout
        |> fun (G, _, _) -> G
        |> Gen.two
        |> Gen.unzip
        ||> Gen.map2 Morphism.hom
        |> sampleSet

    /// Samples a random presheaf.
    let randomPresheaf cat =
        genPushout cat
        |> fun (G, _, _) -> G |> sample |> Presheaf.simplify

    /// Samples a random small presheaf.
    let randomSmallPresheaf cat =
        genSmallPushout cat
        |> fun (G, _, _) -> G |> sample |> Presheaf.simplify

    /// Samples a random sum of representables.
    let randomSumPresheaf cat =
        genRepCoproduct cat |> sample |> Presheaf.simplify

    /// Samples a random representable.
    let randomRepPresheaf cat =
        genRepresentable cat
        |> sample
        |> Presheaf.simplify

    // Category tests: in the tests below random presheaves of various sizes are used to verify identities and facts.
    // The sizes were chosen so that the tests run in a reasonable amount of time.

    // CAUTION: Make sure tests take a unit parameter or else they will secretly only run once!.

    let ``yoneda lemma`` cat () =
        let F = randomPresheaf cat
        let A = cat.Objects |> Gen.elements |> sample
        let yo = Yoneda.yo cat
        let hA = yo.Object A

        let hom = Morphism.hom hA F

        let map =
            Map [ for f in hom do
                      (f, f.Map.[A].[cat.Id.[A]]) ]

        let cod = F.Ob.[A]
        Map.isBijective cod map // Todo: also check naturality.

    let ``F + 0 ~= F`` cat () =
        let O = Presheaf.zero cat
        let F = randomSmallPresheaf cat
        F + O == F

    let ``F * 0 ~= 0`` cat () =
        let O = Presheaf.zero cat
        let F = randomSmallPresheaf cat
        F * O == O

    let ``F * 1 ~= 1`` cat () =
        let I = Presheaf.one cat
        let F = randomSmallPresheaf cat
        F * I == F

    let ``hom<F * G, H> ~= hom <F, G => H>`` cat () =
        let F = randomRepPresheaf cat
        let G = randomRepPresheaf cat
        let H = randomRepPresheaf cat

        let expGH = H ^ G
        let homLHS = Morphism.hom (F * G) H
        let homRHS = Morphism.hom F expGH

        let map =
            Map [ for f in homRHS do
                      let im =
                          let i = Morphism.id G
                          let t = f * i
                          let e = Morphism.eval expGH G H
                          e @ t

                      (f, im) ]

        Map.isBijective homLHS map // Todo: also check naturality.

    let ``sub F ~= hom <F, Omega>`` cat () =
        let F = randomSmallPresheaf cat
        let subF = Subobject.subobjects F
        let hom = (F, Truth.omega cat) ||> Morphism.hom

        let map =
            Map [ for U in subF do
                      let f = U |> Truth.subobjectToChar F

                      (U, f) ]

        Map.isBijective hom map // Todo: also check naturality.

    let ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` cat () =
        let F = randomSmallPresheaf cat // Small.
        let alg = Subobject.algebra F
        let (+) = Subobject.join
        let (*) = Subobject.meet
        let d = Subobject.boundary alg
        let eq (U, V) = d (U * V) = (d U * V) + (U * d V)
        alg.Subobjects |> Set.square |> Set.forall eq

    let ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` cat () =
        let F = randomSmallPresheaf cat // Small.
        let alg = Subobject.algebra F
        let (+) = Subobject.join
        let (*) = Subobject.meet
        let d = Subobject.boundary alg
        let eq (U, V) = d (U + V) + d (U * V) = d U + d V
        alg.Subobjects |> Set.square |> Set.forall eq

    let ``necessity <= identity <= possibility`` cat () =
        let F = randomSmallPresheaf cat // Small.
        let alg = Subobject.algebra F

        let square = Subobject.necessity alg
        let diamond = Subobject.possibility alg

        let eq U =
            alg.LessEq.[square U, U]
            && alg.LessEq.[U, diamond U]

        alg.Subobjects |> Set.forall eq

    let ``possibility-necessity adjunction`` cat () =
        let F = randomSmallPresheaf cat // Small.
        let alg = Subobject.algebra F

        let square = Subobject.necessity alg
        let diamond = Subobject.possibility alg

        let eq (U, V) =
            alg.LessEq.[diamond U, V]
            <=> alg.LessEq.[U, square V]

        alg.Subobjects |> Set.square |> Set.forall eq

    let ``omega-axiom isomorphism`` cat () =
        let F = randomSmallPresheaf cat // Small.
        let alg = Subobject.algebra F
        let chi = Truth.subobjectToChar alg.Top
        let psi = Truth.charToSubobject
        let Om = Truth.omega cat

        (alg.Subobjects
         |> Set.forall (fun U -> U |> chi |> psi = U))
        && (Morphism.hom alg.Top Om
            |> Set.forall (fun n -> n |> psi |> chi = n))

    let ``exists-preimage-forall adjunction`` cat () =
        let f = randomHom cat
        let pre = Subobject.preimage f
        let ex = Subobject.exists f
        let fa = Subobject.forall f
        let algF = Subobject.algebra f.Dom
        let algG = Subobject.algebra f.Cod
        let subG = algF.Subobjects
        let subH = algG.Subobjects

        let adjunction1 (U, V) =
            algG.LessEq.[ex.[U], V]
            <=> algF.LessEq.[U, pre.[V]]

        let adjunction2 (U, V) =
            algG.LessEq.[V, fa.[U]]
            <=> algF.LessEq.[pre.[V], U]

        (subG, subH)
        ||> Set.product
        |> Set.forall (fun UV -> adjunction1 UV && adjunction2 UV)

    let ``frobenius identity`` cat () =
        let f = randomHom cat
        let (.*) = Subobject.meet
        let pre = Subobject.preimage f
        let ex = Subobject.exists f
        let algF = Subobject.algebra f.Dom
        let algG = Subobject.algebra f.Cod
        let subG = algF.Subobjects
        let subH = algG.Subobjects

        let eq (U, V) = ex.[pre.[V] .* U] = V .* ex.[U]

        (subG, subH) ||> Set.product |> Set.forall eq

    let ``beck-chevalley condition`` cat () =
        let (P, f, g) =
            genPullback cat
            |> fun (a, b, c) -> (sample a, sample b, sample c)

        let f' =
            let proj = Morphism.proj1 P
            let inc = Morphism.inc proj.Cod f.Dom
            inc @ proj

        let g' =
            let proj = Morphism.proj2 P
            let inc = Morphism.inc proj.Cod g.Dom
            inc @ proj

        let ex_f = Subobject.exists f
        let ex_g' = Subobject.exists g'

        let fa_f' = Subobject.forall f'
        let fa_g = Subobject.forall g

        let pre_f = Subobject.preimage f
        let pre_g = Subobject.preimage g
        let pre_f' = Subobject.preimage f'
        let pre_g' = Subobject.preimage g'

        Map.compose pre_g ex_f = Map.compose ex_g' pre_f'
        && Map.compose pre_f fa_g = Map.compose fa_f' pre_g'

    let ``double negation morphism is topology`` cat () =
        let neg = Truth.internalNot cat

        neg @ neg |> Topology.isTopology

    module Sets =

        open Examples.Sets

        type Sets =
            static member ``yoneda lemma`` = ``yoneda lemma`` cat
            static member ``F + 0 ~= F`` = ``F + 0 ~= F`` cat
            static member ``F * 0 ~= 0`` = ``F * 0 ~= 0`` cat
            static member ``F * 1 ~= 1`` = ``F * 1 ~= 1`` cat

            static member ``hom<F * G, H> ~= hom <F, G => H>`` = ``hom<F * G, H> ~= hom <F, G => H>`` cat

            static member ``sub F ~= hom <F, Omega>`` = ``sub F ~= hom <F, Omega>`` cat

            static member ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` =
                ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` cat

            static member ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` =
                ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` cat

            static member ``necessity <= identity <= possibility`` =
                ``necessity <= identity <= possibility`` cat

            static member ``possibility-necessity adjunction`` = ``possibility-necessity adjunction`` cat
            static member ``omega-axiom isomorphism`` = ``omega-axiom isomorphism`` cat

            static member ``exists-preimage-forall adjunction`` =
                ``exists-preimage-forall adjunction`` cat

            static member ``frobenius identity`` = ``frobenius identity`` cat
            static member ``beck-chevalley condition`` = ``beck-chevalley condition`` cat

            static member ``double negation morphism is topology`` =
                ``double negation morphism is topology`` cat

    module Bisets =
        open Examples.Bisets

        type Bisets =
            static member ``yoneda lemma`` = ``yoneda lemma`` cat
            static member ``F + 0 ~= F`` = ``F + 0 ~= F`` cat
            static member ``F * 0 ~= 0`` = ``F * 0 ~= 0`` cat
            static member ``F * 1 ~= 1`` = ``F * 1 ~= 1`` cat
            static member ``hom<F * G, H> ~= hom <F, G => H>`` = ``hom<F * G, H> ~= hom <F, G => H>`` cat

            static member ``sub F ~= hom <F, Omega>`` = ``sub F ~= hom <F, Omega>`` cat

            static member ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` =
                ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` cat

            static member ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` =
                ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` cat

            static member ``necessity <= identity <= possibility`` =
                ``necessity <= identity <= possibility`` cat

            static member ``possibility-necessity adjunction`` = ``possibility-necessity adjunction`` cat
            static member ``omega-axiom isomorphism`` = ``omega-axiom isomorphism`` cat

            static member ``exists-preimage-forall adjunction`` =
                ``exists-preimage-forall adjunction`` cat

            static member ``frobenius identity`` = ``frobenius identity`` cat
            static member ``beck-chevalley condition`` = ``beck-chevalley condition`` cat

            static member ``double negation morphism is topology`` =
                ``double negation morphism is topology`` cat

    module Bouquets =
        open Examples.Bouquets

        type Bouquets =
            static member ``yoneda lemma`` = ``yoneda lemma`` cat
            static member ``F + 0 ~= F`` = ``F + 0 ~= F`` cat
            static member ``F * 0 ~= 0`` = ``F * 0 ~= 0`` cat
            static member ``F * 1 ~= 1`` = ``F * 1 ~= 1`` cat

            static member ``hom<F * G, H> ~= hom <F, G => H>`` = ``hom<F * G, H> ~= hom <F, G => H>`` cat

            static member ``sub F ~= hom <F, Omega>`` = ``sub F ~= hom <F, Omega>`` cat

            static member ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` =
                ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` cat

            static member ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` =
                ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` cat

            static member ``necessity <= identity <= possibility`` =
                ``necessity <= identity <= possibility`` cat

            static member ``possibility-necessity adjunction`` = ``possibility-necessity adjunction`` cat
            static member ``omega-axiom isomorphism`` = ``omega-axiom isomorphism`` cat

            static member ``exists-preimage-forall adjunction`` =
                ``exists-preimage-forall adjunction`` cat

            static member ``frobenius identity`` = ``frobenius identity`` cat
            static member ``beck-chevalley condition`` = ``beck-chevalley condition`` cat

            static member ``double negation morphism is topology`` =
                ``double negation morphism is topology`` cat

    module Graphs =
        open Examples.Graphs

        type Graphs =
            static member ``yoneda lemma`` = ``yoneda lemma`` cat
            static member ``F + 0 ~= F`` = ``F + 0 ~= F`` cat
            static member ``F * 0 ~= 0`` = ``F * 0 ~= 0`` cat
            static member ``F * 1 ~= 1`` = ``F * 1 ~= 1`` cat

            static member ``hom<F * G, H> ~= hom <F, G => H>`` = ``hom<F * G, H> ~= hom <F, G => H>`` cat

            static member ``sub F ~= hom <F, Omega>`` = ``sub F ~= hom <F, Omega>`` cat

            static member ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` =
                ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` cat

            static member ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` =
                ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` cat

            static member ``necessity <= identity <= possibility`` =
                ``necessity <= identity <= possibility`` cat

            static member ``possibility-necessity adjunction`` = ``possibility-necessity adjunction`` cat
            static member ``omega-axiom isomorphism`` = ``omega-axiom isomorphism`` cat

            static member ``exists-preimage-forall adjunction`` =
                ``exists-preimage-forall adjunction`` cat

            static member ``frobenius identity`` = ``frobenius identity`` cat
            static member ``beck-chevalley condition`` = ``beck-chevalley condition`` cat

            static member ``double negation morphism is topology`` =
                ``double negation morphism is topology`` cat

    module ReflexiveGraphs =
        open Examples.ReflexiveGraphs

        type ReflexiveGraphs =
            static member ``yoneda lemma`` = ``yoneda lemma`` cat
            static member ``F + 0 ~= F`` = ``F + 0 ~= F`` cat
            static member ``F * 0 ~= 0`` = ``F * 0 ~= 0`` cat
            static member ``F * 1 ~= 1`` = ``F * 1 ~= 1`` cat

            static member ``hom<F * G, H> ~= hom <F, G => H>`` = ``hom<F * G, H> ~= hom <F, G => H>`` cat

            static member ``sub F ~= hom <F, Omega>`` = ``sub F ~= hom <F, Omega>`` cat

            static member ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` =
                ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` cat

            static member ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` =
                ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` cat

            static member ``necessity <= identity <= possibility`` =
                ``necessity <= identity <= possibility`` cat

            static member ``possibility-necessity adjunction`` = ``possibility-necessity adjunction`` cat
            static member ``omega-axiom isomorphism`` = ``omega-axiom isomorphism`` cat

            static member ``exists-preimage-forall adjunction`` =
                ``exists-preimage-forall adjunction`` cat

            static member ``frobenius identity`` = ``frobenius identity`` cat
            static member ``beck-chevalley condition`` = ``beck-chevalley condition`` cat

            static member ``double negation morphism is topology`` =
                ``double negation morphism is topology`` cat

    module DiamondLattice =
        open Examples.DiamondLattice

        type DiamondLattice =
            static member ``yoneda lemma`` = ``yoneda lemma`` cat
            static member ``F + 0 ~= F`` = ``F + 0 ~= F`` cat
            static member ``F * 0 ~= 0`` = ``F * 0 ~= 0`` cat
            static member ``F * 1 ~= 1`` = ``F * 1 ~= 1`` cat

            static member ``hom<F * G, H> ~= hom <F, G => H>`` = ``hom<F * G, H> ~= hom <F, G => H>`` cat

            static member ``sub F ~= hom <F, Omega>`` = ``sub F ~= hom <F, Omega>`` cat

            static member ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` =
                ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` cat

            static member ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` =
                ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` cat

            static member ``necessity <= identity <= possibility`` =
                ``necessity <= identity <= possibility`` cat

            static member ``possibility-necessity adjunction`` = ``possibility-necessity adjunction`` cat
            static member ``omega-axiom isomorphism`` = ``omega-axiom isomorphism`` cat

            static member ``exists-preimage-forall adjunction`` =
                ``exists-preimage-forall adjunction`` cat

            static member ``frobenius identity`` = ``frobenius identity`` cat
            static member ``beck-chevalley condition`` = ``beck-chevalley condition`` cat

            static member ``double negation morphism is topology`` =
                ``double negation morphism is topology`` cat

    module CyclicGroup3 =
        open Examples.DiamondLattice

        type CyclicGroup3 =
            static member ``yoneda lemma`` = ``yoneda lemma`` cat
            static member ``F + 0 ~= F`` = ``F + 0 ~= F`` cat
            static member ``F * 0 ~= 0`` = ``F * 0 ~= 0`` cat
            static member ``F * 1 ~= 1`` = ``F * 1 ~= 1`` cat

            static member ``hom<F * G, H> ~= hom <F, G => H>`` = ``hom<F * G, H> ~= hom <F, G => H>`` cat

            static member ``sub F ~= hom <F, Omega>`` = ``sub F ~= hom <F, Omega>`` cat

            static member ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` =
                ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` cat

            static member ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` =
                ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` cat

            static member ``necessity <= identity <= possibility`` =
                ``necessity <= identity <= possibility`` cat

            static member ``possibility-necessity adjunction`` = ``possibility-necessity adjunction`` cat
            static member ``omega-axiom isomorphism`` = ``omega-axiom isomorphism`` cat

            static member ``exists-preimage-forall adjunction`` =
                ``exists-preimage-forall adjunction`` cat

            static member ``frobenius identity`` = ``frobenius identity`` cat
            static member ``beck-chevalley condition`` = ``beck-chevalley condition`` cat

            static member ``double negation morphism is topology`` =
                ``double negation morphism is topology`` cat

    module MonoidTrans2 =
        open Examples.MonoidTrans2

        type MonoidTrans2 =
            static member ``yoneda lemma`` = ``yoneda lemma`` cat
            static member ``F + 0 ~= F`` = ``F + 0 ~= F`` cat
            static member ``F * 0 ~= 0`` = ``F * 0 ~= 0`` cat
            static member ``F * 1 ~= 1`` = ``F * 1 ~= 1`` cat

            static member ``hom<F * G, H> ~= hom <F, G => H>`` = ``hom<F * G, H> ~= hom <F, G => H>`` cat

            static member ``sub F ~= hom <F, Omega>`` = ``sub F ~= hom <F, Omega>`` cat

            static member ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` =
                ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` cat

            static member ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` =
                ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` cat

            static member ``necessity <= identity <= possibility`` =
                ``necessity <= identity <= possibility`` cat

            static member ``possibility-necessity adjunction`` = ``possibility-necessity adjunction`` cat
            static member ``omega-axiom isomorphism`` = ``omega-axiom isomorphism`` cat

            static member ``exists-preimage-forall adjunction`` =
                ``exists-preimage-forall adjunction`` cat

            static member ``frobenius identity`` = ``frobenius identity`` cat
            static member ``beck-chevalley condition`` = ``beck-chevalley condition`` cat

            static member ``double negation morphism is topology`` =
                ``double negation morphism is topology`` cat

let support () = Check.QuickAll<Support.Support>()

let deterministic () =
    let config = { Config.Default with MaxTest = 1 }
    Check.All<Deterministic.Bisets.Bisets>(config)
    Check.All<Deterministic.Bouquets.Bouquets>(config)
    Check.All<Deterministic.Graphs.Graphs>(config)
    Check.All<Deterministic.RGraphs.RGraphs>(config)

let random () =
    let config = { Config.Default with MaxTest = 50 }
    Check.All<Random.Sets.Sets>(config)
    Check.All<Random.Bisets.Bisets>(config)
    Check.All<Random.Bouquets.Bouquets>(config)
    Check.All<Random.Graphs.Graphs>(config)
    Check.All<Random.ReflexiveGraphs.ReflexiveGraphs>(config)
    Check.All<Random.DiamondLattice.DiamondLattice>(config)
    Check.All<Random.CyclicGroup3.CyclicGroup3>(config)
    Check.All<Random.MonoidTrans2.MonoidTrans2>(config)
