/// Test suite.
[<RequireQualifiedAccess>]
module Test

open FsCheck

module DeterministicTests =
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
                    let mapping =
                        (Map [ V, Map [ cat.Id.[V], t ]
                               E, Map.empty ])

                    Morphism.make "f" hV hE mapping

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
        open Examples.RGraphs

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

module RandomTests =

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

    // Generates a pushout of representables.
    let genSimplePushout cat =
        let (gG, gH, gI) =
            cat |> genRepresentable |> Gen.three |> Gen.unzip3

        let I = gI |> sample

        let f =
            (I, gG)
            ||> genHomFixedToGen
            |> genElementFromInhabitedSet

        let g =
            (I, gH)
            ||> genHomFixedToGen
            |> genElementFromInhabitedSet

        (f, g) ||> Gen.map2 Presheaf.pushout

    // Generates a coequaliser of pushouts of binary products of representables.
    let genCoequaliser cat =
        cat
        |> genSimplePushout
        |> Gen.two
        |> Gen.unzip
        ||> Gen.map2 Morphism.hom
        |> genElementFromInhabitedSet
        |> Gen.two
        |> Gen.unzip
        ||> Gen.map2 Presheaf.coequaliser

    /// Generates a morphism between pushouts of reprsentables.
    let genHom cat =
        cat
        |> genCoequaliser
        |> Gen.two
        |> Gen.unzip
        ||> Gen.map2 Morphism.hom
        |> sampleSet

    let ``F + 0 ~= F`` cat =
        let O = Presheaf.zero cat
        let F = genCoequaliser cat |> sample
        F + O == F

    let ``F * 0 ~= 0`` cat =
        let O = Presheaf.zero cat
        let F = genCoequaliser cat |> sample
        F * O == O

    let ``F * 1 ~= 1`` cat =
        let I = Presheaf.one cat
        let F = genCoequaliser cat |> sample
        F * I == F

    let ``F + G ~= G + F`` cat =
        let F = genCoequaliser cat |> sample
        let G = genCoequaliser cat |> sample
        F + G == G + F

    let ``F * G ~= G * F`` cat =
        let F = genCoequaliser cat |> sample
        let G = genCoequaliser cat |> sample
        F * G == G * F

    let ``# hom<F * G, H> = # hom <F, G => H>`` cat = // Note we only compare cardinalities.
        let F = genCoequaliser cat |> sample
        let G = genCoequaliser cat |> sample
        let H = genCoequaliser cat |> sample
        Set.count (Morphism.hom (F * G) H) = Set.count (Morphism.hom F (H ^ G))

    let ``# sub F = # hom <F, Omega>`` cat = // Note we only compare cardinalities.
        let F = genCoequaliser cat |> sample
        let subF = Subobject.subobjects F
        let Om = Truth.omega cat
        Set.count (Morphism.hom F Om) = Set.count subF

    let ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` cat =
        let F = genCoequaliser cat |> sample
        let alg = (Subobject.algebra F)
        let (+) = Subobject.join
        let (*) = Subobject.meet
        let d = Subobject.boundary alg
        let eq (X, Y) = d (X * Y) = (d X * Y) + (X * d Y)
        alg.Subobjects |> Set.square |> Set.forall eq

    let ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` cat =
        let F = genCoequaliser cat |> sample
        let alg = (Subobject.algebra F)
        let (+) = Subobject.join
        let (*) = Subobject.meet
        let d = Subobject.boundary alg
        let eq (X, Y) = d (X + Y) + d (X * Y) = d X + d Y
        alg.Subobjects |> Set.square |> Set.forall eq

    let ``omega-axiom isomorphism`` cat =
        let F = genCoequaliser cat |> sample
        let alg = (Subobject.algebra F)
        let chi = Truth.subobjectToChar alg.Top
        let psi = Truth.charToSubobject
        let Om = Truth.omega cat

        (alg.Subobjects
         |> Set.forall (fun S -> S |> chi |> psi = S))
        && (Morphism.hom alg.Top Om
            |> Set.forall (fun n -> n |> psi |> chi = n))

    let ``exists-preimage-forall adjunction`` cat =
        let f = genHom cat
        let pi = Subobject.preimage f
        let ex = Subobject.exists f
        let fa = Subobject.forall f
        let algF = Subobject.algebra f.Dom
        let algG = Subobject.algebra f.Cod
        let subG = algF.Subobjects
        let subH = algG.Subobjects

        let adjunction1 (S, T) =
            algG.LessEq.[ex.[S], T]
            <=> algF.LessEq.[S, pi.[T]]

        let adjunction2 (S, T) =
            algG.LessEq.[T, fa.[S]]
            <=> algF.LessEq.[pi.[T], S]

        (subG, subH)
        ||> Set.product
        |> Set.forall (fun ST -> adjunction1 ST && adjunction2 ST)

    let ``double negation morphism is topology`` cat =
        let neg = Truth.internalNot cat

        (neg, neg)
        ||> Morphism.compose
        |> Topology.isTopology

    // todo: pullback of monic is monic
    // todo: pasting lemma

    module Sets =
        open Examples.Sets

        type Sets =
            static member ``(Sets) F + 0 ~= F`` = ``F + 0 ~= F`` cat
            static member ``(Sets) F * 0 ~= 0`` = ``F * 0 ~= 0`` cat
            static member ``(Sets) F * 1 ~= 1`` = ``F * 1 ~= 1`` cat
            static member ``(Sets) F + G ~= G + F`` = ``F + G ~= G + F`` cat
            static member ``(Sets) F * G ~= G * F`` = ``F * G ~= G * F`` cat

            static member ``(Sets) # hom<F * G, H> = # hom <F, G => H>`` =
                ``# hom<F * G, H> = # hom <F, G => H>`` cat

            static member ``(Sets) # sub F = # hom <F, Omega>`` = ``# sub F = # hom <F, Omega>`` cat

            static member ``(Sets) d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` =
                ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` cat

            static member ``(Sets) d(x \/ y) \/ d(x /\ y) = dx \/ dy`` =
                ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` cat

            static member ``(Sets) omega-axiom isomorphism`` = ``omega-axiom isomorphism`` cat

            static member ``(Sets) exists-preimage-forall adjunction`` =
                ``exists-preimage-forall adjunction`` cat

            static member ``(Sets) double negation morphism is topology`` =
                ``double negation morphism is topology`` cat

    module Bisets =
        open Examples.Bisets

        type Bisets =
            static member ``(Bisets) F + 0 ~= F`` = ``F + 0 ~= F`` cat
            static member ``(Bisets) F * 0 ~= 0`` = ``F * 0 ~= 0`` cat
            static member ``(Bisets) F * 1 ~= 1`` = ``F * 1 ~= 1`` cat
            static member ``(Bisets) F + G ~= G + F`` = ``F + G ~= G + F`` cat
            static member ``(Bisets) F * G ~= G * F`` = ``F * G ~= G * F`` cat

            static member ``(Bisets) # hom<F * G, H> = # hom <F, G => H>`` =
                ``# hom<F * G, H> = # hom <F, G => H>`` cat

            static member ``(Bisets) # sub F = # hom <F, Omega>`` = ``# sub F = # hom <F, Omega>`` cat

            static member ``(Bisets) d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` =
                ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` cat

            static member ``(Bisets) d(x \/ y) \/ d(x /\ y) = dx \/ dy`` =
                ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` cat

            static member ``(Bisets) omega-axiom isomorphism`` = ``omega-axiom isomorphism`` cat

            static member ``(Bisets) exists-preimage-forall adjunction`` =
                ``exists-preimage-forall adjunction`` cat

            static member ``(Bisets) double negation morphism is topology`` =
                ``double negation morphism is topology`` cat

    module Bouquets =
        open Examples.Bouquets

        type Bouquets =
            static member ``(Bouquets) F + 0 ~= F`` = ``F + 0 ~= F`` cat
            static member ``(Bouquets) F * 0 ~= 0`` = ``F * 0 ~= 0`` cat
            static member ``(Bouquets) F * 1 ~= 1`` = ``F * 1 ~= 1`` cat
            static member ``(Bouquets) F + G ~= G + F`` = ``F + G ~= G + F`` cat
            static member ``(Bouquets) F * G ~= G * F`` = ``F * G ~= G * F`` cat

            static member ``(Bouquets) # hom<F * G, H> = # hom <F, G => H>`` =
                ``# hom<F * G, H> = # hom <F, G => H>`` cat

            static member ``(Bouquets) # sub F = # hom <F, Omega>`` = ``# sub F = # hom <F, Omega>`` cat

            static member ``(Bouquets) d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` =
                ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` cat

            static member ``(Bouquets) d(x \/ y) \/ d(x /\ y) = dx \/ dy`` =
                ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` cat

            static member ``(Bouquets) omega-axiom isomorphism`` = ``omega-axiom isomorphism`` cat

            static member ``(Bouquets) exists-preimage-forall adjunction`` =
                ``exists-preimage-forall adjunction`` cat

            static member ``(Bouquets) double negation morphism is topology`` =
                ``double negation morphism is topology`` cat

    module Graphs =
        open Examples.Graphs

        type Graphs =
            static member ``(Graphs) F + 0 ~= F`` = ``F + 0 ~= F`` cat
            static member ``(Graphs) F * 0 ~= 0`` = ``F * 0 ~= 0`` cat
            static member ``(Graphs) F * 1 ~= 1`` = ``F * 1 ~= 1`` cat
            static member ``(Graphs) F + G ~= G + F`` = ``F + G ~= G + F`` cat
            static member ``(Graphs) F * G ~= G * F`` = ``F * G ~= G * F`` cat

            static member ``(Graphs) # hom<F * G, H> = # hom <F, G => H>`` =
                ``# hom<F * G, H> = # hom <F, G => H>`` cat

            static member ``(Graphs) # sub F = # hom <F, Omega>`` = ``# sub F = # hom <F, Omega>`` cat

            static member ``(Graphs) d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` =
                ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` cat

            static member ``(Graphs) d(x \/ y) \/ d(x /\ y) = dx \/ dy`` =
                ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` cat

            static member ``omega-axiom isomorphism`` = ``omega-axiom isomorphism`` cat

            static member ``(Graphs) exists-preimage-forall adjunction`` =
                ``exists-preimage-forall adjunction`` cat

            static member ``(Graphs) double negation morphism is topology`` =
                ``double negation morphism is topology`` cat

    module RGraphs =
        open Examples.RGraphs

        type RGraphs =
            static member ``(RGraphs) F + 0 ~= F`` = ``F + 0 ~= F`` cat
            static member ``(RGraphs) F * 0 ~= 0`` = ``F * 0 ~= 0`` cat
            static member ``(RGraphs) F * 1 ~= 1`` = ``F * 1 ~= 1`` cat
            static member ``(RGraphs) F + G ~= G + F`` = ``F + G ~= G + F`` cat
            static member ``(RGraphs) F * G ~= G * F`` = ``F * G ~= G * F`` cat

            static member ``(RGraphs) # hom<F * G, H> = # hom <F, G => H>`` =
                ``# hom<F * G, H> = # hom <F, G => H>`` cat

            static member ``(RGraphs) # sub F = # hom <F, Omega>`` = ``# sub F = # hom <F, Omega>`` cat

            static member ``(RGraphs) d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` =
                ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` cat

            static member ``(RGraphs) d(x \/ y) \/ d(x /\ y) = dx \/ dy`` =
                ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` cat

            static member ``(RGraphs) omega-axiom isomorphism`` = ``omega-axiom isomorphism`` cat

            static member ``(RGraphs) exists-preimage-forall adjunction`` =
                ``exists-preimage-forall adjunction`` cat

            static member ``(RGraphs) double negation morphism is topology`` =
                ``double negation morphism is topology`` cat

    module TruncESets =
        open Examples.TruncESets

        type TruncESets =
            static member ``(TruncESets) F + 0 ~= F`` = ``F + 0 ~= F`` cat
            static member ``(TruncESets) F * 0 ~= 0`` = ``F * 0 ~= 0`` cat
            static member ``(TruncESets) F * 1 ~= 1`` = ``F * 1 ~= 1`` cat
            static member ``(TruncESets) F + G ~= G + F`` = ``F + G ~= G + F`` cat
            static member ``(TruncESets) F * G ~= G * F`` = ``F * G ~= G * F`` cat

            static member ``(TruncESets) # hom<F * G, H> = # hom <F, G => H>`` =
                ``# hom<F * G, H> = # hom <F, G => H>`` cat

            static member ``(TruncESets) # sub F = # hom <F, Omega>`` = ``# sub F = # hom <F, Omega>`` cat

            static member ``(TruncESets) d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` =
                ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` cat

            static member ``(TruncESets) d(x \/ y) \/ d(x /\ y) = dx \/ dy`` =
                ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` cat

            static member ``(TruncESets) omega-axiom isomorphism`` = ``omega-axiom isomorphism`` cat

            static member ``(TruncESets) exists-preimage-forall adjunction`` =
                ``exists-preimage-forall adjunction`` cat

            static member ``(TruncESets) double negation morphism is topology`` =
                ``double negation morphism is topology`` cat

let testDeterministic () =
    let config = { Config.Default with MaxTest = 1 }
    Check.All<DeterministicTests.Bisets.Bisets>(config)
    Check.All<DeterministicTests.Bouquets.Bouquets>(config)
    Check.All<DeterministicTests.Graphs.Graphs>(config)
    Check.All<DeterministicTests.RGraphs.RGraphs>(config)

let testRandom () =
    let config = { Config.Default with MaxTest = 100 }
    Check.All<RandomTests.Sets.Sets>(config)
    Check.All<RandomTests.Bisets.Bisets>(config)
    Check.All<RandomTests.Bouquets.Bouquets>(config)
    Check.All<RandomTests.Graphs.Graphs>(config)
    Check.All<RandomTests.RGraphs.RGraphs>(config) // todo: These examples are currently too complex to test.
    Check.All<RandomTests.TruncESets.TruncESets>(config) //
