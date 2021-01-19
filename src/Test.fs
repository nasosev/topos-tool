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

                Presheaf.isIso lhs rhs

    module Bouquets =
        open Examples.Bouquets

        type Bouquets =
            // Reyes p60--62
            static member ``hV ^ hV = hL`` = Presheaf.isIso (hV ^ hV) hL
            static member ``hV ^ hL = hV`` = Presheaf.isIso (hV ^ hL) hV
            static member ``hL ^ hV = hL`` = Presheaf.isIso (hL ^ hV) hL
            static member ``hL ^ hL = hL`` = Presheaf.isIso (hL ^ hL) hL

            static member ``2hV ^ 2hV = 4hL`` =
                Presheaf.isIso ((hV + hV) ^ (hV + hV)) (hL + hL + hL + hL)

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
                Presheaf.isIso K hV

            // Reyes p47
            static member ``gluing two loops at their point by coequaliser`` =
                let F = Presheaf.sum hL hL
                let maps = Morphism.hom hV F
                let f = maps |> Seq.item 0
                let g = maps |> Seq.item 1
                let K = Presheaf.coequaliser f g

                let J =
                    let ob =
                        map [ (V, set [ 1 ])
                              (L, set [ 1; 2 ]) ]

                    let ar = map [ (v, map [ (1, 1); (2, 1) ]) ]
                    Presheaf.make "J" cat ob ar

                Presheaf.isIso J K

    module Graphs =
        open Examples.Graphs

        type Graphs =

            // Reyes p39
            static member ``hV + hV = hV * hE`` = Presheaf.isIso (hV + hV) (hV * hE)

            // Reyes p40
            static member ``hE * hE = 2hV + hE`` =
                Presheaf.isIso (hE * hE) (hE + (hV + hV))

            // Reyes p51
            static member ``gluing a loop to the tip of an arrow by pushout`` =
                let G =
                    let ob = map [ (V, set [ () ]); (E, set [ () ]) ]

                    let ar =
                        map [ (s, map [ ((), ()) ])
                              (t, map [ ((), ()) ]) ]

                    Presheaf.make "G" cat ob ar

                let m = Morphism.hom hV G |> Seq.exactlyOne

                let f =
                    let mapping =
                        (map [ V, map [ cat.Id.[V], t ]
                               E, Map.empty ])

                    Morphism.make "f" hV hE mapping

                let K = Presheaf.pushout f m

                let J =
                    let ob =
                        map [ (V, set [ 1; 2 ])
                              (E, set [ 1; 2 ]) ]

                    let ar =
                        map [ (s, map [ (1, 2); (2, 1) ])
                              (t, map [ (1, 2); (2, 2) ]) ]

                    Presheaf.make "J" cat ob ar

                Presheaf.isIso J K

            // Reyes p88
            static member Omega_Graphs =
                let F =
                    let ob =
                        map [ V, set [ "L_V"; "T_V" ]
                              E,
                              set [ "L_A"
                                    "T_/s"
                                    "T_/t"
                                    "t_A"
                                    "T_A" ] ]

                    let nontrivAr =
                        map [ s,
                              map [ "L_A", "L_V"
                                    "T_/s", "T_V"
                                    "T_/t", "L_V"
                                    "t_A", "T_V"
                                    "T_A", "T_V" ]
                              t,
                              map [ "L_A", "L_V"
                                    "T_/s", "L_V"
                                    "T_/t", "T_V"
                                    "t_A", "T_V"
                                    "T_A", "T_V" ] ]

                    Presheaf.make "F" cat ob nontrivAr

                Presheaf.isIso F (Truth.omega cat)

    module RGraphs =
        open Examples.RGraphs

        type RGraphs =

            // Reyes p88
            static member Omega_RGraphs =
                let F =
                    let ob =
                        map [ V, set [ "L_V"; "T_V" ]
                              E,
                              set [ "L_A"
                                    "T_/s"
                                    "T_/t"
                                    "t_A"
                                    "T_A" ] ]

                    let nontrivAr =
                        map [ l, map [ "L_V", "L_A"; "T_V", "T_A" ]
                              s,
                              map [ "L_A", "L_V"
                                    "T_/s", "T_V"
                                    "T_/t", "L_V"
                                    "t_A", "T_V"
                                    "T_A", "T_V" ]
                              t,
                              map [ "L_A", "L_V"
                                    "T_/s", "L_V"
                                    "T_/t", "T_V"
                                    "t_A", "T_V"
                                    "T_A", "T_V" ]
                              u,
                              map [ "L_A", "L_A"
                                    "T_/s", "T_A"
                                    "T_/t", "L_A"
                                    "t_A", "T_A"
                                    "T_A", "T_A" ]
                              v,
                              map [ "L_A", "L_A"
                                    "T_/s", "L_A"
                                    "T_/t", "T_A"
                                    "t_A", "T_A"
                                    "T_A", "T_A" ] ]

                    Presheaf.make "F" cat ob nontrivAr

                Presheaf.isIso F (Truth.omega cat)

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
        ||> Gen.map2 Presheaf.product

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

    // Generates a pushout of products of representables.
    let genComplexPushout cat =
        let (gG, gH, gI) =
            cat |> genProduct |> Gen.three |> Gen.unzip3

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

    // Generates a coequaliser of pushouts of representables..
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
        let F = genComplexPushout cat |> sample
        Presheaf.isIso (Presheaf.sum F O) F

    let ``F * 0 ~= 0`` cat =
        let O = Presheaf.zero cat
        let F = genComplexPushout cat |> sample
        Presheaf.isIso (Presheaf.product F O) O

    let ``F * 1 ~= 1`` cat =
        let I = Presheaf.one cat
        let F = genComplexPushout cat |> sample
        Presheaf.isIso (Presheaf.product F I) F

    let ``F + G ~= G + F`` cat =
        let F = genCoequaliser cat |> sample
        let G = genCoequaliser cat |> sample
        Presheaf.isIso (Presheaf.sum F G) (Presheaf.sum G F)

    let ``F * G ~= G * F`` cat =
        let F = genCoequaliser cat |> sample
        let G = genCoequaliser cat |> sample
        Presheaf.isIso (Presheaf.product F G) (Presheaf.product G F)

    let ``# hom<F * G, H> = # hom <F, G => H>`` cat = // Note we only compare cardinalities.
        let F = genCoequaliser cat |> sample
        let G = genCoequaliser cat |> sample
        let H = genCoequaliser cat |> sample
        Set.count (Morphism.hom (Presheaf.product F G) H) = Set.count (Morphism.hom F (Presheaf.exp cat G H))

    let ``# sub F = # hom <F, Omega>`` cat = // Note we only compare cardinalities.
        let F = genCoequaliser cat |> sample
        let subF = Subobject.subobjects cat F
        let Om = Truth.omega cat
        Set.count (Morphism.hom F Om) = Set.count subF

    let ``d(x /\ y) = (dx /\ y) \/ (x /\ dy)`` cat =
        let F = genCoequaliser cat |> sample
        let subalg = (Subobject.subalgebra cat F)
        let (+) = Subobject.join
        let (*) = Subobject.meet
        let d = Subobject.boundary subalg
        let eq (X, Y) = d (X * Y) = (d X * Y) + (X * d Y)
        subalg.Subobjects |> Set.square |> Set.forall eq

    let ``d(x \/ y) \/ d(x /\ y) = dx \/ dy`` cat =
        let F = genCoequaliser cat |> sample
        let subalg = (Subobject.subalgebra cat F)
        let (+) = Subobject.join
        let (*) = Subobject.meet
        let d = Subobject.boundary subalg
        let eq (X, Y) = d (X + Y) + d (X * Y) = d X + d Y
        subalg.Subobjects |> Set.square |> Set.forall eq

    let ``omega-axiom isomorphism`` cat =
        let F = genCoequaliser cat |> sample
        let subalg = (Subobject.subalgebra cat F)
        let phi = Truth.subobjectToChar cat subalg
        let psi = Truth.charToSubobject cat
        let Om = Truth.omega cat

        (subalg.Subobjects
         |> Set.forall (fun S -> S |> phi |> psi = S))
        && (Morphism.hom subalg.Top Om
            |> Set.forall (fun n -> n |> psi |> phi = n))

    let ``exists-preimage-forall adjunction`` cat =
        let f = genHom cat
        let pi = Subobject.preimage cat f
        let ex = Subobject.exists cat f
        let fa = Subobject.forall cat f
        let subalgF = Subobject.subalgebra cat f.Dom
        let subalgG = Subobject.subalgebra cat f.Cod
        let subG = subalgF.Subobjects
        let subH = subalgG.Subobjects

        let adjunction1 (S, T) =
            subalgG.LessEq.[ex.[S], T]
            <=> subalgF.LessEq.[S, pi.[T]]

        let adjunction2 (S, T) =
            subalgG.LessEq.[T, fa.[S]]
            <=> subalgF.LessEq.[pi.[T], S]

        (subG, subH)
        ||> Set.product
        |> Set.forall (fun ST -> adjunction1 ST && adjunction2 ST)

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

let testDeterministic () =
    let config = { Config.Default with MaxTest = 1 }
    Check.All<DeterministicTests.Bisets.Bisets>(config)
    Check.All<DeterministicTests.Bouquets.Bouquets>(config)
    Check.All<DeterministicTests.Graphs.Graphs>(config)
    Check.All<DeterministicTests.RGraphs.RGraphs>(config)

let testRandom () =
    let config = { Config.Default with MaxTest = 10 }
    Check.All<RandomTests.Sets.Sets>(config)
    Check.All<RandomTests.Bisets.Bisets>(config)
    Check.All<RandomTests.Bouquets.Bouquets>(config)
    Check.All<RandomTests.Graphs.Graphs>(config)
    Check.All<RandomTests.RGraphs.RGraphs>(config) // These examples are currently too complex to test.
    Check.All<RandomTests.TruncESets.TruncESets>(config) //
