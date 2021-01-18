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
    // todo: pullback of monic is monic
    // todo: pasting lemma

    // Samples an element from the input sequence.
    let sampleOne g =
        g
        |> Gen.elements
        |> Gen.sample 0 1
        |> Seq.exactlyOne

    // Samples a pair from the input sequence.
    let sampleTwo g =
        g
        |> Gen.elements
        |> Gen.two
        |> Gen.sample 0 1
        |> Seq.exactlyOne

    // Generates an arbitrary representable.
    let makeArbRep cat =
        let yo = Yoneda.yo cat
        let reps = cat.Objects |> Set.map yo.Object
        reps |> sampleOne

    // Tries to generate a random pushout of three representables.
    let tryMakeArbPushout cat =
        let F = makeArbRep cat
        let G = makeArbRep cat
        let H = makeArbRep cat
        let ns = Morphism.hom H F
        let ms = Morphism.hom H G

        if not (Set.isEmpty ns || Set.isEmpty ms) then
            let n = ns |> sampleOne
            let m = ms |> sampleOne
            Presheaf.pushout n m |> Some
        else
            None

    let ``F + 0 ~= F`` cat =
        let oG = tryMakeArbPushout cat
        let O = Presheaf.zero cat

        match oG with
        | Some G -> Presheaf.isIso (Presheaf.sum G O) G
        | _ ->
            printfn "(a test passed vacuously)"
            true

    let ``F * 0 ~= 0`` cat =
        let oG = tryMakeArbPushout cat
        let O = Presheaf.zero cat

        match oG with
        | Some G -> Presheaf.isIso (Presheaf.product G O) O
        | _ ->
            printfn "(a test passed vacuously)"
            true

    let ``F * 1 ~= 1`` cat =
        let oG = tryMakeArbPushout cat
        let I = Presheaf.one cat

        match oG with
        | Some G -> Presheaf.isIso (Presheaf.product G I) G
        | _ ->
            printfn "(a test passed vacuously)"
            true

    let ``F + G ~= G + F`` cat =
        let oG = tryMakeArbPushout cat
        let oH = tryMakeArbPushout cat

        match (oG, oH) with
        | (Some G, Some H) -> Presheaf.isIso (Presheaf.sum G H) (Presheaf.sum H G)
        | _ ->
            printfn "(a test passed vacuously)"
            true

    let ``F * G ~= G * F`` cat =
        let oG = tryMakeArbPushout cat
        let oH = tryMakeArbPushout cat

        match (oG, oH) with
        | (Some G, Some H) -> Presheaf.isIso (Presheaf.product G H) (Presheaf.product H G)
        | _ ->
            printfn "(a test passed vacuously)"
            true

    let ``# hom<F * G, H> = # hom <F, G => H>`` cat = // Note we only test the set cardinalities.
        let oG = tryMakeArbPushout cat
        let oH = tryMakeArbPushout cat
        let oJ = tryMakeArbPushout cat

        match (oG, oH, oJ) with
        | (Some G, Some H, Some J) ->
            Set.count (Morphism.hom (Presheaf.product G H) J) = Set.count (Morphism.hom G (Presheaf.exp cat H J))
        | _ ->
            printfn "(a test passed vacuously)"
            true

    let ``# sub F = # hom <F, Omega>`` cat = // Note we only test the cardinalities.
        let oG = tryMakeArbPushout cat

        match oG with
        | Some G ->
            let subF = Subobject.subobjects cat G
            let omega = Truth.omega cat
            Set.count (Morphism.hom G omega) = Set.count subF
        | _ ->
            printfn "(a test passed vacuously)"
            true

    let ``∂(x ∧ y) = (∂x ∧ y) ∨ (x ∧ ∂y)`` cat =
        let oG = tryMakeArbPushout cat

        match oG with
        | Some G ->
            let subalg = (Subobject.subalgebra cat G)
            let (X, Y) = subalg.Subobjects |> sampleTwo
            let (+) = Subobject.join
            let (*) = Subobject.meet
            let d = Subobject.boundary subalg
            d (X * Y) = (d X * Y) + (X * d Y)
        | _ ->
            printfn "(a test passed vacuously)"
            true

    let ``∂(x ∨ y) ∨ ∂(x ∧ y) = ∂x ∨ ∂y`` cat =
        let oG = tryMakeArbPushout cat

        match oG with
        | Some G ->
            let subalg = (Subobject.subalgebra cat G)
            let (X, Y) = subalg.Subobjects |> sampleTwo
            let (+) = Subobject.join
            let (*) = Subobject.meet
            let d = Subobject.boundary subalg
            d (X + Y) + d (X * Y) = d X + d Y
        | _ ->
            printfn "(a test passed vacuously)"
            true

    let ``omega-axiom isomorphism`` cat =
        let oG = tryMakeArbPushout cat

        match oG with
        | Some G ->
            let subalg = (Subobject.subalgebra cat G)
            let phi = Truth.subobjectToChar cat subalg
            let psi = Truth.charToSubobject cat
            let O = Truth.omega cat

            (subalg.Subobjects
             |> Set.forall (fun S -> S |> phi |> psi = S))
            && (Morphism.hom subalg.Top O
                |> Set.forall (fun n -> n |> psi |> phi = n))
        | _ ->
            printfn "(a test passed vacuously)"
            true

    let ``exists-preimage-forall adjunction`` cat =
        let oG = tryMakeArbPushout cat
        let oH = tryMakeArbPushout cat

        match (oG, oH) with
        | (Some G, Some H) ->
            let hom = Morphism.hom G H

            if Set.isEmpty hom then
                printfn "(a test passed vacuously)"
                true
            else
                let f = hom |> sampleOne

                let pi = Subobject.preimage cat f
                let ex = Subobject.exists cat f
                let fa = Subobject.forall cat f

                let subalgG = Subobject.subalgebra cat G
                let subalgH = Subobject.subalgebra cat H

                let subG = subalgG.Subobjects
                let subH = subalgH.Subobjects

                let adjunction1 (S, T) =
                    subalgH.LessEq.[ex.[S], T]
                    <=> subalgG.LessEq.[S, pi.[T]]

                let adjunction2 (S, T) =
                    subalgH.LessEq.[T, fa.[S]]
                    <=> subalgG.LessEq.[pi.[T], S]

                (subG, subH)
                ||> Set.product
                |> Set.forall (fun ST -> adjunction1 ST && adjunction2 ST)

        | _ ->
            printfn "(a test passed vacuously)"
            true

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
            static member ``(Sets) ∂(x ∧ y) = (∂x ∧ y) ∨ (x ∧ ∂y)`` = ``∂(x ∧ y) = (∂x ∧ y) ∨ (x ∧ ∂y)`` cat
            static member ``(Sets) ∂(x ∨ y) ∨ ∂(x ∧ y) = ∂x ∨ ∂y`` = ``∂(x ∨ y) ∨ ∂(x ∧ y) = ∂x ∨ ∂y`` cat
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
            static member ``(Bisets) ∂(x ∧ y) = (∂x ∧ y) ∨ (x ∧ ∂y)`` = ``∂(x ∧ y) = (∂x ∧ y) ∨ (x ∧ ∂y)`` cat
            static member ``(Bisets) ∂(x ∨ y) ∨ ∂(x ∧ y) = ∂x ∨ ∂y`` = ``∂(x ∨ y) ∨ ∂(x ∧ y) = ∂x ∨ ∂y`` cat

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
            static member ``(Bouquets) ∂(x ∧ y) = (∂x ∧ y) ∨ (x ∧ ∂y)`` = ``∂(x ∧ y) = (∂x ∧ y) ∨ (x ∧ ∂y)`` cat
            static member ``(Bouquets) ∂(x ∨ y) ∨ ∂(x ∧ y) = ∂x ∨ ∂y`` = ``∂(x ∨ y) ∨ ∂(x ∧ y) = ∂x ∨ ∂y`` cat
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
            static member ``(Graphs) ∂(x ∧ y) = (∂x ∧ y) ∨ (x ∧ ∂y)`` = ``∂(x ∧ y) = (∂x ∧ y) ∨ (x ∧ ∂y)`` cat
            static member ``(Graphs) ∂(x ∨ y) ∨ ∂(x ∧ y) = ∂x ∨ ∂y`` = ``∂(x ∨ y) ∨ ∂(x ∧ y) = ∂x ∨ ∂y`` cat
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
            static member ``(RGraphs) ∂(x ∧ y) = (∂x ∧ y) ∨ (x ∧ ∂y)`` = ``∂(x ∧ y) = (∂x ∧ y) ∨ (x ∧ ∂y)`` cat
            static member ``(RGraphs) ∂(x ∨ y) ∨ ∂(x ∧ y) = ∂x ∨ ∂y`` = ``∂(x ∨ y) ∨ ∂(x ∧ y) = ∂x ∨ ∂y`` cat
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
            static member ``(TruncESets) ∂(x ∧ y) = (∂x ∧ y) ∨ (x ∧ ∂y)`` = ``∂(x ∧ y) = (∂x ∧ y) ∨ (x ∧ ∂y)`` cat
            static member ``(TruncESets) ∂(x ∨ y) ∨ ∂(x ∧ y) = ∂x ∨ ∂y`` = ``∂(x ∨ y) ∨ ∂(x ∧ y) = ∂x ∨ ∂y`` cat
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
    Check.All<RandomTests.RGraphs.RGraphs>(config)
    Check.All<RandomTests.TruncESets.TruncESets>(config)
