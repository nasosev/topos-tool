/// Functions to compute general set-valued limits and colimits.
[<RequireQualifiedAccess>]
module Limit

/// Colimit of a functor.
let colim (functor: BigFunctor<'I, 'A, 'S>): Presheaf<'A, Set<'I * 'S>> =
    let ob =

        Map [ for A in functor.Cat.Objects do
                  let coproduct =
                      set [ for I in functor.Dom.Objects do
                                for s in functor.Ob.[I].Ob.[A] do
                                    (I, s) ]

                  let relationDomain =
                      (functor.Dom.Objects, coproduct |> Set.map snd)
                      ||> Set.product

                  let equal =
                      set [ for i in functor.Dom.NonidArrows do
                                for s in functor.Ob.[i.Dom].Ob.[A] do
                                    let im_s = functor.Ar.[i].Map.[A].[s]
                                    set [ (i.Dom, s), (i.Cod, im_s) ] ]
                      |> Set.unionMany
                      |> Relation.ofPairs relationDomain relationDomain
                      |> Relation.equivalenceClosure

                  let colimit =
                      coproduct |> Set.partitionByEquivalence equal

                  (A, colimit) ]

    let ar =
        Map [ for a in functor.Cat.Arrows do
                  let x =
                      Map [ for R in ob.[a.Cod] do
                                let rep = R |> Seq.item 0 // R is inhabited.
                                let repF = functor.Ob.[fst rep]
                                let imageRep = repF.Ar.[a].[snd rep]

                                let imageClass =
                                    ob.[a.Dom]
                                    |> Seq.find (fun X -> X |> Set.contains (fst rep, imageRep))

                                (R, imageClass) ]

                  (a, x) ]

    { Name = Name.empty
      Ob = ob
      Ar = ar
      Cat = functor.Cat }

/// Limit of a functor.
let lim (functor: BigFunctor<'I, 'A, 'S>) = failwith Error.todo
