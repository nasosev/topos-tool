/// A generic functor that computes the Yoneda embedding.
[<RequireQualifiedAccess>]
module Yoneda

/// Yoneda embedding C -> Psh(C).
let yo (cat: Category<'A>): BigFunctor<'A, 'A, Arrow<'A>> =
    let ob =
        Map [ for A in cat.Objects do
                  let name = Name.yoneda (Name.ofString $"{A}")

                  let ob =
                      Map [ for B in cat.Objects do
                                let X = cat.Hom.[B, A]
                                (B, X) ]

                  let ar =
                      Map [ for a in cat.Arrows do
                                let x =
                                    Map [ for b in cat.Hom.[a.Cod, A] do
                                              (b, cat.Compose.[b, a]) ]

                                (a, x) ]

                  let F =
                      { Name = name
                        Ob = ob
                        Ar = ar
                        Cat = cat }

                  (A, F) ]

    let ar =
        Map [ for a in cat.Arrows do
                  let name = Name.yoneda a.Name

                  let map =
                      Map [ for A in cat.Objects do
                                let x =
                                    Map [ for b in cat.Hom.[A, a.Dom] do
                                              (b, cat.Compose.[a, b]) ]

                                (A, x) ]

                  let dom = ob.[a.Dom]
                  let cod = ob.[a.Cod]

                  let f =
                      { Name = name
                        Map = map
                        Dom = dom
                        Cod = cod
                        Cat = dom.Cat }

                  (a, f) ]

    { Name = Name.yo
      Ob = ob
      Ar = ar
      Dom = cat
      Cat = cat }
