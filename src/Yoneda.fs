/// A generic functor that computes the Yoneda embedding.
[<RequireQualifiedAccess>]
module Yoneda

/// Yoneda embedding C -> Psh(C).
let yo (cat: Category<'A>)
       : GenericFunctor<('A -> Presheaf<'A, Arrow<'A>>), (Arrow<'A> -> Morphism<'A, Arrow<'A>, Arrow<'A>>)> =
    let ob (A: 'A): Presheaf<'A, Arrow<'A>> =
        let name = Name.yoneda (Name.ofString $"{A}")

        let ob =
            map [ for B in cat.Objects do
                      let X = cat.Hom.[B, A]
                      (B, X) ]

        let ar =
            map [ for a in cat.Arrows do
                      let x =
                          map [ for b in cat.Hom.[a.Cod, A] do
                                    (b, cat.Compose.[b, a]) ]

                      (a, x) ]

        { Name = name; Ob = ob; Ar = ar }

    let ar (a: Arrow<'A>): Morphism<'A, Arrow<'A>, Arrow<'A>> =
        let name = Name.yoneda a.Name

        let mapping =
            map [ for A in cat.Objects do
                      let x =
                          map [ for b in cat.Hom.[A, a.Dom] do
                                    (b, cat.Compose.[a, b]) ]

                      (A, x) ]

        let dom = ob a.Dom
        let cod = ob a.Cod

        { Name = name
          Mapping = mapping
          Dom = dom
          Cod = cod }

    { Name = Name.yo
      Object = ob
      Arrow = ar }
