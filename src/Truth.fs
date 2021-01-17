/// A generic functor that computes the truth object of a presheaf topos.
module Truth

/// Truth object of a category.
let omega (cat: Category<'A>): Presheaf<'A, Presheaf<'A, Arrow<'A>>> =
    let yo = Yoneda.yo cat

    let ob =
        let sub = Subobject.sub cat

        map [ for A in cat.Objects do
                  let hA = yo.Object A
                  let X = sub.Object hA
                  (A, X) ]

    let ar =
        map [ for a in cat.Arrows do
                  let x =
                      map [ for F in ob.[a.Cod] do
                                let h = Morphism.id F
                                let g = yo.Arrow a
                                let pb = Presheaf.pullback h g
                                let proj = (Morphism.proj2 pb).Cod
                                (F, proj) ]

                  (a, x) ]

    { Name = Name.omega; Ob = ob; Ar = ar }

/// Truth value of the truth object.
let truth (cat: Category<'A>): Morphism<'A, unit, Presheaf<'A, Arrow<'A>>> =
    let name = Name.top

    let mapping =
        let yo = Yoneda.yo cat

        map [ for A in cat.Objects do
                  let hA = yo.Object A
                  let x = map [ ((), hA) ]

                  (A, x) ]

    let dom = Presheaf.one cat
    let cod = omega cat

    { Name = name
      Mapping = mapping
      Dom = dom
      Cod = cod }

/// Characteristic map to subobject.
let charToSubobject (cat: Category<'A>) (c: Morphism<'A, 'S, Presheaf<'A, Arrow<'A>>>): Presheaf<'A, 'S> =
    let t = truth cat
    let pb = Presheaf.pullback c t
    (Morphism.proj1 pb).Cod
