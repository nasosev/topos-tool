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
                                let yoCod = yo.Object a.Cod
                                let yoDom = yo.Object a.Dom
                                let h = Morphism.id F
                                let g = yo.Arrow a
                                let pb = Presheaf.pullback F h yoCod g yoDom
                                let proj = pb |> Morphism.apply (Morphism.proj2 pb)
                                (F, proj) ]

                  (a, x) ]

    { Name = Name.omega; Ob = ob; Ar = ar }
