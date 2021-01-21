/// Functions to compute the truth object of a topos and its internal logic.
module Truth

/// Truth object of a category.
let omega (cat: Category<'A>): Presheaf<'A, Heart<'A>> =
    let yo = Yoneda.yo cat

    let ob =
        let sub = Subobject.sub cat

        Map [ for A in cat.Objects do
                  let hA = yo.Object A
                  let X = sub.Object hA
                  (A, X) ]

    let ar =
        Map [ for a in cat.Arrows do
                  let x =
                      Map [ for F in ob.[a.Cod] do
                                let h = Morphism.id F
                                let g = yo.Arrow a
                                let pb = Presheaf.pullback h g

                                let proj = // Simplify the name of the projection for display.
                                    (Morphism.proj2 pb).Cod
                                    |> Presheaf.simplify ob.[a.Dom]

                                (F, proj) ]

                  (a, x) ]

    { Name = Name.omega
      Ob = ob
      Ar = ar
      Category = cat }

/// Truth value of the truth object.
let truth (cat: Category<'A>): Morphism<'A, unit, Heart<'A>> =
    let name = Name.top

    let mapping =
        let yo = Yoneda.yo cat

        Map [ for A in cat.Objects do
                  let hA = yo.Object A
                  let x = Map [ ((), hA) ]

                  (A, x) ]

    let dom = Presheaf.one cat
    let cod = omega cat

    { Name = name
      Mapping = mapping
      Dom = dom
      Cod = cod
      Category = cat }

/// False value of the truth object.
let falsity (cat: Category<'A>): Morphism<'A, unit, Heart<'A>> =
    let name = Name.bot

    let mapping =
        let yo = Yoneda.yo cat

        Map [ for A in cat.Objects do
                  let hA_bot =
                      let subalg = yo.Object A |> Subobject.algebra
                      subalg.Bot

                  let x = Map [ ((), hA_bot) ]

                  (A, x) ]

    let dom = Presheaf.one cat
    let cod = omega cat

    { Name = name
      Mapping = mapping
      Dom = dom
      Cod = cod
      Category = cat }

/// Characteristic morphism to subobject.
let charToSubobject (c: Morphism<'A, 'S, Heart<'A>>): Presheaf<'A, 'S> =
    let t = truth c.Category
    let pb = Presheaf.pullback c t
    let proj = Morphism.proj1 pb
    proj.Cod

/// Subobject to characteristic morphism. (p92 Reyes.)
let subobjectToChar (top: Presheaf<'A, 'S>) (U: Presheaf<'A, 'S>): Morphism<'A, 'S, Heart<'A>> =
    let name = Name.char U.Name
    let Om = omega U.Category

    let mapping =
        Map [ for A in U.Category.Objects do
                  let x =
                      Map [ for s in top.Ob.[A] do
                                let cs =
                                    let filter (a: Arrow<'A>): bool =
                                        U.Ob.[a.Dom] |> Set.contains top.Ar.[a].[s]

                                    let ob =
                                        Map [ for B in U.Category.Objects do
                                                  let X =
                                                      U.Category.Hom.[B, A] |> Set.filter filter

                                                  (B, X) ]

                                    let ar =
                                        Map [ for a in U.Category.Arrows do
                                                  let x =
                                                      Map [ for b in U.Category.Hom.[a.Cod, A] |> Set.filter filter do
                                                                (b, U.Category.Compose.[b, a]) ]

                                                  (a, x) ]

                                    let presheaf =
                                        { Name = Name.empty
                                          Ob = ob
                                          Ar = ar
                                          Category = U.Category }

                                    presheaf |> Presheaf.simplify Om.Ob.[A]

                                (s, cs) ]

                  (A, x) ]

    { Name = name
      Mapping = mapping
      Dom = top
      Cod = Om
      Category = U.Category }

/// Internal NOT. (p139 Goldblatt.)
let internalNot (cat: Category<'A>): Morphism<'A, Heart<'A>, Heart<'A>> =
    let L = cat |> falsity |> Morphism.image
    let Om = omega cat
    L |> subobjectToChar Om

/// Internal AND. (p139 Goldblatt.)
let internalAnd (cat: Category<'A>): Morphism<'A, Heart<'A> * Heart<'A>, Heart<'A>> =
    let t = truth cat

    let TT =
        (t, t) ||> Morphism.tuple |> Morphism.image

    let Om = omega cat
    TT |> subobjectToChar (Om * Om)

/// Internal OR. (p139 Goldblatt.)
let internalOr (cat: Category<'A>): Morphism<'A, Heart<'A> * Heart<'A>, Heart<'A>> =
    let Om = omega cat
    let one = Morphism.id Om

    let const_T =
        let t = truth cat
        let one = Om |> Morphism.one cat
        Morphism.compose t one

    (Morphism.tuple const_T one, Morphism.tuple one const_T)
    ||> Morphism.cotuple
    |> Morphism.image
    |> subobjectToChar (Om * Om)

/// Internal IMPLIES. (p139 Goldblatt.)
let internalImply (cat: Category<'A>): Morphism<'A, Heart<'A> * Heart<'A>, Heart<'A>> =
    let Om = omega cat
    let pi_1 = Morphism.proj1 (Om * Om)

    (internalAnd cat, pi_1)
    ||> Presheaf.equaliser
    |> subobjectToChar (Om * Om)
