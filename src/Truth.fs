/// Functions to compute the truth object of a topos and its internal logic.
module Truth

/// Truth object of a category.
let omega (cat: Category<'A>): Presheaf<'A, Heart<'A>> =
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
let truth (cat: Category<'A>): Morphism<'A, unit, Heart<'A>> =
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

/// False value of the truth object.
let falsity (cat: Category<'A>): Morphism<'A, unit, Heart<'A>> =
    let name = Name.bot

    let mapping =
        let yo = Yoneda.yo cat

        map [ for A in cat.Objects do
                  let hA_bot =
                      (yo.Object A |> Subobject.subalgebra cat).Bot

                  let x = map [ ((), hA_bot) ]

                  (A, x) ]

    let dom = Presheaf.one cat
    let cod = omega cat

    { Name = name
      Mapping = mapping
      Dom = dom
      Cod = cod }

/// Characteristic morphism to subobject.
let charToSubobject (cat: Category<'A>) (c: Morphism<'A, 'S, Heart<'A>>): Presheaf<'A, 'S> =
    let t = truth cat
    let pb = Presheaf.pullback c t
    (Morphism.proj1 pb).Cod

/// Subobject to characteristic morphism.
let subobjectToChar (cat: Category<'A>) (top: Presheaf<'A, 'S>) (S: Presheaf<'A, 'S>): Morphism<'A, 'S, Heart<'A>> =
    let name = Name.char S.Name
    let cod = omega cat

    let mapping =
        map [ for A in cat.Objects do
                  let x =
                      map [ for s in top.Ob.[A] do
                                let cs =
                                    let filter (a: Arrow<'A>): bool =
                                        S.Ob.[a.Dom] |> Set.contains top.Ar.[a].[s]

                                    let ob =
                                        map [ for B in cat.Objects do
                                                  let X = cat.Hom.[B, A] |> Set.filter filter
                                                  (B, X) ]

                                    let ar =
                                        map [ for a in cat.Arrows do
                                                  let x =
                                                      map [ for b in cat.Hom.[a.Cod, A] |> Set.filter filter do
                                                                (b, cat.Compose.[b, a]) ]

                                                  (a, x) ]

                                    let presheaf = { Name = Name.empty; Ob = ob; Ar = ar }
                                    presheaf |> Presheaf.simplify cod.Ob.[A]

                                (s, cs) ]

                  (A, x) ]

    { Name = name
      Mapping = mapping
      Dom = top
      Cod = cod }

/// Internal NOT. (p139 Goldblatt.)
let internalNot (cat: Category<'A>): Morphism<'A, Heart<'A>, Heart<'A>> =
    let L = cat |> falsity |> Morphism.image
    let Om = omega cat
    L |> subobjectToChar cat Om

/// Internal AND. (p139 Goldblatt.)
let internalAnd (cat: Category<'A>): Morphism<'A, Heart<'A> * Heart<'A>, Heart<'A>> =
    let t = cat |> truth

    let TT =
        (t, t) ||> Morphism.tuple |> Morphism.image

    let Om = omega cat
    let OmOm = (Om, Om) ||> Presheaf.product
    TT |> subobjectToChar cat OmOm

/// Internal OR. (p139 Goldblatt.)
let internalOr (cat: Category<'A>): Morphism<'A, Heart<'A> * Heart<'A>, Heart<'A>> = failwith "todo"

/// Internal IMPLIES. (p139 Goldblatt.)
let internalImplies (cat: Category<'A>): Morphism<'A, Heart<'A> * Heart<'A>, Heart<'A>> = failwith "todo"
