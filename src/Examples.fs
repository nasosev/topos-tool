/// Definitions of simple basis categories. The given name is usually the one of the presheaf topos on it.
[<RequireQualifiedAccess>]
module Examples

/// The terminal category 1: a single object and no nontrivial arrows.
module Sets =
    let cat = Category.one
    let yo = Yoneda.yo cat
    let P = cat.Objects |> Seq.exactlyOne
    let hP = yo.Ob P

/// Two copies of the terminal category: 1 + 1.
module Bisets =
    let cat = Category.one + Category.one
    let yo = Yoneda.yo cat

    let P, S =
        cat.Objects |> Seq.item 0, cat.Objects |> Seq.item 1

    let hP, hS = yo.Ob P, yo.Ob S

/// A category with two objects and one arrow between them.
module Bouquets =
    type Bouquets = Bouquets of string
    let V, L = Bouquets "V", Bouquets "L"
    let objects = [ V; L ]
    let v = Arrow.make "v" V L
    let arrows = [ v ]
    let compose = []

    let cat =
        Category.make "Bouquets" objects arrows compose

    let yo = Yoneda.yo cat
    let hV, hL = yo.Ob V, yo.Ob L

/// A category with two objects and two arrows from one to the other.
module Graphs =
    type Graphs = Graphs of string
    let V, E = Graphs "V", Graphs "E"
    let objects = [ V; E ]
    let s, t = Arrow.make "s" V E, Arrow.make "t" V E
    let arrows = [ s; t ]
    let compose = []

    let cat =
        Category.make "Graphs" objects arrows compose

    let yo = Yoneda.yo cat
    let hV, hE = yo.Ob V, yo.Ob E

/// Same as Graphs but with a new arrow going the other direction. Note the compose relation.
module ReflexiveGraphs =
    type ReflexiveGraphs = ReflexiveGraphs of string
    let V, E = ReflexiveGraphs "V", ReflexiveGraphs "E"
    let objects = [ V; E ]

    let s, t, l, u, v =
        Arrow.make "s" V E, Arrow.make "t" V E, Arrow.make "l" E V, Arrow.make "u" E E, Arrow.make "v" E E

    let arrows = [ s; t; l; u; v ]

    let compose =
        [ (s, l), u
          (t, l), v
          (u, u), u
          (v, v), v
          (u, v), u
          (v, u), v
          (u, s), s
          (u, t), s
          (v, s), t
          (v, t), t
          (l, u), l
          (l, v), l ]

    let cat =
        Category.make "ReflexiveGraphs" objects arrows compose

    let yo = Yoneda.yo cat
    let hV, hE = yo.Ob V, yo.Ob E

/// A diamond lattice as a category.
module DiamondLattice =
    type DiamondLattice = DiamondLattice of string

    let B, L, R, T =
        DiamondLattice "B", DiamondLattice "L", DiamondLattice "R", DiamondLattice "T"

    let cat =
        [ (B, L); (B, R); (L, T); (R, T) ]
        |> set
        |> Relation.posetFromHasse
        |> Category.ofPoset "DiamondLattice"

    let yo = Yoneda.yo cat

    let hB, hL, hR, hT = yo.Ob B, yo.Ob L, yo.Ob R, yo.Ob T

/// The cyclic group Z_3 as a single-object category.
module CyclicGroup3 =
    type CyclicGroup3 = CyclicGroup3 of string
    let G = CyclicGroup3 "G"
    let objects = [ G ]

    let a, b = Arrow.make "a" G G, Arrow.make "b" G G

    let arrows = [ a; b ]

    let compose = [ (a, a), b; (b, b), a ]

    let cat =
        Category.make "CyclicGroup3" objects arrows compose

    let yo = Yoneda.yo cat
    let hG = yo.Ob G

/// The full transformation monoid on a set of size two as a single-object category.
module MonoidTrans2 =
    type MonoidTrans2 = MonoidTrans2 of string
    let M = MonoidTrans2 "M"
    let objects = [ M ]

    let z, n, o =
        Arrow.make "z" M M, Arrow.make "n" M M, Arrow.make "o" M M

    let arrows = [ z; n; o ]

    let compose =
        [ (z, z), z
          (z, o), z
          (z, n), z
          (o, z), o
          (o, o), o
          (o, n), o
          (n, o), z
          (n, z), o ]

    let cat =
        Category.make "MonoidT2" objects arrows compose

    let yo = Yoneda.yo cat
    let hM = yo.Ob M
