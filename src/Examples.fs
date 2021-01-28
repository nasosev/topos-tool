/// Definitions of simple basis categories. The given name is usually the one of the presheaf topos on it.
[<RequireQualifiedAccess>]
module Examples

/// The terminal category 1: a single object and no nontrivial arrows.
module Sets =
    type Sets = Sets of string
    let P = Sets "P"
    let objects = set [ P ]
    let arrows = Set.empty
    let compose = Map.empty

    let cat =
        Category.make "Sets" objects arrows compose

    let yo = Yoneda.yo cat
    let hP = yo.Object P

/// Two copies of the terminal category: 1 + 1.
module Bisets =
    type Bisets = Bisets of string
    let P, S = Bisets "P", Bisets "S"
    let objects = set [ P; S ]
    let arrows = Set.empty
    let compose = Map.empty

    let cat =
        Category.make "Bisets" objects arrows compose

    let yo = Yoneda.yo cat
    let hP, hS = yo.Object P, yo.Object S

/// A category with two objects and one arrow between them.
module Bouquets =
    type Bouquets = Bouquets of string
    let V, L = Bouquets "V", Bouquets "L"
    let objects = set [ V; L ]
    let v = Arrow.make "v" V L
    let arrows = set [ v ]
    let compose = Map.empty

    let cat =
        Category.make "Bouquets" objects arrows compose

    let yo = Yoneda.yo cat
    let hV, hL = yo.Object V, yo.Object L

/// A category with two objects and two arrows from one to the other.
module Graphs =
    type Graphs = Graphs of string
    let V, E = Graphs "V", Graphs "E"
    let objects = set [ V; E ]
    let s, t = Arrow.make "s" V E, Arrow.make "t" V E
    let arrows = set [ s; t ]
    let compose = Map.empty

    let cat =
        Category.make "Graphs" objects arrows compose

    let yo = Yoneda.yo cat
    let hV, hE = yo.Object V, yo.Object E

/// Same as Graphs but with a new arrow going the other direction. Note the compose relation.
module ReflexiveGraphs =
    type ReflexiveGraphs = ReflexiveGraphs of string
    let V, E = ReflexiveGraphs "V", ReflexiveGraphs "E"
    let objects = set [ V; E ]

    let s, t, l, u, v =
        Arrow.make "s" V E, Arrow.make "t" V E, Arrow.make "l" E V, Arrow.make "u" E E, Arrow.make "v" E E

    let arrows = set [ s; t; l; u; v ]

    let compose =
        Map [ (s, l), u
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
    let hV, hE = yo.Object V, yo.Object E

/// A square lattice as a category.
module DiamondLattice =
    type DiamondLattice = DiamondLattice of string

    let cat =
        set [ 0 .. 1 ]
        |> Set.powerset
        |> Relation.posetFromFun Set.isSubset
        |> Category.ofPoset "DiamondLattice"

/// The cyclic group Z_3 as a single-object category.
module CyclicGroup3 =
    type CyclicGroup3 = CyclicGroup3 of string
    let G = CyclicGroup3 "G"
    let objects = set [ G ]

    let a, b = Arrow.make "a" G G, Arrow.make "b" G G

    let arrows = set [ a; b ]

    let compose = Map [ (a, a), b; (b, b), a ]

    let cat =
        Category.make "CyclicGroup3" objects arrows compose

    let yo = Yoneda.yo cat
    let hG = yo.Object G

/// The full transformation monoid on a set of size two as a single-object category.
module MonoidTrans2 =
    type MonoidTrans2 = MonoidTrans2 of string
    let M = MonoidTrans2 "M"
    let objects = set [ M ]

    let z, n, o =
        Arrow.make "z" M M, Arrow.make "n" M M, Arrow.make "o" M M

    let arrows = set [ z; n; o ]

    let compose =
        Map [ (z, z), z
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
    let hM = yo.Object M
