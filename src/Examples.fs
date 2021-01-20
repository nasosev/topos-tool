/// Definitions of simple presheaf topoi from the book of Reyes et al.
[<RequireQualifiedAccess>]
module Examples

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

module RGraphs =
    type RGraphs = RGraphs of string
    let V, E = RGraphs "V", RGraphs "E"
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
        Category.make "RGraphs" objects arrows compose

    let yo = Yoneda.yo cat
    let hV, hE = yo.Object V, yo.Object E

module TruncESets =
    type TruncESets = TruncESets of string
    let V = TruncESets "V"
    let objects = set [ V ]

    let s, s2, s3, s4 =
        Arrow.make "s" V V, Arrow.make "s2" V V, Arrow.make "s3" V V, Arrow.make "s4" V V

    let arrows = set [ s; s2; s3; s4 ]

    let compose =
        Map [ (s, s), s2
              (s, s2), s3
              (s2, s), s3
              (s2, s2), s4
              (s3, s), s4
              (s, s3), s4 ]

    let cat =
        Category.make "TruncESets" objects arrows compose

    let yo = Yoneda.yo cat
    let hV = yo.Object V
