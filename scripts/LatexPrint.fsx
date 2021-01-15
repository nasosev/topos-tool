type Latex =
    static member print(X: Arrow<_>): LaTeXString = Latex.ofArrow X |> LaTeXString
    static member print(C: Category<_>): LaTeXString = Latex.ofCategory C |> LaTeXString
    static member print(F: Presheaf<_, _>): LaTeXString = Latex.ofPresheaf F |> LaTeXString
    static member print(F: Morphism<_, _, _>): LaTeXString = Latex.ofMorphism F |> LaTeXString
    static member print(X: seq<_>): LaTeXString = Latex.ofSeq X |> LaTeXString
    static member genericPrint(x: obj): MathString = Latex.ofGeneric x |> MathString // Todo: must use different name because of https://github.com/fsharp/fslang-suggestions/issues/905 .
    static member mapPrint(x: Map<_, _>): LaTeXString = Latex.ofMap x |> LaTeXString // Todo: as above.