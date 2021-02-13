/// Functions to convert strings to LaTeX intended to be displayed in VSCode or Jupyter notebooks using the
/// LaTeXString command.
[<RequireQualifiedAccess>]
module Latex

let ofGeneric (o: _): string =

    let str = $"%0A{o}" // (Sets print width to zero.)

    str
    |> String.regexReplace "[A-Za-z0-9]* \"([A-Za-z])\"" "$1 " // Converts DU strings.
    |> String.replaceRecursive (String.regexReplace "Choice(\d)Of\d" "\\iota_$1 ") // Converts coproducts.
    |> String.replace @"set []" @"{\emptyset} "
    |> String.replace @"set " @" "
    |> String.replace @"[" @"\lbrace " // Lists and sets will both have braces.
    |> String.replace @"]" @"\rbrace " //
    |> String.replace @"⟦" @"[ " // (Unicode character.) Cotuples will have square brackets.
    |> String.replace @"⟧" @"] " // (Unicode character.)
    |> String.replace @"(" @"\langle "
    |> String.replace @")" @"\rangle "
    |> String.replace @"⟨" "( " // (Unicode character.)
    |> String.replace @"⟩" @") " // (Unicode character.)
    |> String.replace @";" @", "
    |> String.replace @"..." @"\ldots "
    |> String.replace @"->" @"\to "
    |> String.replace @"=>" @"\Rightarrow "
    |> String.replace @"~" @"{\sim} "
    |> String.replace @"-" @"\neg "
    |> String.replace @"/\" @"\land "
    |> String.replace @"\/" @"\lor "
    |> String.replace @"@" @"\circ "
    |> String.replace @"*" @"\times "
    |> String.replace @"<=" @"\leq "
    |> String.replace "\"" " " // Remove quotes.

let ofName (name: Name): string = @$"\[\mathsf{{{ofGeneric name}}}\]"

let ofSeq (X: seq<_>): string =
    X
    |> Seq.map ofGeneric
    |> String.concat ", "
    |> sprintf @"\[\left\lbrace %s \right\rbrace\]"

let ofMap (x: Map<_, _>): string =
    x
    |> Seq.map (fun (KeyValue (k, v)) -> sprintf @"%s &\mapsto %s\\" (ofGeneric k) (ofGeneric v))
    |> String.concat "\n"
    |> sprintf "\n%s\n"
    |> sprintf @"\begin{align*} %s \end{align*}"

let private ofInnerMap (x: Map<_, _>): string =
    x
    |> Seq.map (fun (KeyValue (k, v)) -> sprintf @"%s &\mapsto %s\\" (ofGeneric k) (ofGeneric v))
    |> String.concat "\n"
    |> sprintf "\n%s\n"
    |> sprintf @"\left\lbrace\begin{aligned} %s \end{aligned}\right\rbrace "

let ofMapMap (x: Map<'A, Map<_, _>>): string =
    x
    |> Seq.map (fun (KeyValue (k, v)) -> sprintf @"%s &\mapsto %s\\" (ofGeneric k) (ofInnerMap v))
    |> String.concat "\n"
    |> sprintf "\n%s\n"
    |> sprintf @"\begin{align*} %s \end{align*}"

let ofArrow (a: Arrow<_>): string =
    $"{nameof a.Name}: {ofName a.Name}\n
        {nameof a.Dom}: $${ofGeneric a.Dom}$$\n
        {nameof a.Cod}: $${ofGeneric a.Cod}$$"

let ofMorphism (f: Morphism<_, _, _>): string =
    $"{nameof f.Cat}: {ofName f.Cat.Name}\n
        {nameof f.Name}: {ofName f.Name}\n
        {nameof f.Dom}: {ofName f.Dom.Name}\n
        {nameof f.Cod}: {ofName f.Cod.Name}\n
        {nameof f.Map}: {ofMapMap f.Map}"

let ofCategory (C: Category<_>): string =
    $"{nameof C.Name}: {ofName C.Name}\n
        {nameof C.Objects}: {ofSeq C.Objects}\n
        {nameof C.NonidArrows}: {ofSeq C.NonidArrows}\n
        {nameof C.Hom}: {ofMap C.Hom}\n
        {nameof C.Compose}: {ofMap C.Compose}"

let ofSmallFunctor (F: SmallFunctor<_, _>): string =
    $"{nameof F.Name}: {ofName F.Name}\n
        {nameof F.Ob}: {ofMap F.Ob}\n
        {nameof F.Ar}: {ofMap (F.Ar |> Map.restrict F.Dom.NonidArrows)}\n
        {nameof F.Dom}: {ofName F.Dom.Name}\n
        {nameof F.Cod}: {ofName F.Cod.Name}"

let ofBigFunctor (F: BigFunctor<_, _, _>): string =
    $"{nameof F.Name}: {ofName F.Name}\n
        {nameof F.Ob}: {ofMap F.Ob}\n
        {nameof F.Ar}: {ofMap (F.Ar |> Map.restrict F.Dom.NonidArrows)}\n
        {nameof F.Dom}: {ofName F.Dom.Name}\n
        {nameof F.Cat}: {ofName F.Cat.Name}"

let ofPresheaf (F: Presheaf<_, _>): string =
    $"{nameof F.Name}: {ofName F.Name}\n
        {nameof F.Ob}: {ofMap F.Ob}\n
        {nameof F.Ar}: {ofMapMap (F.Ar |> Map.restrict F.Cat.NonidArrows)}"
