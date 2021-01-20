/// Functions to convert strings to LaTeX intended to be displayed in VSCode or Jupyter notebooks using the
/// LaTeXString command.
[<RequireQualifiedAccess>]
module Latex

let ofGeneric (o: _): string =

    let replace (pattern: string) (replacement: string) (input: string): string = input.Replace(pattern, replacement)

    let regexReplace (pattern: string) (replacement: string) (input: string) =
        System.Text.RegularExpressions.Regex.Replace(input, pattern, replacement)

    let regexReplaceRec replace input =
        let rec recurse input =
            if replace input = input then input else recurse (replace input)

        recurse input

    let str = $"%0A{o}" // Sets print width to zero.

    str
    |> regexReplace "[A-Za-z]* \"([A-Za-z])\"" "$1 " // Converts DU strings.
    |> regexReplaceRec (regexReplace "Choice(\d)Of\d" "\\iota_$1 ") // Converts coproducts.
    |> replace @"set []" @"{\emptyset} "
    |> replace @"set " @" "
    |> replace @"[" @"\lbrace " // Lists and sets will both have braces.
    |> replace @"]" @"\rbrace " //
    |> replace @"⟦" @"[ " // (Unicode character) Cotuples will have square brackets.
    |> replace @"⟧" @"] " // (Unicode character)
    |> replace @"(" @"\langle "
    |> replace @")" @"\rangle "
    |> replace @"⟨" "( " // (Unicode character)
    |> replace @"⟩" @") " // (Unicode character)
    |> replace @";" @", "
    |> replace @"..." @"\ldots "
    |> replace @"->" @"\to "
    |> replace @"=>" @"\Rightarrow "
    |> replace @"~" @"{\sim} "
    |> replace @"!" @"\neg "
    |> replace @"/\" @"\land "
    |> replace @"\/" @"\lor "
    |> replace @"@" @"\circ "
    |> replace @"*" @"\times "
    |> replace @"<=" @"\leq "
    |> replace "\"" " " // Remove quotes.

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
    $"{nameof a.Name}: {ofName a.Name}
        {nameof a.Dom}: {a.Dom}$$$$
        {nameof a.Cod}: {a.Cod}"

let ofMorphism (f: Morphism<_, _, _>): string =
    $"{nameof f.Name}: {ofName f.Name}$$$$
        {nameof f.Dom}: {ofName f.Dom.Name}$$$$
        {nameof f.Cod}: {ofName f.Cod.Name}$$$$
        {nameof f.Mapping}: {ofMapMap f.Mapping}"

let ofCategory (C: Category<_>): string =
    $"{nameof C.Name}: {ofName C.Name}$$$$
        {nameof C.Objects}: {ofSeq C.Objects}$$$$
        {nameof C.Hom}: {ofMap C.Hom}$$$$
        {nameof C.Id}: {ofMap C.Id}$$$$
        {nameof C.Compose}: {ofMap C.Compose}"

let ofPresheaf (F: Presheaf<_, _>): string =
    $"{nameof F.Name}: {ofName F.Name}$$$$
        {nameof F.Ob}: {ofMap F.Ob}$$$$
        {nameof F.Ar}: {ofMapMap (F.Ar |> Map.restrict F.Category.NonidArrows)}"
