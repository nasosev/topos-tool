/// Functions to convert strings to LaTeX intended to be displayed in VSCode or Jupyter notebooks using the
/// LaTeXString command.
[<RequireQualifiedAccess>]
module Latex

open System.Text.RegularExpressions

let ofGeneric (o: obj): string =
    let replace (pattern: string) (replacement: string) (input: string): string = input.Replace(pattern, replacement)

    let unwrapDUStrings (input: string): string =
        Regex.Replace(input, "[A-Za-z]* \"", " ")

    let str = $"%0A{o}" // Sets print width to zero.

    str
    |> unwrapDUStrings
    |> replace "Choice1Of2" "\iota_0 "
    |> replace "Choice2Of2" "\iota_1 "
    |> replace @"set [" " ["
    |> replace @"->" @"\to "
    |> replace @"=>" @"\Rightarrow "
    |> replace @"~" @"{\sim} "
    |> replace @"!" @"\neg "
    |> replace @"/\" @"\land "
    |> replace @"\/" @"\lor "
    |> replace "\"" @" "
    |> replace @"@" @"\circ "
    |> replace @"*" @"\times "
    |> replace @"<=" @"\leq "
    |> replace @"[]" @"\emptyset "
    |> replace @"[" @"\lbrace "
    |> replace @"]" @"\rbrace "
    |> replace @"(" @"\langle "
    |> replace @")" @"\rangle "
    |> replace @"⟨" @"("
    |> replace @"⟩" @")"
    |> replace @";" @", "
    |> replace @"..." @"\ldots "

let ofName (name: Name): string = $"\[\mathsf{{{ofGeneric name}}}\]"

let ofSeq (X: seq<'A>): string =
    X
    |> Seq.map ofGeneric
    |> String.concat ", "
    |> sprintf @"\[\left\lbrace%s\right\rbrace\]"

let ofMap (x: Map<_, _>): string =
    x
    |> Map.toList
    |> List.map (fun (k, v) -> sprintf @"%s &\mapsto %s\\" (ofGeneric k) (ofGeneric v))
    |> String.concat "\n"
    |> sprintf "\n%s\n"
    |> sprintf @"\begin{align*}%s\end{align*}"

let private ofInnerMap (x: Map<_, _>): string =
    x
    |> Map.toList
    |> List.map (fun (k, v) -> sprintf @"%s &\mapsto %s\\" (ofGeneric k) (ofGeneric v))
    |> String.concat "\n"
    |> sprintf "\n%s\n"
    |> sprintf @"\left\lbrace\begin{aligned}%s\end{aligned}\right\rbrace"

let ofMapMap (x: Map<'A, Map<_, _>>): string =
    x
    |> Map.toList
    |> List.map (fun (k, v) -> sprintf @"%s &\mapsto %s\\" (ofGeneric k) (ofInnerMap v))
    |> String.concat "\n"
    |> sprintf "\n%s\n"
    |> sprintf @"\begin{align*}%s\end{align*}"

let ofArrow (a: Arrow<_>): string =
    $"{nameof a.Name}: {ofName a.Name}
        {nameof a.Dom}: {a.Dom}
        {nameof a.Cod}: {a.Cod}"

let ofMorphism (n: Morphism<_, _, _>): string =
    $"{nameof n.Name}: {ofName n.Name}
        {nameof n.Mapping}: {ofMapMap n.Mapping}"

let ofCategory (C: Category<_>): string =
    $"{nameof C.Name}: {ofName C.Name}
        {nameof C.Objects}: {ofSeq C.Objects}
        {nameof C.Hom}: {ofMap C.Hom}
        {nameof C.Id}: {ofMap C.Id}
        {nameof C.Compose}: {ofMap C.Compose}"

let ofPresheaf (F: Presheaf<_, _>): string =
    $"{nameof F.Name}: {ofName F.Name}
        {nameof F.Ob}: {ofMap F.Ob}
        {nameof F.Ar}: {ofMapMap F.Ar}"
