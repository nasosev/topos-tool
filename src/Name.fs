/// Functions to make and combine names.
// todo: names should be rethought as the current design leads to unpleasant and fragile implementation of Arrow.proj
[<RequireQualifiedAccess>]
module Name

let empty = { String = "" }
let yo = { String = "h" }
let omega = { String = @"\Omega" }
let one = { String = "!" }
let top = { String = @"\top" }
let bot = { String = @"\bot" }
let subobject = { String = "Sub" }
let ofString (s: string): Name = { String = s }
let ofInt (i: int): Name = { String = $"{i}" }
let name (a: 'A): Name = { String = $"{a}" }
let id (A: 'A): Name = { String = $"1_{{%A{A}}}" }
let op (name: Name): Name = { String = $"{{{name.String}}}^{{op}}" }
let eval (name: Name): Name = { String = $"e_{{{name.String}}}" }
let char (name: Name): Name = { String = @$"\chi_{{{name.String}}}" }
let categoryOfElements (name: Name): Name = { String = @$"\int {name.String}" }
let negate (name: Name): Name = { String = $"-{name.String}" }
let supplement (name: Name): Name = { String = $"~{name.String}" }
let boundary (name: Name): Name = { String = @$"\partial{name.String}" }
let coboundary (name: Name): Name = { String = $"d{name.String}" }
let possibility (name: Name): Name = { String = @$"\diamond {name.String}" }
let necessity (name: Name): Name = { String = @$"\square {name.String}" }
let proj (i: int) (name: Name): Name = { String = @$"\pi_{i}{name.String}" }
let coproj (i: int) (name: Name): Name = { String = @$"\iota_{i}{name.String}" }

let preimage (name: Name) (name': Name): Name =
    { String = @$"{{{name.String}}}^{{*}}{{{name'.String}}}" }

let exists (name: Name) (name': Name): Name =
    { String = @$"\exists_{{{name.String}}}{{{name'.String}}}" }

let forall (name: Name) (name': Name): Name =
    { String = @$"\forall_{{{name.String}}}{{{name'.String}}}" }

let product (name: Name) (name': Name): Name =
    { String = $"⟨{name.String} * {name'.String}⟩" }

let tuple (name: Name) (name': Name): Name =
    { String = $"({name.String}, {name'.String})" }

let cotuple (name: Name) (name': Name): Name =
    { String = $"⟦{name.String}, {name'.String}⟧" }

let sum (name: Name) (name': Name): Name =
    { String = $"⟨{name.String} + {name'.String}⟩" }

let exp (name: Name) (name': Name): Name =
    { String = $"⟨{name.String} -> {name'.String}⟩" }

let hom (name: Name) (name': Name): Name =
    { String = $"⟨{name.String} => {name'.String}⟩" }

let equaliser (name: Name) (name': Name): Name =
    { String = $"Eq [{name.String}, {name'.String}]" }

let coequaliser (name: Name) (name': Name): Name =
    { String = $"Coeq [{name.String}, {name'.String}]" }

let apply (name: Name) (name': Name): Name =
    { String = $"{name.String} ⟨{name'.String}⟩" }

let compose (name: Name) (name': Name): Name =
    { String = $"⟨{name.String} @ {name'.String}⟩" }

let sub (name: Name) (name': Name): Name =
    { String = $"{{{name.String}}}_{{{name'.String}}}" }

let sup (name: Name) (name': Name): Name =
    { String = $"{{{name.String}}}^{{{name'.String}}}" }

let yoneda (name: Name): Name =
    { String = $"{{ {yo.String}_{{{name.String}}} }}" }

let lessEq (name: Name) (name': Name): Name =
    { String = $"{name.String} <= {name'.String}" }

let join (name: Name) (name': Name): Name =
    { String = $"⟨{name.String} \/ {name'.String}⟩" }

let meet (name: Name) (name': Name): Name =
    { String = $"⟨{name.String} /\ {name'.String}⟩" }

let imply (name: Name) (name': Name): Name =
    { String = $"⟨{name.String} => {name'.String}⟩" }

let minus (name: Name) (name': Name): Name =
    { String = $"⟨{name.String} \ {name'.String}⟩" }

let comma (name: Name) (name': Name): Name =
    { String = $"⟨{name.String} \downarrow {name'.String}⟩" }

let pullback (name: Name) (name': Name) (name'': Name): Name =
    { String = $"⟨{name.String} *_{{{name'.String}}} {name''.String}⟩" }

let pushout (name: Name) (name': Name) (name'': Name): Name =
    { String = $"⟨{name.String} +_{{{name'.String}}} {name''.String}⟩" }
