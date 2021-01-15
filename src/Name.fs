/// Functions to make and combine names.
[<RequireQualifiedAccess>]
module Name

let yo = { String = "h" }
let pi = { String = @"\pi" }
let omega = { String = @"\Omega" }
let top = { String = @"\top" }
let bot = { String = @"\bot" }
let ofString (s: string): Name = { String = s }
let ofInt (i: int): Name = { String = $"{i}" }
let name a: Name = { String = $"{a}" }
let id (name: Name): Name = { String = $"1_{{{name.String}}}" }
let categoryOfElements (name: Name): Name = { String = $"\int {name.String}" }
let negate (name: Name): Name = { String = $"@!{name.String}" }
let supplement (name: Name): Name = { String = $"~{name.String}" }
let boundary (name: Name): Name = { String = $"\partial{name.String}" }
let coboundary (name: Name): Name = { String = $"d{name.String}" }

let product (name: Name) (name': Name): Name =
    { String = $"⟨{name.String} * {name'.String}⟩" }

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

let compose (name: Name) (name': Name): Name =
    { String = $"⟨{name.String} @ {name'.String}⟩" }

let sub (name: Name) (name': Name): Name =
    { String = $"{{{name.String}}}_{{{name'.String}}}" }

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

let pullback (name: Name) (name': Name) (name'': Name): Name =
    { String = $"⟨{name.String} *_{{{name''.String}}} {name'.String}⟩" }

let pushout (name: Name) (name': Name) (name'': Name): Name =
    { String = $"⟨{name.String} +_{{{name''.String}}} {name'.String}⟩" }
