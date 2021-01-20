/// Convenient syntax definitions.
[<AutoOpen>]
module Syntax

let (*) F G = Presheaf.product F G
let (+) F G = Presheaf.sum F G
let (^) F G = Presheaf.exp G F
let (==) F G = Presheaf.isIso F G
