/// Error messages.
[<RequireQualifiedAccess>]
module Error

let makeCategory =
    "Supplied data does not determine a category: not all composable pairs appear in the compose map."

let makePresheaf =
    "Supplied data does not determine a presheaf."

let makeMorphism =
    "Supplied data does not determine a morphism."

let domainMismatch = "Domain mismatch."
let codomainMismatch = "Codomain mismatch."
let todo = "Todo: not yet implemented."
