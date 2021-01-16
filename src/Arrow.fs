/// Functions specific to the 'Arrow' type.
[<RequireQualifiedAccess>]
module Arrow

/// Helper function to create an arrow with a given name, domain and codomain.
let make (nameStr: string) (dom: 'A) (cod: 'A): Arrow<'A> =
    { Name = Name.ofString nameStr
      Dom = dom
      Cod = cod }

/// Creates the identity arrow on a given object.
let internal id (A: 'A): Arrow<'A> = { Name = Name.id A; Dom = A; Cod = A }
