/// Functions specific to the 'Arrow' type.
[<RequireQualifiedAccess>]
module Arrow

/// Helper function to create an arrow with a given name, domain and codomain.
let make (nameString: string) (dom: 'A) (cod: 'A): Arrow<'A> =
    { Name = Name.ofString nameString
      Dom = dom
      Cod = cod }

/// Creates the identity arrow on a given object.
let internal id (A: 'A): Arrow<'A> = { Name = Name.id A; Dom = A; Cod = A }

/// Checks if an arrow is an identity arrow. This shouldn't be used; instead use `Category.Id`.
let internal isId (a: Arrow<'A>): bool = a.Name.String.[0..1] = "1_"

/// Reverses the direction of an arrow.
let flip (a: Arrow<'A>): Arrow<'A> = { a with Dom = a.Cod; Cod = a.Dom }

/// Projects onto the first component of an arrow from a product category.
let proj1 (a: Arrow<'A * 'B>): Arrow<'A> =

    let pattern = "{\(([^,]*), ([^)]*).*"

    { Name =
          String.regexReplace pattern "$1" a.Name.String
          |> Name.ofString
      Dom = fst a.Dom
      Cod = fst a.Cod }

/// Projects onto the second component of an arrow from a product category.
let proj2 (a: Arrow<'A * 'B>): Arrow<'B> =

    let pattern = "{\(([^,]*), ([^)]*).*"

    { Name =
          String.regexReplace pattern "$2" a.Name.String
          |> Name.ofString
      Dom = snd a.Dom
      Cod = snd a.Cod }

/// Projects onto the first component of an arrow from a triple product category.
let proj3_1 (a: Arrow<'A * 'B * 'C>): Arrow<'A> =

    let pattern = "{\(([^,]*), ([^)]*).*"

    { Name =
          String.regexReplace pattern "$1" a.Name.String
          |> Name.ofString
      Dom = first a.Dom
      Cod = first a.Cod }

/// Projects onto the second component of an arrow from a triple product category.
let proj3_2 (a: Arrow<'A * 'B * 'C>): Arrow<'B> =
    let pattern = "{\(([^,]*), ([^)]*).*"

    { Name =
          String.regexReplace pattern "$2" a.Name.String
          |> Name.ofString
      Dom = second a.Dom
      Cod = second a.Cod }

/// Projects onto the third component of an arrow from a triple product category.
let proj3_3 (a: Arrow<'A * 'B * 'C>): Arrow<'C> =
    let pattern = "{\(([^,]*), ([^,]*), ([^)]*),.*"

    { Name =
          String.regexReplace pattern "$3" a.Name.String
          |> Name.ofString
      Dom = third a.Dom
      Cod = third a.Cod }
