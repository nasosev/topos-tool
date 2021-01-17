/// Core types. Auto-opened.
[<AutoOpen>]
module Types

// WARNING: the order or fields in a record may have a huge performance impact!

/// Type of names.
[<StructuredFormatDisplay("{String}")>]
type Name = { String: string }

/// Type of arrows in a category between generic objects.
///
[<StructuredFormatDisplay("{Name}")>]
type Arrow<'A> = { Name: Name; Dom: 'A; Cod: 'A }

/// Type of a category with generic objects.
/// It is intended that ``A` is a single-case DU type, e.g. `type Sets = Sets of string`.
/// This ensures type safety.
[<StructuredFormatDisplay("{Name}")>]
type Category<'A when 'A: comparison> =
    { Name: Name
      Objects: Set<'A>
      NonidArrows: Set<Arrow<'A>>
      Arrows: Set<Arrow<'A>>
      Id: Map<'A, Arrow<'A>>
      Hom: Map<'A * 'A, Set<Arrow<'A>>>
      Compose: Map<Arrow<'A> * Arrow<'A>, Arrow<'A>> }

/// Type of a presheaf into homogenous sets of type `'S` containing object and arrow functions.
/// Overrides comparison so `Name` is ignored.
[<CustomEquality; CustomComparison; StructuredFormatDisplay("{Name}")>]
type Presheaf<'A, 'S when 'A: comparison and 'S: comparison> =
    { Name: Name
      Ob: Map<'A, Set<'S>>
      Ar: Map<Arrow<'A>, Map<'S, 'S>> }
    override x.Equals(yobj) =
        match yobj with
        | :? (Presheaf<'A, 'S>) as y -> (x.Ob = y.Ob && x.Ar = y.Ar) // WARNING: order of conjuction has a big performance impact.
        | _ -> false

    override x.GetHashCode() = hash x.Ob ^^^ hash x.Ar

    interface System.IComparable with
        member x.CompareTo yobj =
            match yobj with
            | :? (Presheaf<'A, 'S>) as y ->
                let c = compare x.Ob y.Ob
                if c <> 0 then c else compare x.Ar y.Ar
            | _ -> invalidArg "yobj" "cannot compare values of different types"

/// Type of morphisms between presheaves.
/// Overrides comparison so `Name` is ignored.
[<CustomEquality; CustomComparison; StructuredFormatDisplay("{Name}")>]
type Morphism<'A, 'S, 'T when 'A: comparison and 'S: comparison and 'T: comparison> =
    { Name: Name
      Mapping: Map<'A, Map<'S, 'T>>
      Dom: Presheaf<'A, 'S>
      Cod: Presheaf<'A, 'T> }
    override x.Equals(yobj) =
        match yobj with
        | :? (Morphism<'A, 'S, 'T>) as y -> x.Mapping = y.Mapping && x.Cod = y.Cod // Dom is automatically equal if Mapping is for valid morphisms but we need to distinguish between codomain and image.
        | _ -> false

    override x.GetHashCode() = hash x.Mapping

    interface System.IComparable with
        member x.CompareTo yobj =
            match yobj with
            | :? (Morphism<'A, 'S, 'T>) as y ->
                let c = compare x.Mapping y.Mapping
                if c <> 0 then c else compare x.Cod y.Cod
            | _ -> invalidArg "yobj" "cannot compare values of different types"

/// Type for a generic functor is just a container for an object map and an arrow map.
[<StructuredFormatDisplay("{Name}")>]
type GenericFunctor<'O, 'A> = { Name: Name; Object: 'O; Arrow: 'A }

/// Type for a (bi)heyting algebra of subobjects.
[<StructuredFormatDisplay("{Top}")>]
type Subalgebra<'A, 'S when 'A: comparison and 'S: comparison> =
    { Top: Presheaf<'A, 'S>
      Bot: Presheaf<'A, 'S>
      Subobjects: Set<Presheaf<'A, 'S>>
      LessEq: Relation<Presheaf<'A, 'S>, Presheaf<'A, 'S>> }
