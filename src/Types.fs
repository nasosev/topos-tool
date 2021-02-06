/// Core types. Auto-opened.
[<AutoOpen>]
module Types

// WARNING: the order or fields in a record or propositions in a conjunction may have a big performance impact!

/// Type of names.
[<StructuredFormatDisplay("{String}")>]
type Name = { String: string }

/// Type of arrows in a category between generic objects.
[<StructuredFormatDisplay("{Name}")>]
type Arrow<'A> = { Name: Name; Dom: 'A; Cod: 'A }

/// Type of a finite category with generic objects.
/// It is intended that `'A` is a single-case DU type, e.g. `type Sets = Sets of string`.
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

/// Type of a functor between finite categories. todo: override equality/compare for performance.
[<StructuredFormatDisplay("{Name}")>]
type Functor<'A, 'B when 'A: comparison and 'B: comparison> =
    { Name: Name
      Ob: Map<'A, 'B>
      Ar: Map<Arrow<'A>, Arrow<'B>>
      Dom: Category<'A>
      Cod: Category<'B> }

/// Type for a Semimonoidal category.
[<StructuredFormatDisplay("{Category.Name}")>]
type SemimonoidalCategory<'A when 'A: comparison> =
    { Cat: Category<'A>
      Multiplication: Functor<'A * 'A, 'A> }

/// Type for a monoidal category.
[<StructuredFormatDisplay("{Category.Name}")>]
type MonoidalCategory<'A when 'A: comparison> =
    { Cat: Category<'A>
      Mult: Functor<'A * 'A, 'A>
      Unit: 'A }

/// Type of a presheaf into homogenous sets of type `'S` containing object and arrow functions.
/// Overrides comparison so `Name` is ignored.
[<CustomEquality; CustomComparison; StructuredFormatDisplay("{Name}")>]
type Presheaf<'A, 'S when 'A: comparison and 'S: comparison> =
    { Name: Name
      Ob: Map<'A, Set<'S>>
      Ar: Map<Arrow<'A>, Map<'S, 'S>>
      Cat: Category<'A> }
    override x.Equals(yobj) =
        match yobj with
        | :? (Presheaf<'A, 'S>) as y -> (x.Ob = y.Ob && x.Ar = y.Ar && x.Cat = y.Cat)
        | _ -> false

    override x.GetHashCode() = hash x.Ob ^^^ hash x.Ar ^^^ hash x.Cat

    interface System.IComparable with
        member x.CompareTo yobj =
            match yobj with
            | :? (Presheaf<'A, 'S>) as y ->
                let c = compare x.Ob y.Ob
                if c <> 0 then c else compare x.Ar y.Ar
            | _ -> invalidArg "yobj" "cannot compare values of different types"

/// Alias for the figures (i.e. the type of the homogeneous sets) of truth objects.
type Heart<'A when 'A: comparison> = Presheaf<'A, Arrow<'A>>

/// Type of morphisms between presheaves.
/// Overrides comparison so `Name` is ignored.
/// `Category` field is ignored in comparisons for performance.
[<CustomEquality; CustomComparison; StructuredFormatDisplay("{Name}")>]
type Morphism<'A, 'S, 'T when 'A: comparison and 'S: comparison and 'T: comparison> =
    { Name: Name
      Map: Map<'A, Map<'S, 'T>>
      Dom: Presheaf<'A, 'S>
      Cod: Presheaf<'A, 'T>
      Cat: Category<'A> }
    override x.Equals(yobj) =
        match yobj with
        | :? (Morphism<'A, 'S, 'T>) as y ->
            x.Map = y.Map
            && x.Cod = y.Cod // Dom should automatically be equal but need to distinguish between codomain and image.
            && x.Cat = y.Cat
        | _ -> false

    override x.GetHashCode() = hash x.Map ^^^ hash x.Cod ^^^ hash x.Cat

    interface System.IComparable with
        member x.CompareTo yobj =
            match yobj with
            | :? (Morphism<'A, 'S, 'T>) as y ->
                let c = compare x.Map y.Map
                if c <> 0 then c else compare x.Cod y.Cod // Comparing the `Category` field has a bad performance cost.
            | _ -> invalidArg "yobj" "cannot compare values of different types"

/// Type for a generic functor is just a container for an object map and an arrow map.
[<StructuredFormatDisplay("{Name}")>]
type GenericFunctor<'O, 'A> = { Name: Name; Object: 'O; Arrow: 'A }

/// Type for a (bi)Heyting algebra of subobjects.
[<StructuredFormatDisplay("{Top}")>]
type Algebra<'A, 'S when 'A: comparison and 'S: comparison> =
    { Top: Presheaf<'A, 'S>
      Bot: Presheaf<'A, 'S>
      Subobjects: Set<Presheaf<'A, 'S>>
      LessEq: Relation<Presheaf<'A, 'S>, Presheaf<'A, 'S>> }
