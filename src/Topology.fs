/// Functions to compute topologies and sheaf operations.
[<RequireQualifiedAccess>]
module Topology

/// Checks if the given morphism Om -> Om is a topology.
let isTopology (j: Morphism<'A, Heart<'A>, Heart<'A>>): bool =
    let t = j.Category |> Truth.truth

    let (&&&) = Truth.internalAnd j.Category

    let cond1 j = j @ t = t
    let cond2 j = j @ j = j

    let cond3 j =
        j @ (&&&) = (&&&) @ (Morphism.product j j)

    cond1 j && cond2 j && cond3 j

/// Gives the set of modalities/Lawvere-Tierney topologies on a topos.
let topologies (cat: Category<'A>): Set<Morphism<'A, Heart<'A>, Heart<'A>>> =
    let Om = Truth.omega cat
    let hom = (Om, Om) ||> Morphism.hom
    hom |> Set.filter isTopology

/// Gives the closure of a subobject relative to a topology.
let closure (alg: Algebra<'A, 'S>) (j: Morphism<'A, Heart<'A>, Heart<'A>>) (U: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let chiS = U |> Truth.subobjectToChar alg.Top

    j @ chiS |> Truth.charToSubobject

/// Checks if a subobject is dense relative to a topology.
let isDense (alg: Algebra<'A, 'S>) (j: Morphism<'A, Heart<'A>, Heart<'A>>) (U: Presheaf<'A, 'S>): bool =
    U = closure alg j U
