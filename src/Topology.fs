/// Functions to compute topologies and sheaf operations.
[<RequireQualifiedAccess>]
module Topology

/// Checks if the given morphism Om -> Om is a topology.
let isTopology (j: Morphism<'A, Heart<'A>, Heart<'A>>): bool =
    let T =
        j.Category |> Truth.truth |> Morphism.image

    let (&&&) = Truth.internalAnd j.Category

    let cond1 j = Morphism.apply j T = T
    let cond2 j = Morphism.compose j j = j

    let cond3 j =
        Morphism.compose j (&&&) = Morphism.compose (&&&) (Morphism.product j j)

    cond1 j && cond2 j && cond3 j

/// Gives the set of modalities/Lawvere-Tierney topologies on a topos.
let topologies (cat: Category<'A>): Set<Morphism<'A, Heart<'A>, Heart<'A>>> =
    let Om = Truth.omega cat
    let hom = (Om, Om) ||> Morphism.hom
    hom |> Set.filter isTopology

/// Gives the closure of a subobject relative to a topology.
let closure (alg: Algebra<'A, 'S>) (j: Morphism<'A, Heart<'A>, Heart<'A>>) (S: Presheaf<'A, 'S>): Presheaf<'A, 'S> =
    let chiS = S |> Truth.subobjectToChar alg.Top

    (j, chiS)
    ||> Morphism.compose
    |> Truth.charToSubobject

/// Checks if a subobject is dense relative to a topology.
let isDense (alg: Algebra<'A, 'S>) (j: Morphism<'A, Heart<'A>, Heart<'A>>) (S: Presheaf<'A, 'S>): bool =
    S = closure alg j S
