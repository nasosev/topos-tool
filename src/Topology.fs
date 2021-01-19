/// Functions to compute modalities and sheaf operations.
[<RequireQualifiedAccess>]
module Topology

// Checks if the given morphism Om -> Om is a modality.
let isModality (cat: Category<'A>) (j: Morphism<'A, Heart<'A>, Heart<'A>>): bool =
    let T = cat |> Truth.truth |> Morphism.image
    let (&&&) = Truth.internalAnd cat

    let cond1 j = Morphism.apply j T = T
    let cond2 j = Morphism.compose j j = j

    let cond3 j =
        Morphism.compose j (&&&) = Morphism.compose (&&&) (Morphism.product j j)

    cond1 j && cond2 j && cond3 j

/// Gives the set of modalities/Lawvere-Tierney topologies on a topos.
let modalities (cat: Category<'A>): Set<Morphism<'A, Heart<'A>, Heart<'A>>> =
    let Om = Truth.omega cat
    let hom = (Om, Om) ||> Morphism.hom
    hom |> Set.filter (isModality cat)
