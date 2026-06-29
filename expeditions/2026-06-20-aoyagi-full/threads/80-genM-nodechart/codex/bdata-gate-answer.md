1. Q1 verdict: **YES, conditional.**  
Assumption I cannot verify from the description: `active \ {p₀}` are exactly coordinates used in the residual `Rmat/Rfin` blocks, and those coordinates are not read unmultiplied by `Bmat`, `Nblk`, or other chart scaffolding. Under that assumption, `phi` is constant on `pivotBlowupOn` fibres: off `x p₀ = 0` the map is injective, and on `x p₀ = 0` the residual terms `u • Rmat` and `u • Rfin` vanish. Also, as defined, there is no pivot-sign two-to-one ambiguity because the pivot coordinate itself is fixed. Then `B` can be the direct boundary decoder reading already-scaled residual coordinates, with the `u`-free determinant supplied by a separate boundary determinant proof.

2. Q2 verdict: **(b) shape-level [BData sidesteps].**  
The F1 refutation kills the old claim that the whole chart is a `composeFold` of disjoint factors. It does not by itself kill factoring out the radial blow-up, because `BData.B` is arbitrary. But trying to instantiate `B` as the refuted disjoint `composeFold` would reintroduce the same coupling bug.

3. Q3: **V-CONSTRUCTIBLE-HARD.**  
Cheapest Lean test before any cold build: prove the per-boundary algebra lemma
`Cgen (x p₀) ... k x = Cboundary ... k (pivotBlowupOn active p₀ x)`
including the leaf case, by expanding only the transition matrices. If this fails because an active coordinate is read unscaled, stop: `BData` is vacuous. Recommended route: define `B` directly as the boundary decoder on blown-up coordinates, prove `hmap` from those matrix equalities, and prove `hdet` via the existing staircase/fused-frame determinant machinery, not via the dead disjoint-factor fold.