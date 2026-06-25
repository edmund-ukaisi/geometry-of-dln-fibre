SET-LEVEL ESCAPES the circularity; the residual wall is the absent reducible product/principal-open dimension package, especially `varietyDim (X × Y) = varietyDim X + varietyDim Y` or the tailored `dim (A[base]_det) = dim A + δ`, about 3 tailored modules, 5-ish for a general product theorem.

**Q1: Crux**
Yes, the set equality is genuinely pointwise linear algebra. It is not equivalent to the strict ideal inclusion.

On the pivot chart, for a block matrix
`M = [[Δ, B12], [B21, B22]]` with `det Δ ≠ 0`,

`rank M ≤ r` iff `B22 - B21 Δ⁻¹ B12 = 0`.

This follows by multiplying by invertible block matrices and reducing to a block diagonal/Schur-complement form. No nilpotents, no radical membership, no reducedness. Then equivariance of `mult` under endpoint base-change gives `mult(endpointGauge(A) • A) = E`, so the normalized point lies in the fibre. The inverse direction is the same calculation reversed.

What this proves algebraically is equality of closed point sets, hence equality of vanishing ideals/radicals by Nullstellensatz. It does not prove equality of the original generator ideals. The old circular step needed scheme-level descent through a non-radical presentation. The set-level proof only sees the reduced closed set.

**Q2: Product Dimension**
Mathematically, yes:

`dim (X × Y) = dim X + dim Y`

for affine algebraic sets over algebraically closed `k`, reducible included. Reducibility is handled by irreducible components:

`dim (X × Y) = max_{i,j} dim (X_i × Y_j) = max_i dim X_i + max_j dim Y_j`.

Lean v4.29: I do not see a ready theorem of this form. I also do not see `ringKrullDim (A ⊗[k] B) = ringKrullDim A + ringKrullDim B`, nor a tensor-product trdeg theorem. `trdeg_add_eq` exists, but it is tower additivity, not product/tensor additivity.

Cheaper route for this chart: since the base factor is explicit Schur coordinates, you can avoid the fully general product theorem. Prove

`O(base × F) ≃ O(F)[δ base variables]_det`

then use Mathlib’s present `MvPolynomial.ringKrullDim_of_isNoetherianRing` for the `+ δ` part, plus a principal-open localization no-drop lemma. This is still real work, but it is narrower than arbitrary reducible product dimension.

**Q3: Localization Dimension**
Mathlib v4.29 does not appear to have a packaged `ringKrullDim_localization` theorem. It does have useful pieces: `IsLocalization.orderIsoOfPrime`, `IsLocalization.height_map_of_disjoint`, `IsLocalization.AtPrime.ringKrullDim_eq_height`, and the project has finite-type affine-domain equidimensionality such as `height_eq_ringKrullDim_of_isMaximal`.

Cheapest route for irreducible affine `A` and nonempty `D(f)`:

1. `dim A_f ≤ dim A` from the prime correspondence/order embedding for localization.
2. Choose a closed point/maximal ideal `m` with `f ∉ m`.
3. Height is preserved after localizing: `height (mA_f) = height m`.
4. For finite-type domains over a field, `height m = ringKrullDim A`.
5. Hence `dim A_f ≥ dim A`.

So Q3 is reachable, not the main conceptual wall. For reducible rings, you must ensure `f` avoids at least one top component, or avoids every top component if you want density on all top components.

**Q4: Glue + Density**
Finite union dimension is mathematically standard and reachable, but not free. You need a lemma like:

`varietyDim (⋃ i, Z i) = max_i varietyDim (Z i)`

for finite nonempty families. Mathlib has Spec zero-locus facts such as `PrimeSpectrum.vanishingIdeal_union`, `PrimeSpectrum.vanishingIdeal_iUnion`, `PrimeSpectrum.zeroLocus_inf`; for `MvPolynomial.vanishingIdeal` on point sets, the union identity is easy from `mem_vanishingIdeal_iff`, but the dimension-max theorem still needs order/minimal-prime bookkeeping.

The density step is separate: each top component of `Σ̄^r` must meet some rank-`r` pivot chart. That is not reducedness, but it is a real component/generic-rank statement. If already available from the θ/component machinery, glue is manageable; otherwise budget another component/density module.