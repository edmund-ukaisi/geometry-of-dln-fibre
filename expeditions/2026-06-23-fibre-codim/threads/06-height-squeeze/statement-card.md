# Tide F2 (height-squeeze) — statement card

## Verdict
**NO-GO on the full Lemma 4.5/4.6 codimension identity** at Mathlib v4.29 (decorrelated Codex
confirmed). The proposed two-inequality sandwich has a sign error (Krull bounds height *above*) and
`mult` is not flat (fibre dimension jumps as rank drops), so the going-down additivity does not apply
at the closed point. The full identity needs a rank-chart local-trivialization build absent from
v4.29 and stays **Cited** (`DLN.BundleShiftInterface.cited_bundle_shift`). The reachable half is
landed below.

## Landed lower bound

> **Claim.** For `B` of rank `r`, the geometric codimension of the closed rank-`≤ r` product locus
> `Σ̄^r = productRankLocusLE d r` is at most that of the fibre `mult⁻¹(B)`:
> `codimRepCanonical Σ̄^r ≤ codimRepCanonical (mult⁻¹ B)` — the `C ≤ codim(mult⁻¹ B)` half of
> Lehalleur–Rimányi Lemma 4.5/4.6.
>
> - **Lean:** `DLNFibre.Core.codimRepCanonical_productRankLocusLE_le_codimRepCanonical_fibre`
>   (`lean/DLNFibre/Core/FibreCodim.lean` @ `714dcf3932ae482ff27f267fc8649d3ae2b60453`)
> - **Gloss.** Over any field `k`, for a dimension vector `d` and a target matrix `B` with
>   `B.rank = r`, the height of the vanishing ideal of `Σ̄^r` (its geometric codimension) is `≤` the
>   height of the vanishing ideal of the fibre `{A | mult d A = B}`. Follows from `mult⁻¹ B ⊆ Σ̄^r`
>   (`fibre_subset_productRankLocusLE`) plus inclusion-monotonicity of `codimRepCanonical`
>   (`codimRepCanonical_mono`: a larger set has a smaller vanishing ideal, and `Ideal.height` is
>   monotone).
> - **Proved.** The inequality `codim Σ̄^r ≤ codim(mult⁻¹ B)` unconditionally, `[Field k]` only.
> - **Assumed.** `B.rank = r` (so the fibre lands in `Σ̄^r`). No `[IsAlgClosed]`/`[CharZero]`.
> - **Cited.** none (this half is pure inclusion monotonicity).
> - **Deferred.** The full Lemma 4.5/4.6 *equality* and the shift `+ r(d_0+d_N−r)` — needs the
>   exact-rank fibre-bundle / rank-chart trivialization (paper's Lie-group submersion), absent from
>   v4.29; carried as `DLN.BundleShiftInterface.cited_bundle_shift`. The other inequality
>   `codim(mult⁻¹ B) ≤ C + r(d_0+d_N−r)` is also NOT proved here.
> - **Status.** sorry-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## Supporting lemmas (same module, same SHA)
- `codimRepCanonical_mono` — `Z ⊆ Z' → codimRepCanonical Z' ≤ codimRepCanonical Z`.
- `fibre_subset_productRankLocusLE` — `B.rank = r → fibre d B ⊆ productRankLocusLE d r`.

## Witness
`(2,2,2)`, `B = 0`, `r = 0` over `AlgebraicClosure ℚ`: the bound `codim Σ̄^0 ≤ codim mult⁻¹(0)` fires
(and is tight there, since `mult⁻¹(0) = Σ̄^0`).

## Roadmap (replacing the dead sandwich)
The full identity's gating step is a `Core.RankChartTrivialization` build: reduce rank-`r` `B` to
`diag(I_r,0)`; build a pivot chart `U = D(Δ)` of dimension `δ = r(d_0+d_N−r)` in `Mat^{rk≤r}`; the
explicit section `D = C A⁻¹ B`; prove `mult⁻¹(U) ∩ Σ̄^r ≅ U × mult⁻¹(E)` as affine algebras; then
flat ⟹ `Algebra.HasGoingDown` ⟹ `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` per top
component, with the minimum over components via Brick A's minimal-prime / orbit-component machinery.
