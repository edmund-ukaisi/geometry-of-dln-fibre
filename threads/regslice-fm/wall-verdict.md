# #82-deriv reg-slice = id — WALL VERDICT (regslice-fm, 2026-06-23)

Target: `deepestEPivot_regSlice_fderiv_id`
`HasStrictFDerivAt (fun r0 => deepestEPivot H r hr hL (r0, 0)) (ContinuousLinearMap.id ℝ _) 0`.

Branch `fm/regslice-id` @f1ff84c (off d9c74e1). File
`lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceId.lean` (standalone, build GREEN, one documented sorry).

## Verdict: TRUE-under-convention, NOT provable as stated — needs the cobuild-side structured equiv

The statement is **mathematically true** but **not provable in Lean from the current definitions**, because
it depends on a coordinate convention that the opaque `Fintype.equivFin` packings do not realise.

### The math is correct and confirmed (g211, this thread)

Re-ran the g213/#91 cert script `g211_dE0_identity.py` (origin/g213-pin1-de0): the reg-slice derivative
is the #91 idempotent collapse `dE = (Σ_s dX_s, dY_L, dZ_1)`, and the pivot-Jacobian w.r.t. the BOUNDARY
generators `(X_first for E00, Y_last for E01, Z_first for E10)` is exactly the identity, |det|=1, for every
config swept (r=1/2/3, depth ≤5, asymmetric/degenerate widths) — 8/8 here, 40/40 in the cert. So the
intended object's reg-slice derivative IS id **provided the reg slot = `(X_first, Y_last, Z_first)` and the
interior `X_s` (s≠first via the Σ), interior `Y_s`/`Z_s` live in the gauge slot.**

### Why it is not reachable in Lean

`deepestEPivot (r0,0)`'s reg input `r0 : Fin nReg → ℝ` is distributed over the per-layer `RegGaugeIdx =
Σ_s (X_s ⊕ Y_s ⊕ Z_s)` (ALL L layers) via `regGaugeSlotEquiv` = OPAQUE `regGaugeIdxSplit.symm ∘ inl`. The
output is packed by `regResidualPack` onto the three boundary blocks `(X-corner r×r) ⊕ (Y_last) ⊕ (Z_first)`.

- `regGaugeIdxSplit := (Fintype.equivFin RegGaugeIdx).trans …` and
  `regResidualPack := … .trans (Fintype.equivFin _).symm` are `Fintype.equivFin` on DIFFERENT types — no
  shared structure, no compatibility lemma, no equation lemma. PROBED: `simp`/`unfold` cannot reduce
  `regGaugeIdxSplit idx` at all (no computation rule for `Fintype.equivFin`).
- Cardinality check (this thread): for L≥2, `nGauge>0` and interior `Y_s`/`Z_s` blocks exist. The reg-slice
  middle step SUMS the X-blocks and DROPS interior `Y_s` (s≠L)/`Z_s` (s≠1). If the opaque `equivFin` sends
  any reg coordinate onto a dropped interior block, the reg→reg map is rank-deficient → not even invertible.
  So under the current defs the statement is not just unprovable but not generically true.

Dimensions match by design (`deepestNReg = r(H_0+H_L−r) = r² + r(H_L−r) + (H_0−r)r` = boundary count), so the
object exists — the `equivFin` orderings simply do not realise the boundary convention.

## The fix (cobuild-side; not my file) — and the #120 history

This is the obligation of **task #120** ("Structure the reg slot: regGaugeIdxSplit opaque equivFin →
boundary-generator equiv"). #120 was closed "SUPERSEDED, NOT done" on the reasoning that PIN1 only needs the
FULL `_deriv` to be an invertible CLE (the shear `[[I,Σ],[0,I]]`), not `=fst`. But cobuild's `_deriv`
assembly still proves `D_E.comp regInCLM = id` (the reg-BLOCK = id, the `[I, …]` top row of the shear) USING
exactly this lemma. So the boundary-correspondence obligation #120 named did NOT vanish — it re-surfaced as
`deepestEPivot_regSlice_fderiv_id`. #120 was closed prematurely w.r.t. the reg-block.

**Minimal fix:** make `regGaugeIdxSplit`'s reg-half and `regResidualPack` the SAME explicit structured
bijection that sends the reg slot to `(X_first, Y_last, Z_first)` and the interior `X_s/Y_s/Z_s` to gauge —
i.e. build `regGaugeIdxSplit` from a NAMED `Equiv` (e.g. a `Fin`-sum decomposition of `RegGaugeIdx` that
separates the boundary triple from the interior + summed-X), with `regResidualPack` its boundary restriction.
Both live in cobuild's `DeepestSplitReindex.lean` / `DeepestGaugeConstruction.lean`.

A pp2 coordinate-correspondence cert ALONE does not unblock — there is nothing to prove a cert against while
the equivs stay `Fintype.equivFin`. The cert must come AS (or with) the redefinition. Once the two packings
are the matching structured equiv, this lemma fills in ~30–50 LoC: `hasStrictFDerivAt_pi'` per output coord,
`hasStrictFDerivAt_prod_entry` for the Leibniz product derivative, the idempotent-sandwich collapse
(`prodAux_framedParamsReg_zero` + `fromBlocks_blockdiag_idem`), and the now-exposed boundary read = `proj i`.
