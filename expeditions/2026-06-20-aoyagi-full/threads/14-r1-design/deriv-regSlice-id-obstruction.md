# `deepestEPivot_regSlice_fderiv_id` — the opaque-pack obstruction (deriv-fm, 2026-06-23)

**Finding (adjudicated, decorrelated; Codex unavailable — AISI git-ssh hang).** The isolated obligation
that cobuild's `deepestEPivot_deriv` assembly (`DeepestGaugeConstruction.lean`, @da45d78/@d3c6b7a) reduces
to —

    deepestEPivot_regSlice_fderiv_id :
      HasStrictFDerivAt (fun r0 => deepestEPivot H r hr hL (r0, 0))
        (ContinuousLinearMap.id ℝ (Fin (deepestNReg H r) → ℝ)) 0

— is **NOT provable as stated** (and is underdetermined / likely false) against the CURRENT definitions,
because it asserts the composite of two INDEPENDENT opaque `Fintype.equivFin` bijections equals literally
the identity.

## Why (the composition)

The gauge-zero reg-slice derivative is

    d[r0 ↦ deepestEPivot(r0, 0)]|_0  =  regResidualPack-CLM ∘ (idempotent sandwich) ∘ regGaugeSlotRead|_reg-CLM

- `regGaugeSlotRead|_reg` (= `regGaugeSlotEquiv` restricted to the reg slot, via `regGaugeIdxSplit.symm ∘ inl`)
  maps `Fin nReg → ℝ` into the per-layer X/Y/Z entries of `RegGaugeIdx`. `regGaugeIdxSplit`
  (`DeepestSplitReindex.lean:235`) is `(Fintype.equivFin (RegGaugeIdx)).trans …` — **opaque**.
- the idempotent sandwich keeps `(Σ_s δX_s, δY_L, δZ_1)` (the surviving blocks at the deepest, g213/#91).
- `regResidualPack` (`DeepestGaugeConstruction.lean:357`) maps the three residual blocks
  `(r×r) ⊕ (r×M_L) ⊕ (M_0×r)` back to `Fin nReg`. It is `(finCongr _).trans (Fintype.equivFin _).symm` —
  a **pure cardinality bijection, zero characterizing API**, an INDEPENDENT opaque choice on a DIFFERENT type.

The two opaque `Fintype.equivFin` witnesses are arbitrary and unrelated, so their composite is some
arbitrary permutation-composite — provably `= id` only if they happen to align, which is not controllable
from the definitions. The assembly's `regStraightenTotalCLM_equiv_of_regBlock_id`
(`DeepestRegAbsorbIFT.lean:512`) requires `D_E.comp regInCLM = id` LITERALLY (no merely-`iso` variant).

Worse than non-`id`: even **injectivity** of the reg-slice derivative is not guaranteed — if the opaque
`regGaugeIdxSplit` routes two distinct reg coordinates into X-entries summed by `Σ_s δX_s`, the reg-block
is non-injective. So no choice of existential `D_E` in `deepestEPivot_deriv` escapes: the headline needs
the alignment regardless of packaging.

## What this is, precisely

This is the **opaque-pack alignment**, the g239 "`_deriv` obstruction" and the #120 "boundary-generator
equiv (the (b) fix for dE(0)=fst)". #120 is marked COMPLETED in the task list, but the DEFINITIONS
`regResidualPack` / `regGaugeIdxSplit` are STILL the opaque `Fintype.equivFin` on the base — the #120
DESIGN was never wired into the defs. The lemma becomes attemptable (the genuine #91 idempotent-sandwich
content, ~150-250 lines) only AFTER that wiring.

## The fix (definition-layer, not a leaf proof)

The honest unblock is to replace the opaque splits with SEMANTIC ones so `pack ∘ sandwich ∘ read|_reg = id`
by construction:

- `regGaugeIdxSplit` (in `DeepestSplitReindex.lean`) must put the boundary generators
  (`X` over all layers summed, `Y_last`, `Z_first`) in the `Fin nReg` half and the interior gauge X/Y/Z in
  the `Fin nGauge` half — NOT an arbitrary `Fintype.equivFin`. This ripples through the measure-preserving
  `split` (the reindex must stay `det = ±1`) and `gaugeSlotRead`.
- `regResidualPack` (in `DeepestGaugeConstruction.lean`) must align with that reg half: the residual block
  `(P11−I, P12, P21)` coordinates map to the same `Fin nReg` entries the reg slot carries.

This is a definition refactor of the core slot-grouping infrastructure with downstream MP/continuity
obligations — owned by the single-writer of those defs, NOT a standalone analytic lemma. The pp2
"coordinate-correspondence cert" cobuild's docstring names IS this alignment.

## Status

ESCALATED to controller 2026-06-23. Recommendation: do the #120 explicit-pack wiring (a
`regGaugeIdxSplit`/`regResidualPack` definition change) BEFORE attempting the analytic lemma; grinding the
lemma as-stated will wall (it is a definition change, not a proof). deriv-fm available for the wiring +
the #91 sandwich proof on top, if authorized to touch those defs.

Banked closable infra (the alt-assembly path that DOESN'T need the literal-`id` route, if useful):
`fm/deriv-pin1` @fb174f0 — `DeepestFramedDeriv.lean` (regShearN/regShearEquiv square-zero-shear ≃L algebra
+ ContDiff-free strict-deriv + the conditional `deepestEPivot_deriv_of_shear`), reviewer-PASS, clean-three.
