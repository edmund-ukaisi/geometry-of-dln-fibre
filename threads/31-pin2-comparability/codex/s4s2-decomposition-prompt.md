I am filling 3 Lean 4 (Mathlib v4.29) `sorry` leaves in a diffeo-bridge proof. The map under study is a "joint (T1,Y1) action" `psiSplitRawL2Core : DeepestSplit → DeepestSplit` where `DeepestSplit = (Fin nReg → ℝ) × ((Fin nCore → ℝ) × (Fin nGauge → ℝ))` (a nested product of finite real coordinate spaces). The correction `δ = psiSplitRawL2Core q - q` (componentwise Pi/Prod subtraction).

`psiSplitRawL2Core q` is built as `(regspec'.1, (core', regspec'.2))` where:
- `core' = paramsEquivFlat M (Function.update ((paramsEquivFlat M).symm q.2.1) lastLayer T1')` — i.e. re-encode the core tuple, editing ONLY the last layer to a new matrix `T1'`.
- `regspec' = (regGaugeSlotEquiv).symm g'` where `g'` edits only the last-layer Y-tag of `g = regGaugeSlotEquiv (q.1, q.2.2)` to a new matrix `Y1'`.
- `T1'` and `Y1'` are matrix expressions: `T1' = W⁻¹·[(1-K)·S1 + Z1·A1⁻¹·Y1 + Z1·A1⁻¹·A0⁻¹·Y0·T1]`, `Y1' = Y1 + A0⁻¹·Y0·(T1-T1')`, where A0=1+readX(0), A1=1+readX(last), Y0=readY(0) reindexed, Z1=readZ(last), Y1=readY(last), T1=core read at last layer, P00=A0·A1+Y0·Z1, K=Z1·P00⁻¹·Y0, W=1+Z1·A1⁻¹·A0⁻¹·Y0.

ALL reads (readX/Y/Z) and the core read are LANDED as entrywise `ContDiff ℝ ⊤` (via a landed CLE `regGaugeSlotCLE` / `paramsEquivFlatCLE`). `paramsEquivFlat M` IS a CLE (`paramsEquivFlatCLE`). The matrix-inverse-entry / matrix-mul-entry `ContDiffAt` on det≠0 are landed (`contDiffAt_matrix_inv_entry_of_det_ne_zero`, `contDiffAt_matrix_mul_entry`). At `q=0` all reads vanish (readX/Y/Z 0 = 0), so A0=A1=1, Y0=Z1=Y1=T1=0, P00=1, K=0, W=1.

TWO smoothness leaves:
- S2: `ContDiffAt ℝ ⊤ δ q` for `q ∈ tsupport(cutoffBump)` (a det-≠0 unit locus where all 1+readX, W, P00 are invertible).
- S4: `HasStrictFDerivAt δ 0 0` (strict derivative of δ at the origin is 0), because δ is `O(read³)` — each correction block is a product with ≥2 vanishing-at-0 read factors.

QUESTION: What is the CLEANEST decomposition to prove S2 and S4 through the encode/decode/Function.update/match-on-g' cast layers, REUSING the landed entrywise primitives? Specifically:
1. To get `ContDiffAt`/`HasStrictFDerivAt` of the FULL `DeepestSplit`-valued map, is it best to reduce via `contDiffAt_pi` / `hasStrictFDerivAt_pi'` to the honest `Fin n → ℝ` coordinate level on each of the 3 product slots, then show each output coordinate is a `paramsEquivFlat`/`regGaugeSlotEquiv.symm` (CLE) applied to a `Function.update`/`match` of matrix-entry functions? 
2. For the core slot `core'`: since `paramsEquivFlat M` is a CLE, `core'` as a function of q is `(CLE) ∘ (Function.update (decode q.2.1) last T1')`. `Function.update f last v` at coordinate `s`: is `s=last ? v : f s`. Is the right move `funext`/`Function.update` case-split, OR is there a slicker "the whole tuple is ContDiff because each layer-block is ContDiff and update is a finite pattern" lemma? 
3. For S4 the derivative VALUE is 0 (fully determined). The key fact: `T1'` and `Y1'-Y1` are each O(read³)/O(read²) — but actually T1' is NOT small (T1'≈T1 to first order? No: at 0, T1=0 so T1'=0; the DELTA T1'-T1 must be O(read·...)). Is the right move to compute `δ`'s core-last-block = `T1' - T1` and show its strict fderiv at 0 is 0 via the landed `hasStrictFDerivAt_triple_mul_zero` generalized, treating W⁻¹ etc as ContDiffAt factors that are ≈1 at 0 (so their product structure gives ≥2 vanishing read factors)?

Give me a concrete Lean proof skeleton (lemma decomposition) for S2 and S4 that minimizes cast thrash. Flag any place where `Function.update` through a CLE or the `match`-on-RegGaugeIdx `g'` will fight Lean's elaborator, and the idiom to defeat it.
