**Verdict:** `hdet` is **not banked-reducible for the actual radial-1 boundary chart** merely from `foldDerivList_abs_det_perBoundary`.

The banked fold lemmas prove the determinant of the synthetic map `composeFold BFactors`:

- `composeFold_hasFDerivAt` gives the derivative of `composeFold fs`.
- `foldDerivList_abs_det_perBoundary` gives the determinant of that folded derivative.

They do **not** prove that the actual `B` in `φ = B ∘ pivotBlowupOn` has that derivative. In `BData`, `DB` is syntactically arbitrary, but `hasDB : HasFDerivAt B DB ...` pins it to the actual derivative. So choosing `DB := (foldDerivList BFactors ...).prod` is legal only after proving `HasFDerivAt B DB`, which is essentially the missing derivative/value bridge. Determinant equality alone is not enough.

Radial-1 removes the scalar `u`; it does **not** remove the `C_{s+1}` accumulator coupling. So `B = composeFold BFactors` still needs a real map-level or derivative-level proof. The F1 refutation does not automatically refute every possible carefully-overlapping accumulator fold, but it absolutely refutes treating the fold telescope as already applicable to the actual chart.

The locality route is logically valid, but not “free”: prove `B`’s own fderiv is block/stair triangular, then identify the diagonal blocks with Schur/LDU engines. That sidesteps `composeFold`, but it is the fused-frame/staircase determinant work in another package.

The single-grading `blockTri` route is also suspect for the real chart: the repo has a banked obstruction that input chart-boundary blocks and output `Params` layers have different per-layer counts. So the sound form is the **two-sided staircase / determinant-level local route**, not a naive `toSquareBlock` under one grading.

Bottom line on routes:

1. **Full BData via composeFold-hdet:** only least work if `B = composeFold BFactors` is actually proved. Currently not banked; this is the disputed hard bridge.
2. **Full BData via locality-hdet:** sound, but adds `hmap` on top of the actual-fderiv determinant work.
3. **No-hmap stairConj / two-sided stairConj:** sound packaging of the real obligation; likely least among your four.
4. **No-hmap blockTri:** only sound after upgrading to a two-sided/rectangular or column-factor formulation; plain single-grading blockTri is blocked.

So the formaliser’s “don’t build full `BData`” recommendation is **sound**, but “sheds work” should be read narrowly: it sheds the `hmap`/`B = composeFold` bridge, while relocating the determinant proof to the actual Jacobian. It does not make the determinant obligation disappear.