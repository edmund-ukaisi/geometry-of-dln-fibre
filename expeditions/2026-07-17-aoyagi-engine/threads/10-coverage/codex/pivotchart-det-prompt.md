# Lean 4 / Mathlib v4.29: cleanest route for |det (fderiv (pivotChart i)) | = |u i|^(d-1)

Verify exact v4.29 lemma names; do NOT trust recalled names (a prior consult misremembered
`LinearMap.transvection` as being in Determinant.lean — it's LinearAlgebra/Transvection/Basic).

## The object
`d : ℕ`, `i : Fin d`. The max-modulus pivot blow-up chart on `Fin d → ℝ`:
`pivotChart i u = fun k => if k = i then u i else u i * u k`
(equivalently `Function.update (u i • u) i (u i)`).

## Goal
`|(fderiv ℝ (pivotChart i) u).det| = |u i| ^ (d - 1)`  (ContinuousLinearMap.det; d ≥ 1).

The Jacobian at u: row i = e_i; row k≠i = u_k • e_i + u_i • e_k. So (reindexing i to first) it is
block lower-triangular `[[1, 0], [col, u_i • I_{d-1}]]`, det = 1 · u_i^(d-1). (For u_i = 0, both sides
are 0 when d ≥ 2; d = 1 gives u_i^0 = 1 and det = 1.)

## Questions (exact v4.29 names + a short skeleton)
1. **fderiv**: cleanest HasFDerivAt for `pivotChart i` with an explicit derivative CLM? Componentwise via
   `hasFDerivAt_pi`? component i is `u ↦ u i` (proj i); component k≠i is `u ↦ u i * u k`
   (deriv `u_k • proj i + u_i • proj k`). How to assemble the pi-derivative and get its `.det`?
2. **det**: cleanest route to `det = u_i^(d-1)`? Options: (a) convert to `Matrix` via
   `LinearMap.toMatrix' / toMatrix (Pi.basisFun ℝ (Fin d))`, reindex `i` to `0` with `Equiv.swap`/
   `Matrix.det_reindex...`, then `Matrix.det_fromBlocks_zero₁₂` (or `_zero₂₁`) with the `u_i • I` block
   (`Matrix.det_smul`, `Matrix.det_one`); (b) the matrix-determinant lemma with a scaling
   `det (c • I + w ⬝ eᵢᵀ)` (needs u_i ≠ 0 case-split — messier); (c) something cleaner. Which is least
   painful at v4.29, with EXACT lemma names (`Matrix.det_fromBlocks_zero₁₂`? `Matrix.det_reindexₐ`?
   `Matrix.det_smul`? and the `ContinuousLinearMap.det → LinearMap.det → Matrix.det` bridge
   `LinearMap.det_toMatrix`)?
3. Any diamond/instance pitfalls converting the pi-fderiv CLM to a matrix and taking det.
4. Is there a slicker route: recognizing `pivotChart i` as `(scaling by u_i) ∘ (something)` whose det
   composes, or via `Matrix.det_updateColumn`/`updateRow` on `u_i • 1`?
Give the recommended route as a lemma skeleton with exact names.
