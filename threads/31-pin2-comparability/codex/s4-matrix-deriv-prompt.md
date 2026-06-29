Lean 4 / Mathlib v4.29. I need to prove, at the origin, `HasStrictFDerivAt δ 0 0` where δ is a matrix-difference `T1' - T1` (and a similar `Y1' - Y1`), each entry a real-valued function of `q` in a finite-dim normed space `X`.

Setup at q=0: all "read" matrices vanish — `Y0(0)=0, Z1(0)=0, Y1(0)=0`, `A0(0)=A1(0)=1`, `P00(0)=1`, `T1(0)=0` (T1 is a core coordinate, itself ~linear, NOT vanishing-deriv). Matrices:
  K = Z1·P00⁻¹·Y0           (O(read²): Z1,Y0 each vanish)
  W = 1 + Z1·A1⁻¹·A0⁻¹·Y0   (W-1 is O(read²))
  S1 = T1 - Z1·A1⁻¹·Y1       (S1 - T1 = -Z1·A1⁻¹·Y1, O(read²))
  T1' = W⁻¹·[(1-K)·S1 + Z1·A1⁻¹·Y1 + Z1·A1⁻¹·A0⁻¹·Y0·T1]
  Y1' = Y1 + A0⁻¹·Y0·(T1 - T1')
GOAL: D(T1'-T1)(0) = 0 and D(Y1'-Y1)(0) = 0, entrywise (over ℝ).

I have these landed scalar atoms:
- `hasStrictFDerivAt_triple_mul_zero (g h w) : g 0 = 0 → w 0 = 0 → D(g·h·w)(0)=0` (3-factor, outer two vanish).
- `hasStrictFDerivAt_mul_of_right_zero (a b) : Db 0 = 0 → b 0 = 0 → D(a·b)(0)=0`.
- `hasStrictFDerivAt_mul_of_snd_zero (a b db) : b 0 = 0 → D(a·b)(0) = a 0 • db`.
- entrywise ContDiffAt of matrix mul/inv on det≠0 (`contDiffAt_matrix_mul_entry`, `contDiffAt_matrix_inv_entry_of_det_ne_zero`).
- `hasStrictFDerivAt_pi'` to descend to coordinates.

The matrix types are DEPENDENT (`Matrix (Fin (deepestM ...)) (Fin (deepestM ...)) ℝ`) so entrywise `Matrix.mul_apply` expansions and casts are fiddly.

QUESTION: Give me the cleanest Lean lemma sequence. Two candidate routes:
(A) Symbolically rewrite `T1' - T1 = (W⁻¹-1)·Br + (Br - T1)` where `Br = (1-K)S1 + Z1A1⁻¹Y1 + Z1A1⁻¹A0⁻¹Y0T1`, prove `Br - T1 = -K·S1 + (Z1A1⁻¹A0⁻¹Y0)·T1` by matrix `ring`-style algebra, then each summand is a matrix product with a factor that is O(read²) (vanishes with zero deriv at 0), so entrywise each is a sum of scalar products with ≥2 vanishing-deriv/value factors → `hasStrictFDerivAt_*_zero`.
(B) Build matrix-entry strict-fderiv lemmas: `D((A*B)_ij)(0)` when `A 0 = 1, B 0 = 0` equals `D(B_ij)(0)`; when `A 0 = 0` (and Da, Db exist), `D((A*B)_ij)(0) = 0` if also `B 0 = 0` OR ... — then track `D(T1')(0) = D(T1)(0)` structurally so the difference is 0.

Which route is less cast-pain over dependent Matrix types? Give the concrete matrix-entry strict-fderiv helper lemma statements + proofs (the `∑ k` over `Matrix.mul_apply`, `HasStrictFDerivAt.sum`, the product rule), and flag the `W⁻¹` handling (W⁻¹ = (W-1+1)⁻¹, W⁻¹(0)=1, ContDiffAt at 0 since det W(0)=1≠0; its deriv at 0 is -D(W)(0) = 0 since W-1 is O(read²)). Specifically: is `D(W⁻¹)(0) = 0` cleanly available (W⁻¹ entry = (det W)⁻¹·adjugate, with D(W-1)(0)=0)?
