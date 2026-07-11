<task>
You are giving a DECORRELATED second opinion for an adversarial fidelity/soundness
review of a Lean 4 (Mathlib) module. Reason about the MATHEMATICS independently;
do not assume the Lean proof is correct.

Two theorems are under audit (informal claims stated first, then the Lean).

INFORMAL CLAIM 1 (single-minor Gram lower bound):
For a real b×q matrix M and any injective column selector S : Fin b → Fin q, the
SQUARE of the b×b column-minor det(M[:, S]) is ≤ det(M Mᵀ). (Should be the
"drop all but one nonnegative Cauchy–Binet term" fact: det(M Mᵀ) = Σ_S minor_S².)

INFORMAL CLAIM 2 (PSD-cone determinant monotonicity):
If A is positive semidefinite and B − A is positive semidefinite (Loewner A ⪯ B),
then det A ≤ det B, for general square real matrices.

Here is the Lean module verbatim:

```lean
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJGramMinorBound` — the single-minor Gram lower bound

For a `b × q` real matrix `M` and any injective column selector `S : Fin b → Fin q`, the Gram
determinant dominates the square of the corresponding `b × b` column minor:

    (M.submatrix id S).det ^ 2  ≤  (M * Mᵀ).det.

This is the elementary consequence of Cauchy–Binet `det(M Mᵀ) = Σ_S minor_S²` (drop all but one
nonnegative term), but Cauchy–Binet is **absent** from Mathlib v4.29, so the proof routes through
the Loewner order instead:

* `N Nᵀ ≤ M Mᵀ` (Loewner), because the difference `M Mᵀ − N Nᵀ` is positive semidefinite — its
  quadratic form is `Σ_j (xᵥ*M)_j² − Σ_l (xᵥ*M)_{S l}²`, a sum over a subset of a nonnegative sum;
* `det` is monotone on positive semidefinite matrices (`det_le_det_of_posSemidef_le`, built here
  from the eigenvalue/spectrum API, since it is also absent from Mathlib);
* `det(N Nᵀ) = det(N)²`.

`det_le_det_of_posSemidef_le` is general and Mathlib-worthy; its `1 ≤ det` core
(`one_le_det_of_one_le`) uses the spectrum-shift `μ − 1 ∈ spectrum(C − 1)` and the fact that a
positive-semidefinite matrix has nonnegative spectrum.

The weight-control obligation this bound serves (integrability of `det(Q_b Q_bᵀ)^{−a/2}` over the
good stratum) is in `expeditions/2026-06-20-aoyagi-full/threads/genm-wtint/verdict.md`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The inverse Gram square-root normaliser** (`W = A^{−1/2}` from `CFC.sqrt`), inlined here to
keep this module self-contained. For a positive-definite `A`, there is a symmetric `W` with
`W A Wᵀ = 1`, `det W ≠ 0`, and `|det W| = (√ det A)⁻¹`. (This is the banked
`RouteMSJGramSqrt.exists_gram_normalizer`; the controller may dedupe on integration.) -/
private theorem gram_normalizer (A : Matrix n n ℝ) (hA : A.PosDef) :
    ∃ W : Matrix n n ℝ,
      Wᵀ = W ∧ W * A * Wᵀ = 1 ∧ W.det ≠ 0 ∧ |W.det| = (Real.sqrt A.det)⁻¹ := by
  classical
  have hAps : A.PosSemidef := hA.posSemidef
  have hAdet_pos : 0 < A.det :=
    lt_of_le_of_ne hAps.det_nonneg
      (Ne.symm ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit).ne_zero)
  have hSps : (CFC.sqrt A).PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hST : (CFC.sqrt A)ᵀ = CFC.sqrt A := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hSps.isHermitian.eq
  have hSsq : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A
  have hSdet : (CFC.sqrt A).det = Real.sqrt A.det := by
    rw [hAps.det_sqrt, RCLike.sqrt_real]
  have hSdet_pos : 0 < (CFC.sqrt A).det := by rw [hSdet]; exact Real.sqrt_pos.mpr hAdet_pos
  have hSunit : IsUnit (CFC.sqrt A).det := (isUnit_iff_ne_zero).mpr (ne_of_gt hSdet_pos)
  refine ⟨(CFC.sqrt A)⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.transpose_nonsing_inv, hST]
  · rw [Matrix.transpose_nonsing_inv, hST]
    calc (CFC.sqrt A)⁻¹ * A * (CFC.sqrt A)⁻¹
        = (CFC.sqrt A)⁻¹ * (CFC.sqrt A * CFC.sqrt A) * (CFC.sqrt A)⁻¹ := by rw [hSsq]
      _ = 1 := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul (CFC.sqrt A) hSunit, Matrix.one_mul,
            Matrix.mul_nonsing_inv (CFC.sqrt A) hSunit]
  · rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, hSdet]
    exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hAdet_pos))
  · rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, hSdet, abs_inv,
      abs_of_nonneg (Real.sqrt_nonneg _)]

/-- The quadratic form of a Gram matrix `P Pᵀ` is a sum of squares:
`x ⬝ᵥ ((P Pᵀ) *ᵥ x) = Σ_j (x ᵥ* P)_j²`. Over `ℝ` this is the key nonnegativity input. -/
theorem real_dotProduct_gram {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix ι κ ℝ) (x : ι → ℝ) :
    x ⬝ᵥ ((P * Pᵀ) *ᵥ x) = ∑ j, (x ᵥ* P) j * (x ᵥ* P) j := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  rfl

/-- If `C` is Hermitian and `C − 1` is positive semidefinite (i.e. `1 ≤ C` in the Loewner order),
then `1 ≤ det C`. Proof: every eigenvalue `μ` of `C` satisfies `μ − 1 ∈ spectrum (C − 1) ⊆ [0, ∞)`,
so `μ ≥ 1`, and `det C = ∏ μ`. -/
theorem one_le_det_of_one_le {C : Matrix n n ℝ}
    (hCherm : C.IsHermitian) (h1 : (C - 1).PosSemidef) : 1 ≤ C.det := by
  rw [hCherm.det_eq_prod_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  apply Finset.one_le_prod
  intro i _
  -- eigenvalue `μ = eigenvalues i` lies in the spectrum of `C`
  have hmem : hCherm.eigenvalues i ∈ spectrum ℝ C := hCherm.eigenvalues_mem_spectrum_real i
  -- spectrum shift: `μ − 1 ∈ spectrum (C − 1)`, since `↑ₐ(μ−1) − (C−1) = ↑ₐμ − C`
  have key : (algebraMap ℝ (Matrix n n ℝ)) (hCherm.eigenvalues i - 1) - (C - 1)
      = (algebraMap ℝ (Matrix n n ℝ)) (hCherm.eigenvalues i) - C := by
    rw [map_sub, map_one]; abel
  have hshift : hCherm.eigenvalues i - 1 ∈ spectrum ℝ (C - 1) := by
    rw [spectrum.mem_iff, key]
    rw [spectrum.mem_iff] at hmem
    exact hmem
  -- a PSD matrix has nonnegative spectrum
  have hnn : (0 : ℝ) ≤ hCherm.eigenvalues i - 1 :=
    (posSemidef_iff_isHermitian_and_spectrum_nonneg.mp h1).2 hshift
  linarith

/-- **Determinant monotonicity on the positive-semidefinite cone.** If `A` is positive semidefinite
and `B − A` is positive semidefinite (i.e. `A ≤ B` in the Loewner order), then `det A ≤ det B`.
Proof: if `A` is singular, `det A = 0 ≤ det B`; otherwise `A` is positive definite, conjugate by the
Gram normaliser `W = A^{−1/2}` (`exists_gram_normalizer`) to `C = W B Wᵀ` with `1 ≤ C` and
`det C = (det A)⁻¹ det B`, whence `det B = det A · det C ≥ det A`. -/
theorem det_le_det_of_posSemidef_le {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hsub : (B - A).PosSemidef) : A.det ≤ B.det := by
  -- `B` is positive semidefinite (a sum of PSD matrices)
  have hB : B.PosSemidef := by
    have h := hsub.add hA
    rwa [sub_add_cancel] at h
  by_cases hdet0 : A.det = 0
  · rw [hdet0]; exact hB.det_nonneg
  · -- `A` is positive definite
    have hApos : 0 < A.det := lt_of_le_of_ne hA.det_nonneg (Ne.symm hdet0)
    have hApd : A.PosDef :=
      hA.posDef_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet0))
    -- the Gram normaliser `W = A^{−1/2}`
    obtain ⟨W, hWsymm, hWAW, hWdet_ne, hWdet_abs⟩ := gram_normalizer A hApd
    have hWH : (Wᵀ)ᴴ = W := by
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
    set C := W * B * Wᵀ with hCdef
    -- `C − 1 = W (B − A) Wᵀ`, hence PSD
    have hid : C - 1 = W * (B - A) * Wᵀ := by
      rw [hCdef, ← hWAW, Matrix.mul_sub, Matrix.sub_mul]
    have hCm1 : (C - 1).PosSemidef := by
      rw [hid]
      have hconj := hsub.conjTranspose_mul_mul_same Wᵀ
      rwa [hWH] at hconj
    -- `C` is PSD (hence Hermitian)
    have hCpsd : C.PosSemidef := by
      rw [hCdef]
      have hconj := hB.conjTranspose_mul_mul_same Wᵀ
      rwa [hWH] at hconj
    have hdetC : 1 ≤ C.det := one_le_det_of_one_le hCpsd.isHermitian hCm1
    -- `(det W)² = (det A)⁻¹`
    have hWdet_sq : (W.det) ^ 2 = (A.det)⁻¹ := by
      have hsq : (W.det) ^ 2 = |W.det| ^ 2 := (sq_abs _).symm
      rw [hsq, hWdet_abs, inv_pow, Real.sq_sqrt hApos.le]
    -- `det C = (det A)⁻¹ · det B`
    have hdetC_eq : C.det = (A.det)⁻¹ * B.det := by
      rw [hCdef, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      rw [show W.det * B.det * W.det = (W.det) ^ 2 * B.det from by ring, hWdet_sq]
    -- conclude
    have hstep : A.det ≤ A.det * C.det := by
      have hnn : (0 : ℝ) ≤ A.det * (C.det - 1) := mul_nonneg hApos.le (by linarith)
      nlinarith [hnn]
    calc A.det ≤ A.det * C.det := hstep
      _ = A.det * ((A.det)⁻¹ * B.det) := by rw [hdetC_eq]
      _ = B.det := by rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hApos), one_mul]

/-- **The single-minor Gram lower bound.** For a `b × q` real matrix `M` and any injective column
selector `S : Fin b → Fin q`, the square of the `b × b` column minor `det (M.submatrix id S)` is at
most the Gram determinant `det (M Mᵀ)`. (Injectivity of `S` forces `b ≤ q`.) -/
theorem det_submatrix_sq_le_det_gram {b q : ℕ} (M : Matrix (Fin b) (Fin q) ℝ)
    {S : Fin b → Fin q} (hS : Function.Injective S) :
    (M.submatrix id S).det ^ 2 ≤ (M * Mᵀ).det := by
  set N := M.submatrix id S with hN
  -- Gram matrices are Hermitian
  have hMMh : (M * Mᵀ).IsHermitian := by
    have h := Matrix.isHermitian_mul_conjTranspose_self M
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hNNh : (N * Nᵀ).IsHermitian := by
    have h := Matrix.isHermitian_mul_conjTranspose_self N
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  -- `M Mᵀ − N Nᵀ` is positive semidefinite (its quadratic form is a subset-sum of squares)
  have hdiff : ((M * Mᵀ) - (N * Nᵀ)).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hMMh.sub hNNh)
    intro x
    have hvecN : ∀ l, (x ᵥ* N) l = (x ᵥ* M) (S l) := fun _ => rfl
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub,
      real_dotProduct_gram M x, real_dotProduct_gram N x]
    simp only [hvecN]
    rw [sub_nonneg]
    calc ∑ l, (x ᵥ* M) (S l) * (x ᵥ* M) (S l)
        = ∑ j ∈ Finset.univ.image S, (x ᵥ* M) j * (x ᵥ* M) j :=
          (Finset.sum_image (f := fun j => (x ᵥ* M) j * (x ᵥ* M) j)
            (fun a _ b _ h => hS h)).symm
      _ ≤ ∑ j, (x ᵥ* M) j * (x ᵥ* M) j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun j _ _ => mul_self_nonneg _)
  -- `N Nᵀ` is positive semidefinite
  have hNNh_psd : (N * Nᵀ).PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose N
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  -- determinant monotonicity + `det(N Nᵀ) = det(N)²`
  have hle := det_le_det_of_posSemidef_le hNNh_psd hdiff
  have hdetNN : (N * Nᵀ).det = N.det ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_transpose, sq]
  rw [hdetNN] at hle
  exact hle

/-- Non-vacuity: the bound applies to a concrete `2 × 3` matrix with a nonzero `2 × 2` minor.
Here `det (minor) = 1` (nonzero) and `det (M Mᵀ) = 42`, so the bound reads `1 ≤ 42`. -/
example :
    ((!![(1 : ℝ), 2, 3; 0, 1, 4]).submatrix id (![0, 1] : Fin 2 → Fin 3)).det ^ 2
      ≤ ((!![(1 : ℝ), 2, 3; 0, 1, 4]) * (!![(1 : ℝ), 2, 3; 0, 1, 4])ᵀ).det :=
  det_submatrix_sq_le_det_gram _ (by decide)

/-- The concrete minor is nonzero (`= 1`), so the non-vacuity instance is a genuine constraint. -/
example :
    ((!![(1 : ℝ), 2, 3; 0, 1, 4]).submatrix id (![0, 1] : Fin 2 → Fin 3)).det = 1 := by
  simp [Matrix.det_fin_two, Matrix.submatrix_apply]

end DLNFibre.DLN.RLCT

```

Questions:
1. FIDELITY of Theorem 1 `det_submatrix_sq_le_det_gram`: does the Lean statement
   `(M.submatrix id S).det ^ 2 ≤ (M * Mᵀ).det` with S injective faithfully and
   fully express INFORMAL CLAIM 1? In Mathlib `M.submatrix id S` has entries
   `M (id i) (S j) = M i (S j)`, i.e. rows unchanged, columns reindexed by S.
   Is `b ≤ q` needed, and is it correctly implied by `hS : Function.Injective S`?
   Any hidden hypothesis, sign issue, or way the statement is weaker/stronger than
   the informal claim?
2. SOUNDNESS of Theorem 2 `det_le_det_of_posSemidef_le`: is the math correct in
   BOTH the A-singular branch (det A = 0) AND the A-positive-definite branch
   (conjugate by A^{-1/2}, show C = A^{-1/2} B A^{-1/2} has all eigenvalues ≥ 1 so
   det C ≥ 1, det B = det A · det C ≥ det A)? Is the eigenvalue-shift step
   (μ ∈ spec C, μ−1 ∈ spec(C−1) ≥ 0) valid? Any missing case or false sub-step?
3. Is the quadratic-form identity `x·((P Pᵀ) x) = Σ_j (xᵀP)_j²` correct, and does
   the "subset sum of nonneg terms" argument (injective S ⟹ image is b distinct
   columns) correctly establish M Mᵀ − N Nᵀ ⪰ 0 where N = M[:, S]?
4. Is the private `gram_normalizer` (W = A^{-1/2} from CFC.sqrt, W A Wᵀ = 1,
   |det W| = (√det A)⁻¹) mathematically correct for A positive-definite?
5. Any SUBTLE conceptual bug, vacuity, or overclaim (name vs content)?
</task>

<output_contract>
For each of the 5 questions: VERDICT (sound / mismatch / gap) + one-sentence
justification. Then a final line: OVERALL = PASS / PASS-WITH-NOTES / FAIL.
Be terse. A specific counterexample beats "seems off".
</output_contract>

<grounding_rules>
Reason from the mathematics. Flag explicitly when a statement is INFERENCE (you
reasoned it) vs OBSERVED (you can point to the exact Lean line). Do not assume the
Lean tactic proof compiles; judge whether the STATEMENT is right and whether a
correct proof of it exists. If you cannot determine a Mathlib lemma's exact
semantics, say so rather than guessing.
</grounding_rules>
