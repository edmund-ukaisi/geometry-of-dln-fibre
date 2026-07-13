import DLNFibre.DLN.RLCT.Validate.RouteMSJResolution
import Mathlib.Analysis.Matrix.Spectrum

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJMeasurableEigenframe` — Brick F2b

`exists_measurableEigenframe` — conjunct (ii) core of Brick F2 (the measurable sorted
eigendecomposition). For a measurable Hermitian (real-symmetric) family
`A : X → Matrix (Fin M₂) (Fin M₂) ℝ` with MEASURABLE sorted eigenvalues (`hλmeas`, supplied by
conjunct (i)/F2a), there is a MEASURABLE orthogonal `U` whose columns are eigenvectors in sorted
(decreasing, `eigenvalues₀`) order.

## Recipe (zero-safe Lagrange projector + measurable first-nonzero-column pivot)

`lagProj A lam i := ∏ j, (1 + (lam i − lam j)⁻¹ • (A − lam i • 1))`, using Lean's total inverse
`0⁻¹ = 0`, is the orthogonal projector onto the FULL `lam i`-eigenspace with NO
multiplicity-partition (totality absorbs stratification). Build columns sequentially:
`R i := P i * (1 − U₍<i₎ U₍<i₎ᵀ)`, `v i :=` normalize (Euclidean) the first nonzero column of `R i`.

Layered to keep the whnf-heavy spectral terms out of the grind (lean/CLAUDE.md): the projector /
recursion / correctness are proved over ABSTRACT `(A, lam, eigenbasis)` in `MEframe`; the spectral
terms are instantiated only in the thin terminal assembly `exists_measurableEigenframe`.
-/

namespace DLNFibre.DLN.RLCT.MEframe

open Matrix

variable {M₂ : ℕ}

/-! ## Layer A, Section 1 — the zero-safe Lagrange projector and its action on eigenvectors -/

/-- One Lagrange factor targeting `lam i`, via `lam j` (`0⁻¹ = 0` when `lam i = lam j`). -/
noncomputable def lagFactor (A : Matrix (Fin M₂) (Fin M₂) ℝ) (lam : Fin M₂ → ℝ) (i j : Fin M₂) :
    Matrix (Fin M₂) (Fin M₂) ℝ :=
  1 + (lam i - lam j)⁻¹ • (A - lam i • 1)

/-- The zero-safe Lagrange projector onto the full `lam i`-eigenspace, `∏_j lagFactor i j` as an
ordered `List.prod` over `List.finRange M₂` (matrix mult is noncommutative; factors do commute). -/
noncomputable def lagProj (A : Matrix (Fin M₂) (Fin M₂) ℝ) (lam : Fin M₂ → ℝ) (i : Fin M₂) :
    Matrix (Fin M₂) (Fin M₂) ℝ :=
  ((List.finRange M₂).map (fun j => lagFactor A lam i j)).prod

/-- A single factor scales an eigenvector `w` by `1 + (lam i − lam j)⁻¹ (μ − lam i)`. -/
theorem lagFactor_mulVec {A : Matrix (Fin M₂) (Fin M₂) ℝ} {lam w : Fin M₂ → ℝ} {μ : ℝ}
    (hw : A *ᵥ w = μ • w) (i j : Fin M₂) :
    lagFactor A lam i j *ᵥ w = (1 + (lam i - lam j)⁻¹ * (μ - lam i)) • w := by
  unfold lagFactor
  rw [add_mulVec, one_mulVec, smul_mulVec, sub_mulVec, smul_mulVec, one_mulVec, hw,
    ← sub_smul, smul_smul, add_smul, one_smul]

/-- The list-projector scales an eigenvector `w` by the list-product of the per-factor scalars. -/
theorem listProj_mulVec {A : Matrix (Fin M₂) (Fin M₂) ℝ} {lam w : Fin M₂ → ℝ} {μ : ℝ}
    (hw : A *ᵥ w = μ • w) (i : Fin M₂) (l : List (Fin M₂)) :
    ((l.map (fun j => lagFactor A lam i j)).prod) *ᵥ w
      = ((l.map (fun j => 1 + (lam i - lam j)⁻¹ * (μ - lam i))).prod) • w := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [← mulVec_mulVec, ih, mulVec_smul, lagFactor_mulVec hw, smul_smul, mul_comm]

/-- **Key lemma (`proj_mulVec_eigen`).** On an eigenvector `w` whose eigenvalue `μ` occurs in the
`lam`-list, the projector acts as the indicator `[μ = lam i]`: identity on the `lam i`-eigenspace,
zero on every other eigenspace. The sole spectral fact everything downstream reduces to. -/
theorem lagProj_eigen {A : Matrix (Fin M₂) (Fin M₂) ℝ} {lam w : Fin M₂ → ℝ} {μ : ℝ}
    (hw : A *ᵥ w = μ • w) (hμ : ∃ k, lam k = μ) (i : Fin M₂) :
    lagProj A lam i *ᵥ w = (if μ = lam i then (1 : ℝ) else 0) • w := by
  rw [lagProj, listProj_mulVec hw]
  congr 1
  by_cases hμi : μ = lam i
  · rw [if_pos hμi]
    apply List.prod_eq_one
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨j, _, rfl⟩ := hx
    rw [hμi, sub_self, mul_zero, add_zero]
  · rw [if_neg hμi]
    obtain ⟨k, hk⟩ := hμ
    apply List.prod_eq_zero
    rw [List.mem_map]
    refine ⟨k, List.mem_finRange k, ?_⟩
    have h1 : lam i - μ ≠ 0 := fun h => hμi (by linarith [sub_eq_zero.mp h])
    rw [hk]
    field_simp
    ring

/-! ## Layer A, Section 2 — the projector is symmetric (factors commute, are symmetric) -/

/-- Two matrices affine in a common `B` commute. -/
theorem commute_affine {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (c c' : ℝ) :
    Commute (1 + c • B) (1 + c' • B) := by
  refine Commute.add_right (Commute.one_right _) (Commute.smul_right ?_ c')
  refine Commute.add_left (Commute.one_left _) (Commute.smul_left ?_ c)
  exact Commute.refl _

/-- Each Lagrange factor is symmetric when `A` is (`Aᵀ = A`). -/
theorem lagFactor_symm {A : Matrix (Fin M₂) (Fin M₂) ℝ} {lam : Fin M₂ → ℝ} (hA : Aᵀ = A)
    (i j : Fin M₂) : (lagFactor A lam i j)ᵀ = lagFactor A lam i j := by
  unfold lagFactor
  rw [transpose_add, transpose_one, transpose_smul, transpose_sub, hA, transpose_smul,
    transpose_one]

/-- Any two Lagrange factors (same `i`) commute — both affine in `A − lam i • 1`. -/
theorem lagFactor_commute {A : Matrix (Fin M₂) (Fin M₂) ℝ} {lam : Fin M₂ → ℝ} (i j k : Fin M₂) :
    Commute (lagFactor A lam i j) (lagFactor A lam i k) :=
  commute_affine (A - lam i • 1) _ _

/-- A list of pairwise-commuting symmetric matrices has a symmetric product. -/
theorem prod_symm_of {n : ℕ} (l : List (Matrix (Fin n) (Fin n) ℝ))
    (hsym : ∀ M ∈ l, Mᵀ = M) (hcomm : ∀ M ∈ l, ∀ N ∈ l, Commute M N) :
    (l.prod)ᵀ = l.prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.prod_cons, transpose_mul,
      ih (fun M hM => hsym M (List.mem_cons_of_mem _ hM))
        (fun M hM N hN => hcomm M (List.mem_cons_of_mem _ hM) N (List.mem_cons_of_mem _ hN)),
      hsym a List.mem_cons_self]
    refine Commute.list_prod_left t a (fun x hx => ?_)
    exact hcomm x (List.mem_cons_of_mem _ hx) a List.mem_cons_self

/-- The zero-safe Lagrange projector is symmetric when `A` is. -/
theorem lagProj_symm {A : Matrix (Fin M₂) (Fin M₂) ℝ} {lam : Fin M₂ → ℝ} (hA : Aᵀ = A)
    (i : Fin M₂) : (lagProj A lam i)ᵀ = lagProj A lam i := by
  rw [lagProj]
  apply prod_symm_of
  · intro M hM
    rw [List.mem_map] at hM
    obtain ⟨j, _, rfl⟩ := hM
    exact lagFactor_symm hA i j
  · intro M hM N hN
    rw [List.mem_map] at hM
    rw [List.mem_map] at hN
    obtain ⟨j, _, rfl⟩ := hM
    obtain ⟨k, _, rfl⟩ := hN
    exact lagFactor_commute i j k

/-! ## Layer A, Section 3 — the sequential frame construction (pivot + fold) -/

open scoped Classical in
/-- The nonzero-column index set of `R` (columns `c` with `fun r => R r c ≠ 0`). -/
noncomputable def nzColSet (R : Matrix (Fin M₂) (Fin M₂) ℝ) : Finset (Fin M₂) :=
  Finset.univ.filter (fun c => (fun r => R r c) ≠ 0)

open scoped Classical in
/-- The first (least-index) nonzero column of `R`, or `0` if `R = 0`. -/
noncomputable def pivotVec (R : Matrix (Fin M₂) (Fin M₂) ℝ) : Fin M₂ → ℝ :=
  if h : (nzColSet R).Nonempty then (fun r => R r ((nzColSet R).min' h)) else 0

/-- The Euclidean-normalized first nonzero column of `R` (a unit vector when `R ≠ 0`). -/
noncomputable def pivotUnit (R : Matrix (Fin M₂) (Fin M₂) ℝ) : Fin M₂ → ℝ :=
  (Real.sqrt (dotProduct (pivotVec R) (pivotVec R)))⁻¹ • pivotVec R

/-- The `n`-th column step from an accumulated projector `Q`: normalize the first nonzero column of
`P⟨n⟩ * (1 − Q)` (junk `0` for out-of-range `n`, never used). -/
noncomputable def colStep (A : Matrix (Fin M₂) (Fin M₂) ℝ) (lam : Fin M₂ → ℝ) (n : ℕ)
    (Q : Matrix (Fin M₂) (Fin M₂) ℝ) : Fin M₂ → ℝ :=
  if h : n < M₂ then pivotUnit (lagProj A lam ⟨n, h⟩ * (1 - Q)) else 0

/-- The accumulated orthogonal projector onto the first `n` chosen columns. -/
noncomputable def Qacc (A : Matrix (Fin M₂) (Fin M₂) ℝ) (lam : Fin M₂ → ℝ) :
    ℕ → Matrix (Fin M₂) (Fin M₂) ℝ
  | 0 => 0
  | (n + 1) =>
    Qacc A lam n +
      vecMulVec (colStep A lam n (Qacc A lam n)) (colStep A lam n (Qacc A lam n))

/-- The `n`-th frame column (`colStep` at the accumulated projector `Qacc … n`). -/
noncomputable def colFn (A : Matrix (Fin M₂) (Fin M₂) ℝ) (lam : Fin M₂ → ℝ) (n : ℕ) : Fin M₂ → ℝ :=
  colStep A lam n (Qacc A lam n)

@[simp] theorem Qacc_zero (A : Matrix (Fin M₂) (Fin M₂) ℝ) (lam : Fin M₂ → ℝ) :
    Qacc A lam 0 = 0 := rfl

theorem Qacc_succ (A : Matrix (Fin M₂) (Fin M₂) ℝ) (lam : Fin M₂ → ℝ) (n : ℕ) :
    Qacc A lam (n + 1) = Qacc A lam n + vecMulVec (colFn A lam n) (colFn A lam n) := rfl

/-- The measurable sorted orthonormal eigenframe: column `c` is `colFn … c`. -/
noncomputable def Uframe (A : Matrix (Fin M₂) (Fin M₂) ℝ) (lam : Fin M₂ → ℝ) :
    Matrix (Fin M₂) (Fin M₂) ℝ :=
  Matrix.of (fun r c => colFn A lam (c : ℕ) r)

/-! ## Layer A, Section 4 — eigenbasis helpers (orthogonality, trace-via-basis, matrix equality) -/

/-- The matrix whose columns are the abstract eigenbasis vectors `b m`. -/
noncomputable def Bmat (b : Fin M₂ → Fin M₂ → ℝ) : Matrix (Fin M₂) (Fin M₂) ℝ :=
  Matrix.of (fun r m => b m r)

variable {b : Fin M₂ → Fin M₂ → ℝ}

/-- Orthonormality in matrix form gives `B Bᵀ = 1` (right inverse of the left inverse). -/
theorem Bmat_mul_transpose (hB : (Bmat b)ᵀ * Bmat b = 1) : Bmat b * (Bmat b)ᵀ = 1 :=
  mul_eq_one_comm.mpr hB

/-- `(M * Bmat b) s m` is the `s`-th entry of `M *ᵥ b m`. -/
theorem mul_Bmat_apply (M : Matrix (Fin M₂) (Fin M₂) ℝ) (s m : Fin M₂) :
    (M * Bmat b) s m = (M *ᵥ b m) s := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Bmat]

/-- Orthonormality (matrix form) as a dotProduct indicator: `⟨b p, b q⟩ = [p = q]`. -/
theorem dotProduct_b (hB : (Bmat b)ᵀ * Bmat b = 1) (p q : Fin M₂) :
    dotProduct (b p) (b q) = if p = q then 1 else 0 := by
  have := congrFun (congrFun hB p) q
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  rw [dotProduct]
  simp only [Matrix.transpose_apply, Bmat, Matrix.of_apply] at this ⊢
  rw [← this]

/-- **Trace via an orthonormal basis.** `trace M = ∑ₘ ⟨b m, M *ᵥ b m⟩` (dotProduct). -/
theorem traceViaBasis (hB : (Bmat b)ᵀ * Bmat b = 1) (M : Matrix (Fin M₂) (Fin M₂) ℝ) :
    M.trace = ∑ m, dotProduct (b m) (M *ᵥ b m) := by
  have hBBt := Bmat_mul_transpose hB
  have hstep : M.trace = ((Bmat b)ᵀ * (M * Bmat b)).trace := by
    rw [← Matrix.trace_mul_comm (M * Bmat b) (Bmat b)ᵀ, Matrix.mul_assoc, hBBt, Matrix.mul_one]
  rw [hstep, Matrix.trace]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Matrix.diag_apply, Matrix.mul_apply, dotProduct]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Matrix.transpose_apply, mul_Bmat_apply]
  simp only [Bmat, Matrix.of_apply]

/-- **Matrix equality from eigenbasis action.** `X`, `Y` agreeing on every `b m` forces `X = Y`. -/
theorem matrix_eq_of_mulVec_basis (hB : (Bmat b)ᵀ * Bmat b = 1)
    {X Y : Matrix (Fin M₂) (Fin M₂) ℝ} (h : ∀ m, X *ᵥ b m = Y *ᵥ b m) : X = Y := by
  have hXB : X * Bmat b = Y * Bmat b := by
    ext s m; rw [mul_Bmat_apply, mul_Bmat_apply, h]
  have hBBt := Bmat_mul_transpose hB
  calc X = X * (Bmat b * (Bmat b)ᵀ) := by rw [hBBt, Matrix.mul_one]
    _ = X * Bmat b * (Bmat b)ᵀ := by rw [Matrix.mul_assoc]
    _ = Y * Bmat b * (Bmat b)ᵀ := by rw [hXB]
    _ = Y * (Bmat b * (Bmat b)ᵀ) := by rw [Matrix.mul_assoc]
    _ = Y := by rw [hBBt, Matrix.mul_one]

/-- **The projector is a `lam i`-eigenprojection (matrix form): `A · P i = lam i • P i`.** Proved by
agreement on the eigenbasis (`proj_mulVec_eigen`: `P i` acts `0/1` on each `b m`). -/
theorem Amul_lagProj {A : Matrix (Fin M₂) (Fin M₂) ℝ} {lam μ : Fin M₂ → ℝ}
    (hB : (Bmat b)ᵀ * Bmat b = 1) (heig : ∀ m, A *ᵥ b m = μ m • b m)
    (hμrange : ∀ m, ∃ k, lam k = μ m) (i : Fin M₂) :
    A * lagProj A lam i = lam i • lagProj A lam i := by
  refine matrix_eq_of_mulVec_basis hB (fun m => ?_)
  have hp := lagProj_eigen (heig m) (hμrange m) i
  rw [← mulVec_mulVec, smul_mulVec]
  simp only [hp]
  rw [mulVec_smul, heig m, smul_smul, smul_smul]
  by_cases h : μ m = lam i <;> simp [h]

/-- **The projector trace counts the `lam i`-eigenvalue multiplicity** `#{m : μ m = lam i}`. -/
theorem trace_lagProj {A : Matrix (Fin M₂) (Fin M₂) ℝ} {lam μ : Fin M₂ → ℝ}
    (hB : (Bmat b)ᵀ * Bmat b = 1) (heig : ∀ m, A *ᵥ b m = μ m • b m)
    (hμrange : ∀ m, ∃ k, lam k = μ m) (i : Fin M₂) :
    (lagProj A lam i).trace = ((Finset.univ.filter (fun m => μ m = lam i)).card : ℝ) := by
  rw [traceViaBasis hB]
  have hterm : ∀ m, dotProduct (b m) (lagProj A lam i *ᵥ b m)
      = if μ m = lam i then (1 : ℝ) else 0 := by
    intro m
    rw [lagProj_eigen (heig m) (hμrange m) i, dotProduct_smul, dotProduct_b hB m m]
    simp
  rw [Finset.sum_congr rfl (fun m _ => hterm m), Finset.sum_boole]

/-! ## Layer A, Section 5 — the frame is orthonormal and diagonalizes (the invariant) -/

/-- Total eigenvalue lookup: `lam ⟨p,·⟩` when `p < M₂`, else `0`. -/
noncomputable def lamN (lam : Fin M₂ → ℝ) (p : ℕ) : ℝ := if h : p < M₂ then lam ⟨p, h⟩ else 0

/-- Outer-product transpose. -/
theorem vecMulVec_transpose (v w : Fin M₂ → ℝ) : (vecMulVec v w)ᵀ = vecMulVec w v := by
  ext i j; simp [vecMulVec, Matrix.transpose_apply, mul_comm]

/-- An outer product acts on a vector by the dotProduct: `(v wᵀ) *ᵥ u = ⟨w, u⟩ • v`. -/
theorem vecMulVec_mulVec (v w u : Fin M₂ → ℝ) :
    vecMulVec v w *ᵥ u = (dotProduct w u) • v := by
  funext i
  simp only [Matrix.mulVec, vecMulVec, Matrix.of_apply, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => by ring)

/-- The accumulated projector is a sum of outer products of the chosen columns. -/
theorem Qacc_eq_sum (A : Matrix (Fin M₂) (Fin M₂) ℝ) (lam : Fin M₂ → ℝ) (n : ℕ) :
    Qacc A lam n = ∑ p ∈ Finset.range n, vecMulVec (colFn A lam p) (colFn A lam p) := by
  induction n with
  | zero => simp
  | succ k ih => rw [Qacc_succ, ih, Finset.sum_range_succ]

/-- The accumulated projector is symmetric. -/
theorem Qacc_symm (A : Matrix (Fin M₂) (Fin M₂) ℝ) (lam : Fin M₂ → ℝ) (n : ℕ) :
    (Qacc A lam n)ᵀ = Qacc A lam n := by
  rw [Qacc_eq_sum, Matrix.transpose_sum]
  exact Finset.sum_congr rfl (fun p _ => vecMulVec_transpose _ _)

/-- Given orthonormality of the first `n` columns, `Qacc … n` fixes each of them. -/
theorem Qacc_fixes (A : Matrix (Fin M₂) (Fin M₂) ℝ) (lam : Fin M₂ → ℝ) (n : ℕ)
    (hon : ∀ p q : ℕ, p < n → q < n →
      dotProduct (colFn A lam p) (colFn A lam q) = if p = q then 1 else 0)
    (q : ℕ) (hq : q < n) :
    Qacc A lam n *ᵥ colFn A lam q = colFn A lam q := by
  rw [Qacc_eq_sum, Matrix.sum_mulVec,
    Finset.sum_congr rfl
      (fun p _ => vecMulVec_mulVec (colFn A lam p) (colFn A lam p) (colFn A lam q)),
    Finset.sum_eq_single q]
  · rw [hon q q hq hq]; simp
  · intro p hp hpq
    rw [hon p q (Finset.mem_range.mp hp) hq, if_neg hpq, zero_smul]
  · intro h; exact absurd (Finset.mem_range.mpr hq) h

/-- If `R ≠ 0`, some column is nonzero. -/
theorem nzColSet_nonempty_of_ne_zero {R : Matrix (Fin M₂) (Fin M₂) ℝ} (hR : R ≠ 0) :
    (nzColSet R).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  apply hR
  ext i j
  have hj : (fun r => R r j) = (0 : Fin M₂ → ℝ) := by
    by_contra hc
    have hmem : j ∈ nzColSet R := by
      simp only [nzColSet, Finset.mem_filter]; exact ⟨Finset.mem_univ j, hc⟩
    rw [h] at hmem; simp at hmem
  have := congrFun hj i
  simpa using this

/-- The first nonzero column of `R` is the matrix acting on a standard basis vector. -/
theorem pivotVec_eq (R : Matrix (Fin M₂) (Fin M₂) ℝ) (h : (nzColSet R).Nonempty) :
    pivotVec R = R *ᵥ Pi.single ((nzColSet R).min' h) 1 := by
  funext r
  rw [pivotVec, dif_pos h]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The first nonzero column of a nonzero matrix is nonzero. -/
theorem pivotVec_ne_zero {R : Matrix (Fin M₂) (Fin M₂) ℝ} (hR : R ≠ 0) : pivotVec R ≠ 0 := by
  have h := nzColSet_nonempty_of_ne_zero hR
  rw [pivotVec, dif_pos h]
  have hmem := Finset.min'_mem (nzColSet R) h
  simp only [nzColSet, Finset.mem_filter] at hmem
  exact hmem.2

/-- The normalized first nonzero column is a unit vector (`⟨v, v⟩ = 1`). -/
theorem dotProduct_pivotUnit_self {R : Matrix (Fin M₂) (Fin M₂) ℝ} (hR : R ≠ 0) :
    dotProduct (pivotUnit R) (pivotUnit R) = 1 := by
  have hv : pivotVec R ≠ 0 := pivotVec_ne_zero hR
  have hd : (0 : ℝ) < dotProduct (pivotVec R) (pivotVec R) := by
    rw [dotProduct]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    refine Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
    exact mul_self_pos.mpr (by simpa using hi)
  rw [pivotUnit, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ← mul_inv, Real.mul_self_sqrt hd.le, inv_mul_cancel₀ (ne_of_gt hd)]

/-- `trace (P * v vᵀ) = ⟨v, P *ᵥ v⟩` (dotProduct). -/
theorem trace_mul_vecMulVec (P : Matrix (Fin M₂) (Fin M₂) ℝ) (v : Fin M₂ → ℝ) :
    (P * vecMulVec v v).trace = dotProduct v (P *ᵥ v) := by
  rw [Matrix.trace, dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [vecMulVec_apply]; ring

/-- Multiplicity of `c` is the same through `lam` or through `μ` (a perm-reindexing). -/
theorem card_lam_eq_card_mu {lam μ : Fin M₂ → ℝ} {σ : Equiv.Perm (Fin M₂)}
    (hσ : lam = μ ∘ σ) (c : ℝ) :
    (Finset.univ.filter (fun k => lam k = c)).card
      = (Finset.univ.filter (fun m => μ m = c)).card := by
  apply Finset.card_equiv σ
  intro k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hσ, Function.comp_apply]

/-- The count of chosen columns already in the `lam ⟨n⟩`-eigenspace is below its multiplicity. -/
theorem chosen_lt_mult (lam : Fin M₂ → ℝ) (n : ℕ) (hn : n < M₂) :
    ((Finset.range n).filter (fun p => lamN lam p = lam ⟨n, hn⟩)).card
      < (Finset.univ.filter (fun k : Fin M₂ => lam k = lam ⟨n, hn⟩)).card := by
  set T : Finset (Fin M₂) := Finset.univ.filter (fun k => lam k = lam ⟨n, hn⟩) with hT
  have hsub : (Finset.range n).filter (fun p => lamN lam p = lam ⟨n, hn⟩) ⊆ T.image Fin.val := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    have hpM : p < M₂ := lt_trans hp.1 hn
    have hpl : lam ⟨p, hpM⟩ = lam ⟨n, hn⟩ := by rw [lamN, dif_pos hpM] at hp; exact hp.2
    rw [Finset.mem_image]
    exact ⟨⟨p, hpM⟩, by rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hpl⟩, rfl⟩
  have hnotL : n ∉ (Finset.range n).filter (fun p => lamN lam p = lam ⟨n, hn⟩) := by
    rw [Finset.mem_filter, Finset.mem_range]; rintro ⟨h, _⟩; omega
  have hnT : n ∈ T.image Fin.val := by
    rw [Finset.mem_image]
    exact ⟨⟨n, hn⟩, by rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, rfl⟩, rfl⟩
  calc ((Finset.range n).filter (fun p => lamN lam p = lam ⟨n, hn⟩)).card
      < (T.image Fin.val).card :=
        Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨n, hnT, hnotL⟩)
    _ = T.card := Finset.card_image_of_injective T Fin.val_injective

/-- **The residual `R_n = P⟨n⟩ (1 − Qacc n)` is nonzero** — the trace non-vanishing crux. If it
vanished, `P⟨n⟩ = P⟨n⟩ Qacc n`, so `trace P⟨n⟩ = trace (P⟨n⟩ Qacc n)`; the former counts the full
`lam ⟨n⟩`-multiplicity, the latter only the `< n` chosen columns there — strictly fewer. -/
theorem R_ne_zero {A : Matrix (Fin M₂) (Fin M₂) ℝ} {lam μ : Fin M₂ → ℝ} {σ : Equiv.Perm (Fin M₂)}
    (hB : (Bmat b)ᵀ * Bmat b = 1) (heig : ∀ m, A *ᵥ b m = μ m • b m) (hσ : lam = μ ∘ σ)
    (n : ℕ) (hn : n < M₂)
    (ih_on : ∀ p q : ℕ, p < n → q < n →
      dotProduct (colFn A lam p) (colFn A lam q) = if p = q then 1 else 0)
    (ih_eig : ∀ p : ℕ, p < n → A *ᵥ colFn A lam p = lamN lam p • colFn A lam p) :
    lagProj A lam ⟨n, hn⟩ * (1 - Qacc A lam n) ≠ 0 := by
  intro hR0
  set i : Fin M₂ := ⟨n, hn⟩ with hi
  have hμrange : ∀ m, ∃ k, lam k = μ m := fun m => ⟨σ.symm m, by rw [hσ]; simp⟩
  have hPQ : lagProj A lam i = lagProj A lam i * Qacc A lam n := by
    have h0 : lagProj A lam i * (1 - Qacc A lam n) = 0 := hR0
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h0; exact h0
  have hterm : ∀ p ∈ Finset.range n,
      (lagProj A lam i * vecMulVec (colFn A lam p) (colFn A lam p)).trace
        = (if lamN lam p = lam i then (1 : ℝ) else 0) := by
    intro p hp
    have hpn := Finset.mem_range.mp hp
    have hpM : p < M₂ := lt_trans hpn hn
    have hpr : ∃ kk, lam kk = lamN lam p := ⟨⟨p, hpM⟩, by rw [lamN, dif_pos hpM]⟩
    rw [trace_mul_vecMulVec, lagProj_eigen (ih_eig p hpn) hpr i, dotProduct_smul,
      ih_on p p hpn hpn]
    simp
  have key : ((Finset.univ.filter (fun m => μ m = lam i)).card : ℝ)
      = ((Finset.range n).filter (fun p => lamN lam p = lam i)).card := by
    rw [← trace_lagProj hB heig hμrange i, hPQ, Qacc_eq_sum, Finset.mul_sum, Matrix.trace_sum,
      Finset.sum_congr rfl hterm, Finset.sum_boole]
  have hcast : (Finset.univ.filter (fun m => μ m = lam i)).card
      = ((Finset.range n).filter (fun p => lamN lam p = lam i)).card := by exact_mod_cast key
  have hmult := card_lam_eq_card_mu hσ (lam i)
  have hlt := chosen_lt_mult lam n hn
  rw [← hi] at hlt
  omega

/-- If `A · R = c • R`, the first nonzero column of `R` is a `c`-eigenvector. -/
theorem pivotVec_eigen {A R : Matrix (Fin M₂) (Fin M₂) ℝ} {c : ℝ} (hAR : A * R = c • R) :
    A *ᵥ pivotVec R = c • pivotVec R := by
  by_cases h : (nzColSet R).Nonempty
  · rw [pivotVec_eq R h, mulVec_mulVec, hAR, smul_mulVec]
  · rw [pivotVec, dif_neg h]; simp

/-- The normalized first nonzero column of `R` (with `A · R = c • R`) is a `c`-eigenvector. -/
theorem pivotUnit_eigen {A R : Matrix (Fin M₂) (Fin M₂) ℝ} {c : ℝ} (hAR : A * R = c • R) :
    A *ᵥ pivotUnit R = c • pivotUnit R := by
  rw [pivotUnit, mulVec_smul, pivotVec_eigen hAR, smul_comm]

/-- `A · (P i · X) = lam i • (P i · X)` — the eigenprojector pushed through a right factor. -/
theorem AR_smul {A : Matrix (Fin M₂) (Fin M₂) ℝ} {lam μ : Fin M₂ → ℝ} {σ : Equiv.Perm (Fin M₂)}
    (hB : (Bmat b)ᵀ * Bmat b = 1) (heig : ∀ m, A *ᵥ b m = μ m • b m) (hσ : lam = μ ∘ σ)
    (i : Fin M₂) (X : Matrix (Fin M₂) (Fin M₂) ℝ) :
    A * (lagProj A lam i * X) = lam i • (lagProj A lam i * X) := by
  have hμrange : ∀ m, ∃ k, lam k = μ m := fun m => ⟨σ.symm m, by rw [hσ]; simp⟩
  rw [← Matrix.mul_assoc, Amul_lagProj hB heig hμrange i, Matrix.smul_mul]

/-- The residual's transpose kills every earlier column: `Rᵀ *ᵥ colFn q = 0` for `q < n`. -/
theorem Rt_mulVec_colFn_zero {A : Matrix (Fin M₂) (Fin M₂) ℝ} {lam : Fin M₂ → ℝ} (hsymm : Aᵀ = A)
    (n : ℕ) (hn : n < M₂)
    (ih_on : ∀ p q : ℕ, p < n → q < n →
      dotProduct (colFn A lam p) (colFn A lam q) = if p = q then 1 else 0)
    (ih_eig : ∀ p : ℕ, p < n → A *ᵥ colFn A lam p = lamN lam p • colFn A lam p)
    (q : ℕ) (hq : q < n) :
    (lagProj A lam ⟨n, hn⟩ * (1 - Qacc A lam n))ᵀ *ᵥ colFn A lam q = 0 := by
  have hRt : (lagProj A lam ⟨n, hn⟩ * (1 - Qacc A lam n))ᵀ
      = (1 - Qacc A lam n) * lagProj A lam ⟨n, hn⟩ := by
    rw [Matrix.transpose_mul, lagProj_symm hsymm, Matrix.transpose_sub, Matrix.transpose_one,
      Qacc_symm]
  rw [hRt, ← mulVec_mulVec (colFn A lam q) (1 - Qacc A lam n) (lagProj A lam ⟨n, hn⟩)]
  have hqM : q < M₂ := lt_trans hq hn
  have hqr : ∃ kk, lam kk = lamN lam q := ⟨⟨q, hqM⟩, by rw [lamN, dif_pos hqM]⟩
  rw [lagProj_eigen (ih_eig q hq) hqr ⟨n, hn⟩]
  by_cases hc : lamN lam q = lam ⟨n, hn⟩
  · rw [if_pos hc, one_smul, sub_mulVec, one_mulVec, Qacc_fixes A lam n ih_on q hq, sub_self]
  · rw [if_neg hc, zero_smul, mulVec_zero]

/-- **The frame invariant.** For `n ≤ M₂`: the first `n` columns are orthonormal and each `colFn p`
(`p < n`) is an `A`-eigenvector with eigenvalue `lamN lam p`. Induction on `n`, the new column `k`
handled by the pivot facts (`R_ne_zero`, `pivotUnit_eigen`, `Rt_mulVec_colFn_zero`). -/
theorem frame_invariant {A : Matrix (Fin M₂) (Fin M₂) ℝ} {lam μ : Fin M₂ → ℝ}
    {σ : Equiv.Perm (Fin M₂)} (hsymm : Aᵀ = A) (hB : (Bmat b)ᵀ * Bmat b = 1)
    (heig : ∀ m, A *ᵥ b m = μ m • b m) (hσ : lam = μ ∘ σ) :
    ∀ n : ℕ, n ≤ M₂ →
      (∀ p q : ℕ, p < n → q < n →
        dotProduct (colFn A lam p) (colFn A lam q) = if p = q then 1 else 0) ∧
      (∀ p : ℕ, p < n → A *ᵥ colFn A lam p = lamN lam p • colFn A lam p) := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨fun p q hp _ => absurd hp (by omega), fun p hp => absurd hp (by omega)⟩
  | succ k ih =>
    intro hk1
    have hk : k < M₂ := by omega
    obtain ⟨ih_on, ih_eig⟩ := ih (by omega)
    have hRne : lagProj A lam ⟨k, hk⟩ * (1 - Qacc A lam k) ≠ 0 :=
      R_ne_zero hB heig hσ k hk ih_on ih_eig
    have hcolk : colFn A lam k = pivotUnit (lagProj A lam ⟨k, hk⟩ * (1 - Qacc A lam k)) := by
      rw [colFn, colStep, dif_pos hk]
    have heigk : A *ᵥ colFn A lam k = lam ⟨k, hk⟩ • colFn A lam k := by
      rw [hcolk]; exact pivotUnit_eigen (AR_smul hB heig hσ ⟨k, hk⟩ (1 - Qacc A lam k))
    have hunitk : dotProduct (colFn A lam k) (colFn A lam k) = 1 := by
      rw [hcolk]; exact dotProduct_pivotUnit_self hRne
    have horthk : ∀ q : ℕ, q < k → dotProduct (colFn A lam q) (colFn A lam k) = 0 := by
      intro q hq
      have hpv : dotProduct (colFn A lam q)
          (pivotVec (lagProj A lam ⟨k, hk⟩ * (1 - Qacc A lam k))) = 0 := by
        rw [pivotVec_eq _ (nzColSet_nonempty_of_ne_zero hRne), dotProduct_mulVec,
          ← mulVec_transpose (lagProj A lam ⟨k, hk⟩ * (1 - Qacc A lam k)) (colFn A lam q),
          Rt_mulVec_colFn_zero hsymm k hk ih_on ih_eig q hq, zero_dotProduct]
      rw [hcolk, pivotUnit, dotProduct_smul, hpv, smul_zero]
    refine ⟨fun p q hp hq => ?_, fun p hp => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hpk | hpe
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hqk | hqe
        · exact ih_on p q hpk hqk
        · rw [hqe, horthk p hpk, if_neg (by omega)]
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hqk | hqe
        · rw [hpe, dotProduct_comm, horthk q hqk, if_neg (by omega)]
        · rw [hpe, hqe, hunitk, if_pos rfl]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hpk | hpe
      · exact ih_eig p hpk
      · rw [hpe, show lamN lam k = lam ⟨k, hk⟩ from by rw [lamN, dif_pos hk]]; exact heigk

/-- **The frame is orthogonal: `Uᵀ U = 1`** (orthonormal columns; invariant at `n = M₂`). -/
theorem Uframe_orthonormal {A : Matrix (Fin M₂) (Fin M₂) ℝ} {lam μ : Fin M₂ → ℝ}
    {σ : Equiv.Perm (Fin M₂)} (hsymm : Aᵀ = A) (hB : (Bmat b)ᵀ * Bmat b = 1)
    (heig : ∀ m, A *ᵥ b m = μ m • b m) (hσ : lam = μ ∘ σ) :
    (Uframe A lam)ᵀ * Uframe A lam = 1 := by
  obtain ⟨hon, _⟩ := frame_invariant hsymm hB heig hσ M₂ le_rfl
  ext c c'
  rw [Matrix.mul_apply, Matrix.one_apply]
  change dotProduct (colFn A lam (c : ℕ)) (colFn A lam (c' : ℕ)) = if c = c' then 1 else 0
  rw [hon (c : ℕ) (c' : ℕ) c.isLt c'.isLt]
  simp [Fin.val_inj]

/-- **The frame diagonalizes: `A U = U · diagonal lam`** (each column a sorted eigenvector). -/
theorem Uframe_diagonalizes {A : Matrix (Fin M₂) (Fin M₂) ℝ} {lam μ : Fin M₂ → ℝ}
    {σ : Equiv.Perm (Fin M₂)} (hsymm : Aᵀ = A) (hB : (Bmat b)ᵀ * Bmat b = 1)
    (heig : ∀ m, A *ᵥ b m = μ m • b m) (hσ : lam = μ ∘ σ) :
    A * Uframe A lam = Uframe A lam * Matrix.diagonal lam := by
  obtain ⟨_, heigf⟩ := frame_invariant hsymm hB heig hσ M₂ le_rfl
  ext r c
  have hcol : A *ᵥ colFn A lam (c : ℕ) = lam c • colFn A lam (c : ℕ) := by
    rw [heigf (c : ℕ) c.isLt, lamN, dif_pos c.isLt]
  have hL : (∑ s, A r s * Uframe A lam s c) = (A *ᵥ colFn A lam (c : ℕ)) r := rfl
  rw [Matrix.mul_apply, hL, hcol, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Finset.sum_eq_single c]
  · rw [Matrix.diagonal_apply_eq]
    change lam c * colFn A lam (c : ℕ) r = colFn A lam (c : ℕ) r * lam c
    ring
  · intro s _ hsc; rw [Matrix.diagonal_apply_ne _ hsc, mul_zero]
  · intro h; exact absurd (Finset.mem_univ c) h

/-! ## Layer M — measurability (entrywise, then the fold by `ℕ`-induction) -/

variable {X : Type*} [MeasurableSpace X]

/-- A matrix family with all entries measurable. -/
def MeasEntries (f : X → Matrix (Fin M₂) (Fin M₂) ℝ) : Prop :=
  ∀ i j, Measurable (fun z => f z i j)

/-- A vector family with all components measurable. -/
def MeasVec (v : X → Fin M₂ → ℝ) : Prop := ∀ i, Measurable (fun z => v z i)

theorem MeasEntries.add {f g : X → Matrix (Fin M₂) (Fin M₂) ℝ} (hf : MeasEntries f)
    (hg : MeasEntries g) : MeasEntries (fun z => f z + g z) := fun i j => by
  simpa using (hf i j).add (hg i j)

theorem MeasEntries.sub {f g : X → Matrix (Fin M₂) (Fin M₂) ℝ} (hf : MeasEntries f)
    (hg : MeasEntries g) : MeasEntries (fun z => f z - g z) := fun i j => by
  simpa using (hf i j).sub (hg i j)

theorem MeasEntries.mul {f g : X → Matrix (Fin M₂) (Fin M₂) ℝ} (hf : MeasEntries f)
    (hg : MeasEntries g) : MeasEntries (fun z => f z * g z) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ (fun k _ => (hf i k).mul (hg k j))

theorem MeasEntries.smul {c : X → ℝ} {f : X → Matrix (Fin M₂) (Fin M₂) ℝ} (hc : Measurable c)
    (hf : MeasEntries f) : MeasEntries (fun z => c z • f z) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact hc.mul (hf i j)

theorem measEntries_one : MeasEntries (fun _ : X => (1 : Matrix (Fin M₂) (Fin M₂) ℝ)) :=
  fun _ _ => measurable_const

theorem MeasVec.vecMulVec {v : X → Fin M₂ → ℝ} (hv : MeasVec v) :
    MeasEntries (fun z => vecMulVec (v z) (v z)) := fun i j => by
  simp only [vecMulVec_apply]; exact (hv i).mul (hv j)

/-- Each Lagrange factor is entrywise measurable. -/
theorem measEntries_lagFactor {A : X → Matrix (Fin M₂) (Fin M₂) ℝ} {lam : X → Fin M₂ → ℝ}
    (hA : MeasEntries A) (hlam : MeasVec lam) (i j : Fin M₂) :
    MeasEntries (fun z => lagFactor (A z) (lam z) i j) := by
  refine measEntries_one.add (MeasEntries.smul ((hlam i).sub (hlam j)).inv ?_)
  exact hA.sub (MeasEntries.smul (hlam i) measEntries_one)

/-- The list-projector is entrywise measurable. -/
theorem measEntries_listProj {A : X → Matrix (Fin M₂) (Fin M₂) ℝ} {lam : X → Fin M₂ → ℝ}
    (hA : MeasEntries A) (hlam : MeasVec lam) (i : Fin M₂) (l : List (Fin M₂)) :
    MeasEntries (fun z => (l.map (fun j => lagFactor (A z) (lam z) i j)).prod) := by
  induction l with
  | nil => simpa using measEntries_one
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (measEntries_lagFactor hA hlam i a).mul ih

/-- The Lagrange projector is entrywise measurable. -/
theorem measEntries_lagProj {A : X → Matrix (Fin M₂) (Fin M₂) ℝ} {lam : X → Fin M₂ → ℝ}
    (hA : MeasEntries A) (hlam : MeasVec lam) (i : Fin M₂) :
    MeasEntries (fun z => lagProj (A z) (lam z) i) :=
  measEntries_listProj hA hlam i (List.finRange M₂)

open scoped Classical in
/-- The first-nonzero column, as a finite indicator sum over "`c` is the first nonzero column". -/
theorem pivotVec_eq_sum_ite (R : Matrix (Fin M₂) (Fin M₂) ℝ) (r : Fin M₂) :
    pivotVec R r
      = ∑ c : Fin M₂, if ((fun r' => R r' c) ≠ 0 ∧ ∀ c', c' < c → (fun r' => R r' c') = 0)
          then R r c else 0 := by
  by_cases h : (nzColSet R).Nonempty
  · rw [pivotVec, dif_pos h]
    have hc0mem := Finset.min'_mem (nzColSet R) h
    simp only [nzColSet, Finset.mem_filter] at hc0mem
    have hP0 : (fun r' => R r' ((nzColSet R).min' h)) ≠ 0
        ∧ ∀ c', c' < (nzColSet R).min' h → (fun r' => R r' c') = 0 := by
      refine ⟨hc0mem.2, fun c' hc' => ?_⟩
      by_contra hcol
      have : c' ∈ nzColSet R := by
        simp only [nzColSet, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hcol⟩
      exact absurd (Finset.min'_le _ _ this) (not_le.mpr hc')
    rw [Finset.sum_eq_single ((nzColSet R).min' h) (fun c _ hcne => ?_) (fun hc0 => ?_)]
    · rw [if_pos hP0]
    · refine if_neg (fun ⟨hcol, hlt⟩ => ?_)
      have hcmem : c ∈ nzColSet R := by
        simp only [nzColSet, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hcol⟩
      rcases lt_or_eq_of_le (Finset.min'_le _ _ hcmem) with hlt2 | heq
      · exact hc0mem.2 (hlt _ hlt2)
      · exact hcne heq.symm
    · exact absurd (Finset.mem_univ _) hc0
  · rw [pivotVec, dif_neg h]
    refine (Finset.sum_eq_zero (fun c _ => if_neg (fun ⟨hcol, _⟩ => h ⟨c, ?_⟩))).symm
    simp only [nzColSet, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hcol⟩

/-- Measurability of the first-nonzero-column selection (the sole finite measurable pivot). -/
theorem measVec_pivotVec {R : X → Matrix (Fin M₂) (Fin M₂) ℝ} (hR : MeasEntries R) :
    MeasVec (fun z => pivotVec (R z)) := by
  intro r
  simp_rw [pivotVec_eq_sum_ite]
  refine Finset.measurable_sum _ (fun c _ => ?_)
  have hcolzero : ∀ c', MeasurableSet {z | (fun r' => R z r' c') = 0} := by
    intro c'
    have : {z | (fun r' => R z r' c') = 0} = ⋂ r', {z | R z r' c' = 0} := by
      ext z; simp [funext_iff]
    rw [this]
    exact MeasurableSet.iInter (fun r' => (hR r' c') (measurableSet_singleton 0))
  have hset : MeasurableSet {z | (fun r' => R z r' c) ≠ 0
      ∧ ∀ c', c' < c → (fun r' => R z r' c') = 0} := by
    rw [Set.setOf_and]
    refine MeasurableSet.inter ?_ ?_
    · have heq : {z | (fun r' => R z r' c) ≠ 0} = (⋂ r', {z | R z r' c = 0})ᶜ := by
        ext z; simp [funext_iff]
      rw [heq]
      exact (MeasurableSet.iInter (fun r' => (hR r' c) (measurableSet_singleton 0))).compl
    · rw [Set.setOf_forall]
      refine MeasurableSet.iInter (fun c' => ?_)
      by_cases hc' : c' < c
      · have : {z | c' < c → (fun r' => R z r' c') = 0} = {z | (fun r' => R z r' c') = 0} := by
          ext z; simp [hc']
        rw [this]; exact hcolzero c'
      · have : {z | c' < c → (fun r' => R z r' c') = 0} = Set.univ := by ext z; simp [hc']
        rw [this]; exact MeasurableSet.univ
  exact Measurable.ite hset (hR r c) measurable_const

/-- Measurability of the normalized first-nonzero column. -/
theorem measVec_pivotUnit {R : X → Matrix (Fin M₂) (Fin M₂) ℝ} (hR : MeasEntries R) :
    MeasVec (fun z => pivotUnit (R z)) := by
  have hpv := measVec_pivotVec hR
  have hd : Measurable (fun z => dotProduct (pivotVec (R z)) (pivotVec (R z))) := by
    simp only [dotProduct]
    exact Finset.measurable_sum _ (fun i _ => (hpv i).mul (hpv i))
  intro i
  simp only [pivotUnit, Pi.smul_apply, smul_eq_mul]
  exact (Real.continuous_sqrt.measurable.comp hd).inv.mul (hpv i)

end DLNFibre.DLN.RLCT.MEframe
