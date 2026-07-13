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

end DLNFibre.DLN.RLCT.MEframe
