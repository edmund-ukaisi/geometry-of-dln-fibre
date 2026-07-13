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

end DLNFibre.DLN.RLCT.MEframe
