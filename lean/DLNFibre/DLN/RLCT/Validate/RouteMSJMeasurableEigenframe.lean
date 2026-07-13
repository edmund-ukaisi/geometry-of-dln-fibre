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

end DLNFibre.DLN.RLCT.MEframe
