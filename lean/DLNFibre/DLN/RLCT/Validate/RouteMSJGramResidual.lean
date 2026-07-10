import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJGramResidual` — Gram determinant row-residual recursion

**Thread `genm-catI-integrability`, Cat I good-stratum piece P3 (geometric half).** Prepending one
row `w` to a family `u : Fin n → E` (`E` a real inner-product space) multiplies the Gram determinant
by the *squared residual* `‖P_{V⊥} w‖²`, where `V = span (range u)` is the span of the other
rows and `P_{V⊥}` is orthogonal projection onto `V⊥`:

    det( gram (cons w u) ) = det( gram u ) · ‖(span (range u))ᗮ.starProjection w‖².

This is the geometric identification of the Schur-complement scalar of `RouteMSJGramSchur`. The
identity holds UNCONDITIONALLY (both the good-stratum `det(gram u) ≠ 0` branch, via the Schur
complement + least-squares residual normal equations, and the degenerate `det(gram u) = 0` branch,
via a shared kernel vector). This is exactly the pointwise integrand rewrite the Cat I Tonelli
row-recursion consumes.

S2-FREE: pure inner-product / matrix algebra. Intended axiom footprint
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped Matrix InnerProductSpace

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Reindexing equivalence `Fin (n+1) ≃ Fin n ⊕ Unit`: `0 ↦ inr`, `i.succ ↦ inl i`.  Used to move
between the `Fin.cons w u` row order and the `Sum.elim u (const w)` block order (`u`-block first, so
that `det_fromBlocks₁₁` uses the invertible Gram block). -/
def consSumEquiv (n : ℕ) : Fin (n + 1) ≃ (Fin n ⊕ Unit) where
  toFun := fun x => Fin.cases (Sum.inr Unit.unit) Sum.inl x
  invFun := Sum.elim Fin.succ (fun _ => 0)
  left_inv := fun x => by
    refine Fin.cases ?_ ?_ x
    · simp
    · intro i; simp
  right_inv := fun s => by
    rcases s with i | u
    · simp
    · simp

@[simp] lemma consSumEquiv_zero : consSumEquiv n 0 = Sum.inr Unit.unit := by
  simp [consSumEquiv]

@[simp] lemma consSumEquiv_succ (i : Fin n) : consSumEquiv n i.succ = Sum.inl i := by
  simp [consSumEquiv]

/-- The `Sum.elim u (const w)` family, precomposed with `consSumEquiv`, is `Fin.cons w u`. -/
lemma sumElim_comp_consSumEquiv (u : Fin n → E) (w : E) :
    (Sum.elim u (fun _ : Unit => w)) ∘ consSumEquiv n = Fin.cons w u := by
  funext x
  refine Fin.cases ?_ ?_ x
  · simp
  · intro i; simp

/-- Reindexing invariance of the Gram determinant: the `cons` row order and the `Sum.elim` block
order give equal Gram determinants. -/
lemma det_gram_cons_eq_det_gram_sumElim (u : Fin n → E) (w : E) :
    (Matrix.gram ℝ (Fin.cons w u)).det
      = (Matrix.gram ℝ (Sum.elim u (fun _ : Unit => w))).det := by
  have h : Matrix.gram ℝ (Fin.cons w u)
      = (Matrix.gram ℝ (Sum.elim u (fun _ : Unit => w))).submatrix
          (consSumEquiv n) (consSumEquiv n) := by
    rw [← sumElim_comp_consSumEquiv u w]; rfl
  rw [h, Matrix.det_submatrix_equiv_self]

/-- Block decomposition of the Gram of `Sum.elim u (const w)` (`u`-block in the top-left corner). -/
lemma gram_sumElim_eq_fromBlocks (u : Fin n → E) (w : E) :
    Matrix.gram ℝ (Sum.elim u (fun _ : Unit => w))
      = Matrix.fromBlocks (Matrix.gram ℝ u)
          (Matrix.of fun i (_ : Unit) => ⟪u i, w⟫_ℝ)
          (Matrix.of fun (_ : Unit) j => ⟪u j, w⟫_ℝ)
          (Matrix.of fun (_ : Unit) (_ : Unit) => ⟪w, w⟫_ℝ) := by
  ext a b
  rcases a with i | pa <;> rcases b with j | pb <;>
    simp [Matrix.gram_apply, real_inner_comm]

/-- **Degenerate branch.** If the Gram of `u` is singular, so is the Gram of `Fin.cons w u`:
`u` is then linearly dependent, so `Fin.cons w u` is too, and a shared kernel vector kills the
determinant. -/
lemma det_gram_cons_of_det_gram_zero (u : Fin n → E) (w : E)
    (hdet : (Matrix.gram ℝ u).det = 0) :
    (Matrix.gram ℝ (Fin.cons w u)).det = 0 := by
  obtain ⟨x, hx_ne, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set v : Fin (n + 1) → E := Fin.cons w u with hv
  set z : Fin (n + 1) → ℝ := Fin.cons (0 : ℝ) x with hz
  -- `∑ xᵢ • uᵢ = 0`
  have hsum : ∑ i, x i • u i = (0 : E) := by
    have h := Matrix.star_dotProduct_gram_mulVec (𝕜 := ℝ) u x x
    rw [hx, dotProduct_zero] at h
    exact inner_self_eq_zero.mp h.symm
  -- extend by a zero in the head coordinate
  have hsum' : ∑ j, z j • v j = (0 : E) := by
    rw [hz, hv, Fin.sum_univ_succ]; simp [Fin.cons_zero, Fin.cons_succ, hsum]
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨z, ?_, ?_⟩
  · intro hzero
    apply hx_ne
    funext i
    have hi := congrFun hzero i.succ
    rw [hz] at hi
    rwa [Fin.cons_succ, Pi.zero_apply] at hi
  · funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.gram_apply, Pi.zero_apply]
    calc ∑ j, ⟪v k, v j⟫_ℝ * z j
        = ⟪v k, ∑ j, z j • v j⟫_ℝ := by
          rw [inner_sum]; exact Finset.sum_congr rfl fun j _ => by
            rw [real_inner_smul_right]; ring
      _ = 0 := by rw [hsum']; exact inner_zero_right _

variable [FiniteDimensional ℝ E]

/-- **Good-stratum branch.** With the Gram of `u` invertible, the least-squares residual
`r = w - ∑ cᵢ uᵢ` (`c = ⅟(gram u) · y`, `yᵢ = ⟪uᵢ, w⟫`) is the orthogonal projection of `w` onto
`(span (range u))ᗮ`, and the Schur-complement scalar equals `‖r‖²`. -/
lemma det_gram_cons_of_det_gram_ne_zero (u : Fin n → E) (w : E)
    (hdet : (Matrix.gram ℝ u).det ≠ 0) :
    (Matrix.gram ℝ (Fin.cons w u)).det
      = (Matrix.gram ℝ u).det
        * ‖(Submodule.span ℝ (Set.range u))ᗮ.starProjection w‖ ^ 2 := by
  letI : Invertible (Matrix.gram ℝ u) :=
    Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hdet)
  set y : Fin n → ℝ := fun i => ⟪u i, w⟫_ℝ with hy
  set c : Fin n → ℝ := ⅟(Matrix.gram ℝ u) *ᵥ y with hc
  set p : E := ∑ i, c i • u i with hp
  set V := Submodule.span ℝ (Set.range u) with hV
  set r : E := w - p with hr
  -- `gram u ·ᵥ c = y`
  have hGc : Matrix.gram ℝ u *ᵥ c = y := by
    rw [hc, Matrix.mulVec_mulVec, mul_invOf_self, Matrix.one_mulVec]
  -- `⟪p, uᵢ⟫ = yᵢ`
  have hpu : ∀ i, ⟪p, u i⟫_ℝ = y i := by
    intro i
    rw [hp, sum_inner]
    have : y i = (Matrix.gram ℝ u *ᵥ c) i := by rw [hGc]
    rw [this]
    simp only [real_inner_smul_left, Matrix.mulVec, dotProduct, Matrix.gram_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [real_inner_comm (u j) (u i)]; ring
  -- `⟪p, w⟫ = c ⬝ᵥ y`
  have hpw : ⟪p, w⟫_ℝ = c ⬝ᵥ y := by
    rw [hp, sum_inner]; simp only [real_inner_smul_left]; rfl
  -- `⟪p, p⟫ = c ⬝ᵥ y`
  have hpp : ⟪p, p⟫_ℝ = c ⬝ᵥ y := by
    calc ⟪p, p⟫_ℝ = ⟪p, ∑ i, c i • u i⟫_ℝ := by rw [← hp]
      _ = ∑ i, c i * ⟪p, u i⟫_ℝ := by rw [inner_sum]; simp only [real_inner_smul_right]
      _ = ∑ i, c i * y i := by simp only [hpu]
      _ = c ⬝ᵥ y := rfl
  -- residual squared = Schur scalar
  have hrr : ⟪r, r⟫_ℝ = ⟪w, w⟫_ℝ - y ⬝ᵥ (⅟(Matrix.gram ℝ u) *ᵥ y) := by
    have hwp : ⟪w, p⟫_ℝ = c ⬝ᵥ y := by rw [real_inner_comm]; exact hpw
    have hcomm : c ⬝ᵥ y = y ⬝ᵥ (⅟(Matrix.gram ℝ u) *ᵥ y) := by
      rw [dotProduct_comm, hc]
    have expand : ⟪r, r⟫_ℝ = ⟪w, w⟫_ℝ - ⟪w, p⟫_ℝ - ⟪p, w⟫_ℝ + ⟪p, p⟫_ℝ := by
      rw [hr, inner_sub_left, inner_sub_right, inner_sub_right]; ring
    rw [expand, hwp, hpw, hpp, hcomm]; ring
  -- `r ∈ Vᗮ`
  have hrperp : r ∈ Vᗮ := by
    rw [hV, Submodule.mem_orthogonal']
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        change ⟪r, u i⟫_ℝ = 0
        rw [hr, inner_sub_left, hpu i, real_inner_comm (u i) w, sub_self]
    | zero => exact inner_zero_right _
    | add a b _ _ ha hb => rw [inner_add_right, ha, hb, add_zero]
    | smul t a _ ha => rw [real_inner_smul_right, ha, mul_zero]
  -- `p ∈ V`
  have hp_mem : p ∈ V := by
    rw [hp, hV]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  -- `r = Vᗮ.starProjection w`
  have hproj : Vᗮ.starProjection w = r := by
    refine Submodule.eq_starProjection_of_mem_orthogonal' hrperp
      (V.le_orthogonal_orthogonal hp_mem) ?_
    rw [hr]; abel
  -- assemble
  rw [det_gram_cons_eq_det_gram_sumElim, gram_sumElim_eq_fromBlocks, Matrix.det_fromBlocks₁₁]
  congr 1
  rw [Matrix.det_unique, hproj, ← real_inner_self_eq_norm_sq, hrr, Matrix.sub_apply,
    Matrix.mul_assoc]
  simp only [Matrix.of_apply, Matrix.mul_apply, dotProduct, Matrix.mulVec, hy]

/-- **Gram determinant row-residual recursion** (unconditional). Prepending a row `w` to a family
`u` multiplies the Gram determinant by the squared residual of `w` off `span (range u)`. -/
theorem det_gram_cons (u : Fin n → E) (w : E) :
    (Matrix.gram ℝ (Fin.cons w u)).det
      = (Matrix.gram ℝ u).det
        * ‖(Submodule.span ℝ (Set.range u))ᗮ.starProjection w‖ ^ 2 := by
  by_cases h : (Matrix.gram ℝ u).det = 0
  · rw [det_gram_cons_of_det_gram_zero u w h, h, zero_mul]
  · exact det_gram_cons_of_det_gram_ne_zero u w h

end DLNFibre.DLN.RLCT
