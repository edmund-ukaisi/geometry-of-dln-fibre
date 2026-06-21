import DLNFibre.DLN.RLCT.Foundations.S1G5
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Determinant
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1G5Charts` — the pivot blow-up chart node (R1 measure-side)

The reusable per-node atom for the R1 resolution charts: the **pivot blow-up** map on
`Fin (n+1) → ℝ` and the three obligations a `g5_step` node needs (`HasFDerivWithinAt`, the Jacobian
`det`, `InjOn`). Every blow-up node of the `(2,2,2)` cover (and the general-`M` atlas) is this map
on its active coordinate block: step-1 (A-pivot, `n = 3`, Jac `x³`), step-2 (E-pivot, `n = 2`, Jac
`s²`), step-3 (y0-pivot, `n = 3`, Jac `u³`) are all `pivotBlowup` on the pivot-block coordinates.

## The chart and its derivative
`pivotBlowup n x = (x₀, x₀·x₁, …, x₀·xₙ)` — pivot coordinate `0`, the rest scaled by it. Its fderiv
is `pivotBlowupDeriv`, the linear map `v ↦ (v₀, x₀vᵢ + xᵢv₀)`; lower-triangular (pivot row `e₀`, row
`i ≠ 0` = `x₀eᵢ + xᵢe₀`), so `det = x₀ⁿ` — the Jacobian weight that lands in the `g5_step`
`weightedThreshold` `ρ`-slot (`ofReal |det| · g ∘ φ`).

## The three node obligations (independent of the leaf set / the deeper-point pin)
- `pivotBlowup_hasFDerivWithinAt` — C¹ with fderiv `pivotBlowupDeriv` (on any set).
- `pivotBlowupDeriv_det` — `det (pivotBlowupDeriv n x) = (x 0)ⁿ` (lower-triangular diagonal
  product).
- `pivotBlowup_injOn` — injective off the pivot-zero locus `{x | x 0 = 0}` (recover `x₀ = y₀`,
  `xᵢ = yᵢ/y₀`); the `Z`-exceptional `g5_step` drops at the cover level.

These discharge the `g5_step` per-leaf `hφ'`/`hinj` (and supply the `det` for the integrand) once
the explicit chart family — `φᵢ`, `Vᵢ`, `Zᵢ`, the cover/disjointness — lands from the design. -/

open MeasureTheory Set Matrix
open scoped BigOperators
namespace DLNFibre.DLN.RLCT

/-- The pivot blow-up chart on `Fin (n+1) → ℝ`: `φ(x)₀ = x₀`, `φ(x)ᵢ = x₀·xᵢ` for `i ≠ 0`.
Pivot = coordinate 0; the step-1, 2, 3 blow-up charts are this shape on the active block. -/
noncomputable def pivotBlowup (n : ℕ) (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun i => if i = 0 then x 0 else x 0 * x i

/-- The fderiv of `pivotBlowup` at `x`: the linear map `v ↦ (v₀, x₀·vᵢ + xᵢ·v₀)`. Lower-triangular
(pivot row `e₀`, row `i ≠ 0` = `x₀·eᵢ + xᵢ·e₀`), so `det = x₀ⁿ`. -/
noncomputable def pivotBlowupDeriv (n : ℕ) (x : Fin (n + 1) → ℝ) :
    (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi (fun i =>
    if i = 0 then ContinuousLinearMap.proj 0
    else (x 0) • ContinuousLinearMap.proj i + (x i) • ContinuousLinearMap.proj 0)

/-- **(node C¹/Jac).** `pivotBlowup` has fderiv `pivotBlowupDeriv` within any set `s` at any `x`.
Componentwise (`hasFDerivWithinAt_pi''`): component `0` is the projection `x ↦ x 0`; component
`i ≠ 0` is `x ↦ x 0 * x i`, the product of two projections (`HasFDerivWithinAt.mul`). -/
theorem pivotBlowup_hasFDerivWithinAt (n : ℕ) (s : Set (Fin (n + 1) → ℝ)) (x : Fin (n + 1) → ℝ) :
    HasFDerivWithinAt (pivotBlowup n) (pivotBlowupDeriv n x) s x := by
  apply hasFDerivWithinAt_pi''
  intro i
  rw [pivotBlowupDeriv, ContinuousLinearMap.proj_pi]
  rcases eq_or_ne i 0 with rfl | hi
  · have hcomp : (fun y : Fin (n + 1) → ℝ => pivotBlowup n y 0) = (fun y => y 0) := by
      funext y; unfold pivotBlowup; rw [if_pos rfl]
    rw [if_pos rfl, hcomp]; exact hasFDerivWithinAt_apply 0 x s
  · have hcomp : (fun y : Fin (n + 1) → ℝ => pivotBlowup n y i) = (fun y => y 0 * y i) := by
      funext y; unfold pivotBlowup; rw [if_neg hi]
    rw [if_neg hi, hcomp]
    exact (hasFDerivWithinAt_apply 0 x s).mul (hasFDerivWithinAt_apply i x s)

/-- The matrix entry of `pivotBlowupDeriv` in the standard basis: row `0` is `e₀`; row `i ≠ 0` is
`x₀` on the diagonal plus `xᵢ` in column `0`. -/
private theorem pivotBlowupDeriv_toMatrix (n : ℕ) (x : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) :
    LinearMap.toMatrix' (pivotBlowupDeriv n x : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)) i j
      = (if i = 0 then (if j = 0 then (1 : ℝ) else 0)
         else (x 0) * (if j = i then 1 else 0) + (x i) * (if j = 0 then 1 else 0)) := by
  rw [LinearMap.toMatrix'_apply]
  change (pivotBlowupDeriv n x) (Pi.single j 1) i = _
  rw [pivotBlowupDeriv]
  simp only [ContinuousLinearMap.pi_apply]
  rcases eq_or_ne i 0 with rfl | hi
  · by_cases hj : j = 0 <;> simp [hj, eq_comm]
  · simp only [if_neg hi, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, Pi.single_apply, smul_eq_mul]
    by_cases hj1 : j = i <;> by_cases hj2 : j = 0 <;> simp_all [eq_comm]

/-- **(node Jac value).** `det (pivotBlowupDeriv n x) = (x 0)ⁿ`. The matrix is lower-triangular
(`BlockTriangular toDual`), so the determinant is the diagonal product `1 · (x 0)ⁿ`. This `|x₀|ⁿ` is
the Jacobian weight the `g5_step` change-of-variables puts in the `weightedThreshold` `ρ`-slot. -/
theorem pivotBlowupDeriv_det (n : ℕ) (x : Fin (n + 1) → ℝ) :
    (pivotBlowupDeriv n x).det = (x 0) ^ n := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix']
  set M := LinearMap.toMatrix' (pivotBlowupDeriv n x : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ))
    with hM
  have htri : M.BlockTriangular OrderDual.toDual := by
    intro i j hij
    rw [OrderDual.toDual_lt_toDual] at hij
    rw [hM, pivotBlowupDeriv_toMatrix]
    rcases eq_or_ne i 0 with rfl | hi
    · have hj0 : j ≠ 0 := by rintro rfl; exact absurd hij (lt_irrefl _)
      simp [hj0]
    · have hji : j ≠ i := ne_of_gt hij
      have hj0 : j ≠ 0 := by rintro rfl; exact absurd hij (Fin.not_lt_zero i)
      simp [if_neg hji, if_neg hj0]
  rw [Matrix.det_of_lowerTriangular M htri]
  have hdiag : ∀ i : Fin (n + 1), M i i = if i = 0 then 1 else x 0 := by
    intro i
    rw [hM, pivotBlowupDeriv_toMatrix]
    rcases eq_or_ne i 0 with rfl | hi
    · simp
    · simp [if_neg hi]
  rw [Finset.prod_congr rfl (fun i _ => hdiag i), Fin.prod_univ_succ]
  have hsucc : ∀ i : Fin n, (if Fin.succ i = 0 then (1 : ℝ) else x 0) = x 0 := by
    intro i; rw [if_neg (Fin.succ_ne_zero i)]
  rw [Finset.prod_congr rfl (fun i _ => hsucc i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  simp

/-- **(node inj).** `pivotBlowup` is injective off the pivot-zero locus `{x | x 0 = 0}`: on
`s \ {x | x 0 = 0}`, recover `x 0 = y 0` (component `0`) and `x i = y i / y 0` (`x 0 ≠ 0`). The
`g5_step` cover drops this `Z`-exceptional at the cover level. -/
theorem pivotBlowup_injOn (n : ℕ) (s : Set (Fin (n + 1) → ℝ)) :
    InjOn (pivotBlowup n) (s \ {x | x 0 = 0}) := by
  rintro x ⟨_, hx⟩ y ⟨_, _⟩ hxy
  simp only [Set.mem_setOf_eq] at hx
  have hx0 : x 0 ≠ 0 := hx
  funext i
  rcases eq_or_ne i 0 with rfl | hi
  · have := congrFun hxy 0; simpa [pivotBlowup] using this
  · have h0 : x 0 = y 0 := by have := congrFun hxy 0; simpa [pivotBlowup] using this
    have hi' := congrFun hxy i
    simp only [pivotBlowup, if_neg hi] at hi'
    rw [← h0] at hi'
    exact mul_left_cancel₀ hx0 hi'

/-! ## The argmax cover (the `g5_step` `hcover`/`hdisj` discharge — the cover wall)

The pivot-blow-up FAMILY (one chart per pivot `p`) covers `{y ≠ 0}` up to the null tie-set, a.e.-
disjointly. The chart's fundamental domain bounds the NON-pivot coordinates (`|x j| ≤ 1` for
`j ≠ p`; the pivot `x p` is free), so the pivot blow-up at `p` maps it ONTO the weak-argmax cell at
`p` — the `g5_step` per-chart image. Cover by a finite argmax (`Finset.exists_max_image`);
disjointness because two argmax cells meet only on the null hyperplane pair `{|y p| = |y q|}`
(proper subspaces, Haar-null via `addHaar_submodule`). Structure Codex-confirmed (no bundled
Mathlib argmax-cover lemma). -/

/-- The pivot blow-up at coordinate `p`: `φ(x)_p = x_p`, `φ(x)_j = x_p · x_j` for `j ≠ p`. The
general pivot (`pivotBlowup n = pivotBlowupAt n 0`); the `(2,2,2)` step-1 = the 4 A-pivots. -/
noncomputable def pivotBlowupAt (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun i => if i = p then x p else x p * x i

/-- The weak-argmax cell at `p`: `{y | y p ≠ 0 ∧ ∀ j, |y j| ≤ |y p|}` (the `g5_step` image). -/
def argmaxCell (n : ℕ) (p : Fin (n + 1)) : Set (Fin (n + 1) → ℝ) :=
  {y | y p ≠ 0 ∧ ∀ j, |y j| ≤ |y p|}

/-- The chart fundamental domain: non-pivot coordinates bounded by `1` (the pivot `x p` is free). -/
def chartDom (n : ℕ) (p : Fin (n + 1)) : Set (Fin (n + 1) → ℝ) := {x | ∀ j, j ≠ p → |x j| ≤ 1}

/-- The chart exceptional locus (the pivot-zero hyperplane). -/
def pivotZero (n : ℕ) (p : Fin (n + 1)) : Set (Fin (n + 1) → ℝ) := {x | x p = 0}

/-- **(cover image char).** The pivot-`p` blow-up maps its fundamental domain (off the pivot-zero
locus) ONTO the weak-argmax cell: `φ_p '' (chartDom \ pivotZero) = argmaxCell p`. Forward: `|y j| =
|x p|·|x j| ≤ |x p| = |y p|` (`|x j| ≤ 1`). Backward: `x p = y p`, `x j = y j / y p` (`|x j| ≤ 1`
from `|y j| ≤ |y p|`). The `g5_step` per-chart image set (with this `V \ Z`). -/
theorem pivotBlowupAt_image (n : ℕ) (p : Fin (n + 1)) :
    (pivotBlowupAt n p) '' (chartDom n p \ pivotZero n p) = argmaxCell n p := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxdom, hxnz⟩, rfl⟩
    simp only [chartDom, Set.mem_setOf_eq] at hxdom
    simp only [pivotZero, Set.mem_setOf_eq] at hxnz
    refine ⟨by simp only [pivotBlowupAt]; exact hxnz, fun j => ?_⟩
    rcases eq_or_ne j p with rfl | hj
    · simp only [pivotBlowupAt]; exact le_refl _
    · simp only [pivotBlowupAt, if_neg hj, abs_mul]
      calc |x p| * |x j| ≤ |x p| * 1 := mul_le_mul_of_nonneg_left (hxdom j hj) (abs_nonneg _)
        _ = |x p| := mul_one _
  · rintro ⟨hyp, hybound⟩
    refine ⟨fun i => if i = p then y p else y i / y p, ⟨fun j hj => ?_, ?_⟩, ?_⟩
    · simp only [if_neg hj, abs_div, div_le_one (abs_pos.2 hyp)]; exact hybound j
    · simp only [pivotZero, Set.mem_setOf_eq]; exact hyp
    · funext i
      rcases eq_or_ne i p with rfl | hi
      · simp [pivotBlowupAt]
      · show pivotBlowupAt n p _ i = y i
        simp only [pivotBlowupAt, if_neg hi, if_true]
        rw [mul_div_cancel₀ _ hyp]

/-- **(cover).** The argmax cells cover the nonzero set EXACTLY: `{y ≠ 0} = ⋃ p, argmaxCell p`. `⊇`:
each cell has `y p ≠ 0`. `⊆`: for `y ≠ 0`, the argmax `p` of `|y ·|` has `y p ≠ 0` and dominates all
coordinates (`Finset.exists_max_image`). -/
theorem argmaxCell_cover (n : ℕ) :
    {y : Fin (n + 1) → ℝ | y ≠ 0} = ⋃ p : Fin (n + 1), argmaxCell n p := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, argmaxCell]
  constructor
  · intro hy
    obtain ⟨p, _, hp⟩ :=
      Finset.exists_max_image Finset.univ (fun j => |y j|) ⟨0, Finset.mem_univ 0⟩
    refine ⟨p, ?_, fun j => hp j (Finset.mem_univ j)⟩
    intro hyp0
    apply hy
    funext j
    have hj := hp j (Finset.mem_univ j)
    rw [hyp0, abs_zero] at hj
    simpa using abs_nonpos_iff.1 hj
  · rintro ⟨p, hyp, _⟩ hy0
    exact hyp (by rw [hy0]; rfl)

/-- The eq-abs-coordinate set `{y | |y p| = |y q|}` is Haar-null for `p ≠ q`: it lies in the union
of the two hyperplanes `ker (proj p ∓ proj q)`, both proper subspaces (`addHaar_submodule`). -/
private theorem absEq_null {N : ℕ} (p q : Fin N) (hpq : p ≠ q) :
    (volume : Measure (Fin N → ℝ)) {y | |y p| = |y q|} = 0 := by
  let fm : (Fin N → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj p : (Fin N → ℝ) →ₗ[ℝ] ℝ) - (LinearMap.proj q : (Fin N → ℝ) →ₗ[ℝ] ℝ)
  let fp : (Fin N → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj p : (Fin N → ℝ) →ₗ[ℝ] ℝ) + (LinearMap.proj q : (Fin N → ℝ) →ₗ[ℝ] ℝ)
  have hsub : {y : Fin N → ℝ | |y p| = |y q|}
      ⊆ (↑(LinearMap.ker fm) : Set _) ∪ (↑(LinearMap.ker fp) : Set _) := by
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    rcases abs_eq_abs.1 hy with h | h
    · left; simp only [SetLike.mem_coe, LinearMap.mem_ker, fm, LinearMap.sub_apply,
        LinearMap.proj_apply, sub_eq_zero]; exact h
    · right; simp only [SetLike.mem_coe, LinearMap.mem_ker, fp, LinearMap.add_apply,
        LinearMap.proj_apply, add_eq_zero_iff_eq_neg]; exact h
  apply measure_mono_null hsub
  rw [measure_union_null_iff]
  refine ⟨MeasureTheory.Measure.addHaar_submodule _ _ ?_,
    MeasureTheory.Measure.addHaar_submodule _ _ ?_⟩
  · intro htop
    have hmem : (Pi.single p (1 : ℝ)) ∈ LinearMap.ker fm := htop ▸ Submodule.mem_top
    simp only [LinearMap.mem_ker, fm, LinearMap.sub_apply, LinearMap.proj_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hpq), sub_zero, one_ne_zero] at hmem
  · intro htop
    have hmem : (Pi.single p (1 : ℝ)) ∈ LinearMap.ker fp := htop ▸ Submodule.mem_top
    simp only [LinearMap.mem_ker, fp, LinearMap.add_apply, LinearMap.proj_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hpq), add_zero, one_ne_zero] at hmem

/-- **(disjoint).** Distinct argmax cells are a.e.-disjoint: their overlap forces `|y p| = |y q|`
(`|y q| ≤ |y p|` from the `p`-cell, `|y p| ≤ |y q|` from the `q`-cell): a null set (`absEq_null`).
The `g5_step` `hdisj`. -/
theorem argmaxCell_aedisjoint (n : ℕ) (p q : Fin (n + 1)) (hpq : p ≠ q) :
    AEDisjoint volume (argmaxCell n p) (argmaxCell n q) := by
  have hov : argmaxCell n p ∩ argmaxCell n q ⊆ {y | |y p| = |y q|} := by
    rintro y ⟨⟨_, hp⟩, ⟨_, hq⟩⟩
    exact le_antisymm (hq p) (hp q)
  exact measure_mono_null hov (absEq_null p q hpq)

/-! ## The spectator-product extension (each `(2,2,2)` node has SPECTATOR coordinates)

A blow-up node acts on a sub-block (the pivot block) while the other coordinates are SPECTATORS
(passed through, ranging over a bounded box `S`). The chart is `pivotBlowupAt ⊗ id` on the product
`(Fin (n+1) → ℝ) × W`, with `Vᵢ = chartDom ×ˢ S`, `Zᵢ = pivotZero ×ˢ univ`. Cover and
a.e.-disjointness reduce to the active-block argmax (the spectator factor is common): step-1 has the
`B`-block as `W`, step-2 has `q,G,H` as `W`. -/

/-- The product chart `pivotBlowupAt n p` on the active block, identity on the spectator `W`. -/
noncomputable def pivotBlowupProd (n : ℕ) (p : Fin (n + 1)) {W : Type*}
    (x : (Fin (n + 1) → ℝ) × W) : (Fin (n + 1) → ℝ) × W :=
  (pivotBlowupAt n p x.1, x.2)

/-- The product chart domain: the active max-region `chartDom` times the spectator box `S`. -/
def chartDomProd (n : ℕ) (p : Fin (n + 1)) {W : Type*} (S : Set W) :
    Set ((Fin (n + 1) → ℝ) × W) := (chartDom n p) ×ˢ S

/-- The product exceptional locus: the active pivot-zero hyperplane (any spectator). -/
def pivotZeroProd (n : ℕ) (p : Fin (n + 1)) {W : Type*} :
    Set ((Fin (n + 1) → ℝ) × W) := (pivotZero n p) ×ˢ (Set.univ)

/-- **(product image char).** `pivotBlowupProd '' (chartDomProd \ pivotZeroProd) = argmaxCell ×ˢ S`
— the active blow-up image (`pivotBlowupAt_image`) times the spectator box. -/
theorem pivotBlowupProd_image (n : ℕ) (p : Fin (n + 1)) {W : Type*} (S : Set W) :
    (pivotBlowupProd n p) '' (chartDomProd n p S \ pivotZeroProd n p)
      = (argmaxCell n p) ×ˢ S := by
  have hdom : (chartDomProd n p S \ pivotZeroProd n p (W := W))
      = (chartDom n p \ pivotZero n p) ×ˢ S := by
    ext ⟨a, b⟩
    simp only [chartDomProd, pivotZeroProd, Set.mem_diff, Set.mem_prod, Set.mem_univ, and_true]
    tauto
  rw [hdom, ← pivotBlowupAt_image n p]
  ext ⟨y, w⟩
  simp only [pivotBlowupProd, Set.mem_image, Set.mem_prod, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, hb⟩
  · rintro ⟨⟨a, ha, rfl⟩, hw⟩
    exact ⟨a, w, ⟨ha, hw⟩, rfl, rfl⟩

/-- **(product cover).** The product cells cover the active-nonzero × spectator-box set exactly. -/
theorem argmaxCellProd_cover (n : ℕ) {W : Type*} (S : Set W) :
    {x : (Fin (n + 1) → ℝ) × W | x.1 ≠ 0 ∧ x.2 ∈ S}
      = ⋃ p : Fin (n + 1), (argmaxCell n p) ×ˢ S := by
  have hbase := argmaxCell_cover n
  ext ⟨y, w⟩
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod]
  constructor
  · rintro ⟨hy, hw⟩
    have hmem : y ∈ ⋃ p, argmaxCell n p := by rw [← hbase]; exact hy
    rw [Set.mem_iUnion] at hmem
    obtain ⟨p, hp⟩ := hmem
    exact ⟨p, hp, hw⟩
  · rintro ⟨p, hp, hw⟩
    refine ⟨?_, hw⟩
    have hmem : y ∈ ⋃ p, argmaxCell n p := Set.mem_iUnion.2 ⟨p, hp⟩
    rw [← hbase] at hmem
    exact hmem

/-- **(product disjoint).** Distinct product cells are a.e.-disjoint: the overlap is
`(argmaxCell p ∩ argmaxCell q) ×ˢ S`, null because the active overlap is null
(`argmaxCell_aedisjoint`) and `volume (null ×ˢ S) = 0 · volume S = 0`. -/
theorem argmaxCellProd_aedisjoint {W : Type*} [MeasureSpace W] [SFinite (volume : Measure W)]
    (n : ℕ) (p q : Fin (n + 1)) (hpq : p ≠ q) (S : Set W) :
    AEDisjoint volume ((argmaxCell n p) ×ˢ S) ((argmaxCell n q) ×ˢ S) := by
  have hnull := argmaxCell_aedisjoint n p q hpq
  unfold AEDisjoint at hnull ⊢
  rw [Set.prod_inter_prod, Set.inter_self, Measure.volume_eq_prod, Measure.prod_prod, hnull,
    zero_mul]

/-- **(cell measurability).** `argmaxCell p` is Borel: a finite intersection of measurable
coordinate conditions (`y p ≠ 0` and each `|y j| ≤ |y p|`). Supports the `g5_step` `hmeas`
(`NullMeasurableSet` of the chart image). -/
theorem argmaxCell_measurableSet (n : ℕ) (p : Fin (n + 1)) :
    MeasurableSet (argmaxCell n p) := by
  have h1 : MeasurableSet {y : Fin (n + 1) → ℝ | y p ≠ 0} := by
    have hpre : {y : Fin (n + 1) → ℝ | y p ≠ 0} = (fun y => y p) ⁻¹' {0}ᶜ := by
      ext y; simp [Set.mem_preimage]
    rw [hpre]; exact (measurable_pi_apply p) (measurableSet_singleton 0).compl
  have h2 : MeasurableSet {y : Fin (n + 1) → ℝ | ∀ j, |y j| ≤ |y p|} := by
    rw [Set.setOf_forall]
    refine MeasurableSet.iInter (fun j => ?_)
    have hj : Measurable (fun y : Fin (n + 1) → ℝ => |y j|) := by fun_prop
    have hp : Measurable (fun y : Fin (n + 1) → ℝ => |y p|) := by fun_prop
    exact measurableSet_le hj hp
  exact h1.inter h2

/-! ## The flat coordinate-subset cover (the form that plugs into `g5_step` on `Fin N → ℝ`)

`g5_step` requires `E` to carry `IsAddHaarMeasure`; the product `(Fin k → ℝ) × W` does NOT
auto-synth it, but the flat `Fin N → ℝ` does — so the `(2,2,2)` cover runs on flat `Fin 8 → ℝ` with
the active block expressed as a coordinate SUBSET (spectators are the inactive coords, passed
through). This is the `g5_step`-ready cover; the three nodes are instances (`active` = the A-block /
`(E,F0,δ)`-slots / the 4-block). Argmax over `active`; cover is `{∃ active coord ≠ 0}`. -/

/-- The argmax cell over a coordinate SUBSET `active`, pivot `p`: `y p ≠ 0` and `p` dominates the
active coords (the inactive/spectator coords are free). -/
def argmaxCellOn {N : ℕ} (active : Finset (Fin N)) (p : Fin N) : Set (Fin N → ℝ) :=
  {y | y p ≠ 0 ∧ ∀ j ∈ active, |y j| ≤ |y p|}

/-- **(subset cover).** The active-pivot cells cover `{some active coord ≠ 0}` exactly: for such
a `y`, the argmax `p` over `active` of `|y ·|` dominates and is nonzero (`exists_max_image`). -/
theorem argmaxCellOn_cover {N : ℕ} (active : Finset (Fin N)) :
    {y : Fin N → ℝ | ∃ j ∈ active, y j ≠ 0} = ⋃ p ∈ active, argmaxCellOn active p := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, argmaxCellOn, exists_prop]
  constructor
  · rintro ⟨j0, hj0a, hj0⟩
    obtain ⟨p, hpa, hp⟩ := active.exists_max_image (fun j => |y j|) ⟨j0, hj0a⟩
    refine ⟨p, hpa, ?_, fun j hj => hp j hj⟩
    intro hyp0
    have hle : |y j0| ≤ |y p| := hp j0 hj0a
    rw [hyp0, abs_zero] at hle
    exact hj0 (abs_eq_zero.1 (le_antisymm hle (abs_nonneg _)))
  · rintro ⟨p, hpa, hyp, _⟩
    exact ⟨p, hpa, hyp⟩

/-- **(subset disjoint).** Distinct active-pivot cells (`p, q ∈ active`) are a.e.-disjoint: the
overlap forces `|y p| = |y q|` (each pivot dominates the other, both being active): a null set. -/
theorem argmaxCellOn_aedisjoint {N : ℕ} (active : Finset (Fin N)) (p q : Fin N)
    (hp : p ∈ active) (hq : q ∈ active) (hpq : p ≠ q) :
    AEDisjoint volume (argmaxCellOn active p) (argmaxCellOn active q) := by
  have hov : argmaxCellOn active p ∩ argmaxCellOn active q ⊆ {y | |y p| = |y q|} := by
    rintro y ⟨⟨_, hpd⟩, ⟨_, hqd⟩⟩
    exact le_antisymm (hqd p hp) (hpd q hq)
  exact measure_mono_null hov (absEq_null p q hpq)

/-! ## The flat-subset chart map and its per-node obligations (`hφ'`/`hinj`/image)

`pivotBlowupOn active p` blows up the active block at pivot `p` on flat `Fin N → ℝ`, identity on the
inactive (spectator) coords. Its fderiv is `pivotBlowupOnDeriv` (an "arrow" linear map: diagonal +
pivot column); `InjOn` off `{x p = 0}`; image of the bounded chart domain = `argmaxCellOn`. These
are the flat-carrier analogues of the full-block `pivotBlowup` node. The Jacobian
`det = (x p)^(active.card-1)` is handled separately. -/

/-- The flat-subset pivot blow-up: pivot `x_p`, active `j ≠ p` ↦ `x_p·x_j`, spectators fixed. -/
noncomputable def pivotBlowupOn {N : ℕ} (active : Finset (Fin N)) (p : Fin N) (x : Fin N → ℝ) :
    Fin N → ℝ :=
  fun i => if i = p then x p else if i ∈ active then x p * x i else x i

/-- The fderiv of `pivotBlowupOn`: the arrow map `v ↦ (v_p at p; x_p·v_i + x_i·v_p at active i≠p;
v_i at spectators)`. -/
noncomputable def pivotBlowupOnDeriv {N : ℕ} (active : Finset (Fin N)) (p : Fin N) (x : Fin N → ℝ) :
    (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi (fun i =>
    if i = p then ContinuousLinearMap.proj p
    else if i ∈ active then (x p) • ContinuousLinearMap.proj i + (x i) • ContinuousLinearMap.proj p
    else ContinuousLinearMap.proj i)

/-- The flat-subset chart domain (active non-pivot coords bounded; pivot and spectators free). -/
def chartDomOn {N : ℕ} (active : Finset (Fin N)) (p : Fin N) : Set (Fin N → ℝ) :=
  {x | ∀ j ∈ active, j ≠ p → |x j| ≤ 1}

/-- The flat-subset exceptional locus (the pivot-zero hyperplane). -/
def pivotZeroOn {N : ℕ} (p : Fin N) : Set (Fin N → ℝ) := {x | x p = 0}

/-- **(node C¹).** `pivotBlowupOn` has fderiv `pivotBlowupOnDeriv` on any set: componentwise the
pivot/spectator rows are projections, the active rows are products of two projections. -/
theorem pivotBlowupOn_hasFDerivWithinAt {N : ℕ} (active : Finset (Fin N)) (p : Fin N)
    (s : Set (Fin N → ℝ)) (x : Fin N → ℝ) :
    HasFDerivWithinAt (pivotBlowupOn active p) (pivotBlowupOnDeriv active p x) s x := by
  apply hasFDerivWithinAt_pi''
  intro i
  rw [pivotBlowupOnDeriv, ContinuousLinearMap.proj_pi]
  rcases eq_or_ne i p with rfl | hi
  · have hc : (fun y : Fin N → ℝ => pivotBlowupOn active i y i) = (fun y => y i) := by
      funext y; unfold pivotBlowupOn; rw [if_pos rfl]
    rw [if_pos rfl, hc]; exact hasFDerivWithinAt_apply i x s
  · by_cases ha : i ∈ active
    · have hc : (fun y : Fin N → ℝ => pivotBlowupOn active p y i) = (fun y => y p * y i) := by
        funext y; unfold pivotBlowupOn; rw [if_neg hi, if_pos ha]
      rw [if_neg hi, if_pos ha, hc]
      exact (hasFDerivWithinAt_apply p x s).mul (hasFDerivWithinAt_apply i x s)
    · have hc : (fun y : Fin N → ℝ => pivotBlowupOn active p y i) = (fun y => y i) := by
        funext y; unfold pivotBlowupOn; rw [if_neg hi, if_neg ha]
      rw [if_neg hi, if_neg ha, hc]; exact hasFDerivWithinAt_apply i x s

/-- **(node inj).** `pivotBlowupOn` is injective off `{x p = 0}`: `x p = y p` (pivot), `x i = y i`
(active via `mul_left_cancel`, spectators directly). -/
theorem pivotBlowupOn_injOn {N : ℕ} (active : Finset (Fin N)) (p : Fin N) (s : Set (Fin N → ℝ)) :
    InjOn (pivotBlowupOn active p) (s \ {x | x p = 0}) := by
  rintro x ⟨_, hx⟩ y ⟨_, _⟩ hxy
  simp only [Set.mem_setOf_eq] at hx
  have hx0 : x p ≠ 0 := hx
  have hpeq : x p = y p := by have := congrFun hxy p; simpa [pivotBlowupOn] using this
  funext i
  rcases eq_or_ne i p with rfl | hi
  · exact hpeq
  · by_cases ha : i ∈ active
    · have hi' := congrFun hxy i
      simp only [pivotBlowupOn, if_neg hi, if_pos ha] at hi'
      rw [← hpeq] at hi'
      exact mul_left_cancel₀ hx0 hi'
    · have hi' := congrFun hxy i
      simp only [pivotBlowupOn, if_neg hi, if_neg ha] at hi'
      exact hi'

/-- **(image char).** `pivotBlowupOn '' (chartDomOn \ pivotZeroOn) = argmaxCellOn active p`
(`p ∈ active`). Forward: `|x_p·x_j| ≤ |x_p|` (active `|x_j| ≤ 1`); spectators free. Backward: `x_p =
y_p`, active `x_j = y_j/y_p` (`|x_j| ≤ 1`), spectators `x_i = y_i`. -/
theorem pivotBlowupOn_image {N : ℕ} (active : Finset (Fin N)) (p : Fin N) (hp : p ∈ active) :
    (pivotBlowupOn active p) '' (chartDomOn active p \ pivotZeroOn p) = argmaxCellOn active p := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxdom, hxnz⟩, rfl⟩
    simp only [chartDomOn, Set.mem_setOf_eq] at hxdom
    simp only [pivotZeroOn, Set.mem_setOf_eq] at hxnz
    refine ⟨by simp only [pivotBlowupOn]; exact hxnz, fun j hj => ?_⟩
    rcases eq_or_ne j p with rfl | hjp
    · simp only [pivotBlowupOn]; exact le_refl _
    · simp only [pivotBlowupOn, if_neg hjp, if_pos hj, abs_mul]
      calc |x p| * |x j| ≤ |x p| * 1 :=
            mul_le_mul_of_nonneg_left (hxdom j hj hjp) (abs_nonneg _)
        _ = |x p| := mul_one _
  · rintro ⟨hyp, hybound⟩
    refine ⟨fun i => if i = p then y p else if i ∈ active then y i / y p else y i,
      ⟨fun j hj hjp => ?_, ?_⟩, ?_⟩
    · simp only [if_neg hjp, if_pos hj, abs_div, div_le_one (abs_pos.2 hyp)]; exact hybound j hj
    · simp only [pivotZeroOn, Set.mem_setOf_eq]; exact hyp
    · funext i
      rcases eq_or_ne i p with rfl | hip
      · simp [pivotBlowupOn]
      · by_cases ha : i ∈ active
        · show pivotBlowupOn active p _ i = y i
          simp only [pivotBlowupOn, if_neg hip, if_pos ha, if_true]
          rw [mul_div_cancel₀ _ hyp]
        · show pivotBlowupOn active p _ i = y i
          simp only [pivotBlowupOn, if_neg hip, if_neg ha]

end DLNFibre.DLN.RLCT
