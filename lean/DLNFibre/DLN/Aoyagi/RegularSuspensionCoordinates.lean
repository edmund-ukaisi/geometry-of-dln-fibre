import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import DLNFibre.DLN.Aoyagi.ProductReductionEntryIdealBoundary
import DLNFibre.DLN.Aoyagi.FinalFormula
import DLNFibre.DLN.Aoyagi.Definition3RankWidthBridge

/-!
# Scalar coordinate indices for Aoyagi's p. 13 blocks

This file scalarizes the three regular block families appearing after
Aoyagi's product reduction:

* `Ctop - 1`,
* `F2`,
* `F3`.

It also scalarizes the residual `D` block while keeping those coordinates
separate from the regular-coordinate index and regular-variable shift.  It
proves finite coordinate bookkeeping and componentwise continuity projections,
plus the algebraic bridge from tagged scalar-coordinate values to the relevant
matrix-entry ideals.  It does not construct a regular-suspension chart, prove
analytic ideal transport, prove chart coverage, prove Jacobian compatibility,
produce normal crossings, or extract pole order/RLCT.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

open Matrix

set_option linter.style.longLine false

universe uι uμ uν

/-- Finite algebraic square-sum attached to a scalar coordinate family.

This is the square-sum convention for a finite generator family.  It is not an
analytic norm, chart statement, or RLCT statement. -/
def aoyagiCoordinateSquareSum
    {η R : Type*} [Fintype η] [CommSemiring R] (f : η → R) : R :=
  ∑ c, f c ^ 2

/-- The square-sum over a disjoint sum of coordinate indices is the sum of the
two square-sums. -/
@[simp]
theorem aoyagiCoordinateSquareSum_sumElim
    {η κ R : Type*} [Fintype η] [Fintype κ] [CommSemiring R]
    (f : η → R) (g : κ → R) :
    aoyagiCoordinateSquareSum (Sum.elim f g) =
      aoyagiCoordinateSquareSum f + aoyagiCoordinateSquareSum g := by
  simp [aoyagiCoordinateSquareSum, Fintype.sum_sum_type]

/-- A finite coordinate square-sum is nonnegative over an ordered scalar
ring. -/
theorem aoyagiCoordinateSquareSum_nonneg
    {η R : Type*} [Fintype η] [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (f : η → R) :
    0 ≤ aoyagiCoordinateSquareSum f := by
  exact Finset.sum_nonneg (fun c _ => sq_nonneg (f c))

/-- Pointwise square estimate used to compare corrected and uncorrected
finite square-sums. -/
theorem aoyagi_sq_sub_le_two_mul_sq_add_two_mul_sq
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (a b : R) :
    (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a + b)]

/-- Pointwise square estimate for a sum. -/
theorem aoyagi_sq_add_le_two_mul_sq_add_two_mul_sq
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (a b : R) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- Finite square-sum estimate for coordinatewise subtraction. -/
theorem aoyagiCoordinateSquareSum_sub_le_two_mul_add_two_mul
    {η R : Type*} [Fintype η] [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (f g : η → R) :
    aoyagiCoordinateSquareSum (fun c => f c - g c) ≤
      2 * aoyagiCoordinateSquareSum f + 2 * aoyagiCoordinateSquareSum g := by
  classical
  unfold aoyagiCoordinateSquareSum
  calc
    ∑ c, (f c - g c) ^ 2 ≤
        ∑ c, (2 * f c ^ 2 + 2 * g c ^ 2) := by
      exact Finset.sum_le_sum
        (fun c _ => aoyagi_sq_sub_le_two_mul_sq_add_two_mul_sq (f c) (g c))
    _ = (∑ c, 2 * f c ^ 2) + ∑ c, 2 * g c ^ 2 := by
      rw [Finset.sum_add_distrib]
    _ = 2 * (∑ c, f c ^ 2) + 2 * ∑ c, g c ^ 2 := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- Finite square-sum estimate for coordinatewise addition. -/
theorem aoyagiCoordinateSquareSum_add_le_two_mul_add_two_mul
    {η R : Type*} [Fintype η] [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (f g : η → R) :
    aoyagiCoordinateSquareSum (fun c => f c + g c) ≤
      2 * aoyagiCoordinateSquareSum f + 2 * aoyagiCoordinateSquareSum g := by
  classical
  unfold aoyagiCoordinateSquareSum
  calc
    ∑ c, (f c + g c) ^ 2 ≤
        ∑ c, (2 * f c ^ 2 + 2 * g c ^ 2) := by
      exact Finset.sum_le_sum
        (fun c _ => aoyagi_sq_add_le_two_mul_sq_add_two_mul_sq (f c) (g c))
    _ = (∑ c, 2 * f c ^ 2) + ∑ c, 2 * g c ^ 2 := by
      rw [Finset.sum_add_distrib]
    _ = 2 * (∑ c, f c ^ 2) + 2 * ∑ c, g c ^ 2 := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- A finite real coordinate square-sum is continuous at a point when the
coordinate family is continuous there. -/
theorem aoyagiCoordinateSquareSum_continuousAt
    {η α : Type*} [Fintype η] [TopologicalSpace α]
    {f : α → η → ℝ} {x₀ : α}
    (hf : ContinuousAt f x₀) :
    ContinuousAt (fun x : α => aoyagiCoordinateSquareSum (f x)) x₀ := by
  classical
  unfold aoyagiCoordinateSquareSum
  change ContinuousAt (fun x : α => ∑ c : η, (f x c) ^ 2) x₀
  refine Finset.induction_on (s := (Finset.univ : Finset η)) ?_ ?_
  · simpa using (continuousAt_const : ContinuousAt (fun _ : α => (0 : ℝ)) x₀)
  · intro c s hcs ih
    have hterm : ContinuousAt (fun x : α => (f x c) ^ 2) x₀ :=
      (((continuous_apply c).continuousAt.comp hf).pow 2)
    simpa [Finset.sum_insert, hcs] using hterm.add ih

/-- Centered continuity lets one shrink to a neighborhood where the finite real
coordinate square-sum is at most `1`. -/
theorem aoyagiCoordinateSquareSum_eventually_le_one_of_continuousAt_zero
    {η α : Type*} [Fintype η] [TopologicalSpace α]
    {f : α → η → ℝ} {x₀ : α}
    (h0 : f x₀ = 0)
    (hf : ContinuousAt f x₀) :
    ∀ᶠ x in nhds x₀, aoyagiCoordinateSquareSum (f x) ≤ 1 := by
  have hs :
      ContinuousAt (fun x : α => aoyagiCoordinateSquareSum (f x)) x₀ :=
    aoyagiCoordinateSquareSum_continuousAt hf
  have hcenter :
      aoyagiCoordinateSquareSum (f x₀) = (0 : ℝ) := by
    simp [aoyagiCoordinateSquareSum, h0]
  have hsmall :
      ∀ᶠ y in nhds (aoyagiCoordinateSquareSum (f x₀)), y ≤ (1 : ℝ) := by
    simpa [hcenter] using (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
  exact hs.eventually hsmall

/-- Centered continuity of two finite real coordinate families gives a
neighborhood where their square-sums have total at most `1`. -/
theorem aoyagiCoordinateSquareSum_add_eventually_le_one_of_continuousAt_zero
    {η κ α : Type*} [Fintype η] [Fintype κ] [TopologicalSpace α]
    {f : α → η → ℝ} {g : α → κ → ℝ} {x₀ : α}
    (hf0 : f x₀ = 0)
    (hg0 : g x₀ = 0)
    (hf : ContinuousAt f x₀)
    (hg : ContinuousAt g x₀) :
    ∀ᶠ x in nhds x₀,
      aoyagiCoordinateSquareSum (f x) + aoyagiCoordinateSquareSum (g x) ≤ 1 := by
  let F : α → (η ⊕ κ) → ℝ := fun x => Sum.elim (f x) (g x)
  have hF0 : F x₀ = 0 := by
    funext c
    cases c <;> simp [F, hf0, hg0]
  have hF : ContinuousAt F x₀ := by
    refine continuousAt_pi.2 ?_
    intro c
    cases c with
    | inl c =>
        exact ((continuous_apply c).continuousAt.comp hf)
    | inr c =>
        exact ((continuous_apply c).continuousAt.comp hg)
  have hsmall :
      ∀ᶠ x in nhds x₀, aoyagiCoordinateSquareSum (F x) ≤ 1 :=
    aoyagiCoordinateSquareSum_eventually_le_one_of_continuousAt_zero hF0 hF
  filter_upwards [hsmall] with x hx
  simpa [F, aoyagiCoordinateSquareSum_sumElim] using hx

/-- Scalar centered-continuity data for each coordinate is enough to shrink to
a neighborhood where the finite real square-sum is at most `1`. -/
theorem aoyagiCoordinateSquareSum_eventually_le_one_of_forall_centered_continuousAt
    {η α : Type*} [Fintype η] [TopologicalSpace α]
    {f : α → η → ℝ} {x₀ : α}
    (hf : ∀ c, f x₀ c = 0 ∧ ContinuousAt (fun x : α => f x c) x₀) :
    ∀ᶠ x in nhds x₀, aoyagiCoordinateSquareSum (f x) ≤ 1 := by
  have h0 : f x₀ = 0 := by
    funext c
    exact (hf c).1
  have hcont : ContinuousAt f x₀ :=
    continuousAt_pi' (fun c => (hf c).2)
  exact aoyagiCoordinateSquareSum_eventually_le_one_of_continuousAt_zero h0 hcont

/-- Scalar centered-continuity data for two finite real coordinate families is
enough to shrink to a neighborhood where their square-sums total at most `1`. -/
theorem aoyagiCoordinateSquareSum_add_eventually_le_one_of_forall_centered_continuousAt
    {η κ α : Type*} [Fintype η] [Fintype κ] [TopologicalSpace α]
    {f : α → η → ℝ} {g : α → κ → ℝ} {x₀ : α}
    (hf : ∀ c, f x₀ c = 0 ∧ ContinuousAt (fun x : α => f x c) x₀)
    (hg : ∀ c, g x₀ c = 0 ∧ ContinuousAt (fun x : α => g x c) x₀) :
    ∀ᶠ x in nhds x₀,
      aoyagiCoordinateSquareSum (f x) + aoyagiCoordinateSquareSum (g x) ≤ 1 := by
  have hf0 : f x₀ = 0 := by
    funext c
    exact (hf c).1
  have hg0 : g x₀ = 0 := by
    funext c
    exact (hg c).1
  have hfcont : ContinuousAt f x₀ :=
    continuousAt_pi' (fun c => (hf c).2)
  have hgcont : ContinuousAt g x₀ :=
    continuousAt_pi' (fun c => (hg c).2)
  exact aoyagiCoordinateSquareSum_add_eventually_le_one_of_continuousAt_zero
    hf0 hg0 hfcont hgcont

/-- Scalar coordinates for the three regular block families
`Ctop - 1`, `F2`, and `F3`.

The type parameters are:
* `ι`: the rank-`r` through-coordinate index;
* `μ`: the row/left-endpoint residual-coordinate index;
* `ν`: the column/right-endpoint residual-coordinate index. -/
abbrev AoyagiRegularBlockCoordinateIndex
    (ι : Type uι) (μ : Type uμ) (ν : Type uν) :
    Type (max uι uμ uν) :=
  (ι × ι) ⊕ ((ι × ν) ⊕ (μ × ι))

namespace AoyagiRegularBlockCoordinateIndex

variable {ι μ ν R α : Type*}

/-- The number of scalar regular coordinates is the sum of the three block
entry counts. -/
@[simp]
theorem card [Fintype ι] [Fintype μ] [Fintype ν] :
    Fintype.card (AoyagiRegularBlockCoordinateIndex ι μ ν) =
      Fintype.card ι * Fintype.card ι +
        Fintype.card ι * Fintype.card ν +
          Fintype.card μ * Fintype.card ι := by
  simp [AoyagiRegularBlockCoordinateIndex, add_assoc]

/-- The scalar value attached to a regular block coordinate. -/
def value
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R) :
    AoyagiRegularBlockCoordinateIndex ι μ ν → R
  | Sum.inl ij => X ij.1 ij.2
  | Sum.inr (Sum.inl ij) => F2 ij.1 ij.2
  | Sum.inr (Sum.inr ij) => F3 ij.1 ij.2

@[simp]
theorem value_ctop
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (i j : ι) :
    value X F2 F3
        (Sum.inl (β := (ι × ν) ⊕ (μ × ι)) (i, j)) = X i j :=
  rfl

@[simp]
theorem value_f2
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (i : ι) (j : ν) :
    value X F2 F3
        (Sum.inr (α := ι × ι) (Sum.inl (β := μ × ι) (i, j))) = F2 i j :=
  rfl

@[simp]
theorem value_f3
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (i : μ) (j : ι) :
    value X F2 F3
        (Sum.inr (α := ι × ι) (Sum.inr (α := ι × ν) (i, j))) = F3 i j :=
  rfl

/-- The ideal generated by the scalar regular coordinates. -/
def entryIdeal [CommRing R]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R) :
    Ideal R :=
  Ideal.span (Set.range (value X F2 F3))

/-- The scalar regular-coordinate ideal is exactly the regular block-entry
ideal. -/
theorem entryIdeal_eq_regularBlockEntryIdeal [CommRing R]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R) :
    entryIdeal X F2 F3 = regularBlockEntryIdeal X F2 F3 := by
  refine le_antisymm ?_ ?_
  · rw [entryIdeal, Ideal.span_le]
    rintro _ ⟨c, rfl⟩
    cases c with
    | inl ij =>
        rcases ij with ⟨i, j⟩
        exact
          ((show matrixEntryIdeal X ≤ regularBlockEntryIdeal X F2 F3 from
            le_sup_left.trans le_sup_left) (matrixEntry_mem X i j))
    | inr rest =>
        cases rest with
        | inl ij =>
            rcases ij with ⟨i, j⟩
            exact
              ((show matrixEntryIdeal F2 ≤ regularBlockEntryIdeal X F2 F3 from
                le_sup_right.trans le_sup_left) (matrixEntry_mem F2 i j))
        | inr ij =>
            rcases ij with ⟨i, j⟩
            exact
              ((show matrixEntryIdeal F3 ≤ regularBlockEntryIdeal X F2 F3 from
                le_sup_right) (matrixEntry_mem F3 i j))
  · unfold regularBlockEntryIdeal
    refine sup_le ?_ ?_
    · refine sup_le ?_ ?_
      · rw [matrixEntryIdeal, Ideal.span_le]
        rintro _ ⟨⟨i, j⟩, rfl⟩
        exact
          Ideal.subset_span
            ⟨Sum.inl (β := (ι × ν) ⊕ (μ × ι)) (i, j), rfl⟩
      · rw [matrixEntryIdeal, Ideal.span_le]
        rintro _ ⟨⟨i, j⟩, rfl⟩
        exact
          Ideal.subset_span
            ⟨Sum.inr (α := ι × ι) (Sum.inl (β := μ × ι) (i, j)), rfl⟩
    · rw [matrixEntryIdeal, Ideal.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact
        Ideal.subset_span
          ⟨Sum.inr (α := ι × ι) (Sum.inr (α := ι × ν) (i, j)), rfl⟩

/-- A blockwise centered-continuity package projects to every scalar regular
coordinate. -/
theorem value_centered_continuousAt
    [Zero R] [TopologicalSpace α] [TopologicalSpace R]
    {x₀ : α}
    (X : α → Matrix ι ι R)
    (F2 : α → Matrix ι ν R)
    (F3 : α → Matrix μ ι R)
    (hX0 : X x₀ = 0) (hF20 : F2 x₀ = 0) (hF30 : F3 x₀ = 0)
    (hX : ContinuousAt X x₀)
    (hF2 : ContinuousAt F2 x₀)
    (hF3 : ContinuousAt F3 x₀) :
    ∀ c : AoyagiRegularBlockCoordinateIndex ι μ ν,
      value (X x₀) (F2 x₀) (F3 x₀) c = 0 ∧
        ContinuousAt
          (fun x : α => value (X x) (F2 x) (F3 x) c) x₀ := by
  intro c
  cases c with
  | inl ij =>
      rcases ij with ⟨i, j⟩
      constructor
      · simp [value, hX0]
      · exact
          ((continuous_apply j).continuousAt.comp
            ((continuous_apply i).continuousAt.comp hX))
  | inr rest =>
      cases rest with
      | inl ij =>
          rcases ij with ⟨i, j⟩
          constructor
          · simp [value, hF20]
          · exact
              ((continuous_apply j).continuousAt.comp
                ((continuous_apply i).continuousAt.comp hF2))
      | inr ij =>
          rcases ij with ⟨i, j⟩
          constructor
          · simp [value, hF30]
          · exact
              ((continuous_apply j).continuousAt.comp
                ((continuous_apply i).continuousAt.comp hF3))

/-- The regular-coordinate square-sum splits into the three displayed p. 13
regular block square-sums. -/
theorem coordinateSquareSum_eq_ctop_add_f2_add_f3
    [CommSemiring R] [Fintype ι] [Fintype μ] [Fintype ν]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R) :
    aoyagiCoordinateSquareSum (value X F2 F3) =
      aoyagiCoordinateSquareSum (fun ij : ι × ι => X ij.1 ij.2) +
        (aoyagiCoordinateSquareSum (fun ij : ι × ν => F2 ij.1 ij.2) +
          aoyagiCoordinateSquareSum (fun ij : μ × ι => F3 ij.1 ij.2)) := by
  simp [aoyagiCoordinateSquareSum, value, Fintype.sum_sum_type]

/-- The `F2` square-sum is bounded by the full regular-coordinate square-sum. -/
theorem f2SquareSum_le_regularSquareSum
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] [Fintype μ] [Fintype ν]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R) :
    aoyagiCoordinateSquareSum (fun ij : ι × ν => F2 ij.1 ij.2) ≤
      aoyagiCoordinateSquareSum (value X F2 F3) := by
  let SX := aoyagiCoordinateSquareSum (fun ij : ι × ι => X ij.1 ij.2)
  let SF2 := aoyagiCoordinateSquareSum (fun ij : ι × ν => F2 ij.1 ij.2)
  let SF3 := aoyagiCoordinateSquareSum (fun ij : μ × ι => F3 ij.1 ij.2)
  have hsplit : aoyagiCoordinateSquareSum (value X F2 F3) = SX + (SF2 + SF3) := by
    simpa [SX, SF2, SF3] using coordinateSquareSum_eq_ctop_add_f2_add_f3 X F2 F3
  have hSX : 0 ≤ SX := by
    exact aoyagiCoordinateSquareSum_nonneg (fun ij : ι × ι => X ij.1 ij.2)
  have hSF3 : 0 ≤ SF3 := by
    exact aoyagiCoordinateSquareSum_nonneg (fun ij : μ × ι => F3 ij.1 ij.2)
  rw [hsplit]
  nlinarith

/-- The `F3` square-sum is bounded by the full regular-coordinate square-sum. -/
theorem f3SquareSum_le_regularSquareSum
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] [Fintype μ] [Fintype ν]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R) :
    aoyagiCoordinateSquareSum (fun ij : μ × ι => F3 ij.1 ij.2) ≤
      aoyagiCoordinateSquareSum (value X F2 F3) := by
  let SX := aoyagiCoordinateSquareSum (fun ij : ι × ι => X ij.1 ij.2)
  let SF2 := aoyagiCoordinateSquareSum (fun ij : ι × ν => F2 ij.1 ij.2)
  let SF3 := aoyagiCoordinateSquareSum (fun ij : μ × ι => F3 ij.1 ij.2)
  have hsplit : aoyagiCoordinateSquareSum (value X F2 F3) = SX + (SF2 + SF3) := by
    simpa [SX, SF2, SF3] using coordinateSquareSum_eq_ctop_add_f2_add_f3 X F2 F3
  have hSX : 0 ≤ SX := by
    exact aoyagiCoordinateSquareSum_nonneg (fun ij : ι × ι => X ij.1 ij.2)
  have hSF2 : 0 ≤ SF2 := by
    exact aoyagiCoordinateSquareSum_nonneg (fun ij : ι × ν => F2 ij.1 ij.2)
  rw [hsplit]
  nlinarith

/-- Centered continuity of all scalar regular coordinates gives a neighborhood
where the `F2` and `F3` square-sums have total at most `1`. -/
theorem f2_f3_squareSum_eventually_le_one_of_forall_centered_continuousAt
    [Fintype ι] [Fintype μ] [Fintype ν] [TopologicalSpace α]
    {coord : α → AoyagiRegularBlockCoordinateIndex ι μ ν → ℝ} {x₀ : α}
    (hcoord :
      ∀ c : AoyagiRegularBlockCoordinateIndex ι μ ν,
        coord x₀ c = 0 ∧ ContinuousAt (fun x : α => coord x c) x₀) :
    ∀ᶠ x in nhds x₀,
      aoyagiCoordinateSquareSum
          (fun ij : ι × ν =>
            coord x (Sum.inr (α := ι × ι) (Sum.inl (β := μ × ι) ij))) +
        aoyagiCoordinateSquareSum
          (fun ij : μ × ι =>
            coord x (Sum.inr (α := ι × ι) (Sum.inr (α := ι × ν) ij))) ≤
          1 := by
  exact
    aoyagiCoordinateSquareSum_add_eventually_le_one_of_forall_centered_continuousAt
      (fun ij : ι × ν =>
        hcoord (Sum.inr (α := ι × ι) (Sum.inl (β := μ × ι) ij)))
      (fun ij : μ × ι =>
        hcoord (Sum.inr (α := ι × ι) (Sum.inr (α := ι × ν) ij)))

/-- The abstract scalar regular-coordinate count matches Aoyagi's p. 13 count
once the three index-cardinalities are identified with `r`, `H(L+1)-r`, and
`H(1)-r`.

This is only finite cardinal arithmetic.  The endpoint cardinality
identifications are separate source/geometric obligations. -/
theorem card_eq_aoyagiTheorem2RegularVariableCount
    [Fintype ι] [Fintype μ] [Fintype ν]
    {L : ℕ} {H : ℕ → ℕ} {r : ℕ}
    (hι : Fintype.card ι = r)
    (hμ : Fintype.card μ = H 1 - r)
    (hν : Fintype.card ν = H (L + 1) - r) :
    Fintype.card (AoyagiRegularBlockCoordinateIndex ι μ ν) =
      aoyagiTheorem2RegularVariableCount L H r := by
  rw [card, hι, hμ, hν]
  simp [aoyagiTheorem2RegularVariableCount, add_assoc]

end AoyagiRegularBlockCoordinateIndex

/-- Scalar coordinates for the residual `D` block in Aoyagi's p. 13
product-difference split. -/
abbrev AoyagiResidualBlockCoordinateIndex (μ : Type uμ) (ν : Type uν) :
    Type (max uμ uν) :=
  μ × ν

namespace AoyagiResidualBlockCoordinateIndex

variable {μ ν R α : Type*}

/-- The number of scalar residual coordinates is the entry count of the
residual block. -/
@[simp]
theorem card [Fintype μ] [Fintype ν] :
    Fintype.card (AoyagiResidualBlockCoordinateIndex μ ν) =
      Fintype.card μ * Fintype.card ν := by
  simp [AoyagiResidualBlockCoordinateIndex]

/-- The scalar value attached to a residual block coordinate. -/
def value (D : Matrix μ ν R) :
    AoyagiResidualBlockCoordinateIndex μ ν → R
  | ij => D ij.1 ij.2

@[simp]
theorem value_apply (D : Matrix μ ν R) (i : μ) (j : ν) :
    value D (i, j) = D i j :=
  rfl

/-- The ideal generated by the scalar residual coordinates. -/
def entryIdeal [CommRing R] (D : Matrix μ ν R) : Ideal R :=
  Ideal.span (Set.range (value D))

/-- The scalar residual-coordinate ideal is exactly the residual matrix-entry
ideal. -/
theorem entryIdeal_eq_matrixEntryIdeal [CommRing R] (D : Matrix μ ν R) :
    entryIdeal D = matrixEntryIdeal D := by
  refine le_antisymm ?_ ?_
  · rw [entryIdeal, Ideal.span_le]
    rintro _ ⟨c, rfl⟩
    rcases c with ⟨i, j⟩
    exact matrixEntry_mem D i j
  · rw [matrixEntryIdeal, Ideal.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact Ideal.subset_span ⟨(i, j), rfl⟩

/-- A centered-continuous residual block projects to every scalar residual
coordinate. -/
theorem value_centered_continuousAt
    [Zero R] [TopologicalSpace α] [TopologicalSpace R]
    {x₀ : α}
    (D : α → Matrix μ ν R)
    (hD0 : D x₀ = 0)
    (hD : ContinuousAt D x₀) :
    ∀ c : AoyagiResidualBlockCoordinateIndex μ ν,
      value (D x₀) c = 0 ∧
        ContinuousAt (fun x : α => value (D x) c) x₀ := by
  intro c
  rcases c with ⟨i, j⟩
  constructor
  · simp [value, hD0]
  · exact
      ((continuous_apply j).continuousAt.comp
        ((continuous_apply i).continuousAt.comp hD))

/-- The endpoint residual block entry count is the product of the two endpoint
residual dimensions. -/
theorem card_eq_endpointResidualEntryCount
    [Fintype μ] [Fintype ν]
    {L : ℕ} {H : ℕ → ℕ} {r : ℕ}
    (hμ : Fintype.card μ = H 1 - r)
    (hν : Fintype.card ν = H (L + 1) - r) :
    Fintype.card (AoyagiResidualBlockCoordinateIndex μ ν) =
      (H 1 - r) * (H (L + 1) - r) := by
  rw [card, hμ, hν]

end AoyagiResidualBlockCoordinateIndex

/-- Scalar coordinates for the cleaned p. 13 product-difference ideal family:
the three regular blocks together with the residual `D` block. -/
abbrev AoyagiProductDifferenceCoordinateIndex
    (ι : Type uι) (μ : Type uμ) (ν : Type uν) :
    Type (max uι uμ uν) :=
  AoyagiRegularBlockCoordinateIndex ι μ ν ⊕
    AoyagiResidualBlockCoordinateIndex μ ν

namespace AoyagiProductDifferenceCoordinateIndex

variable {ι μ ν R α : Type*}

@[simp]
theorem card [Fintype ι] [Fintype μ] [Fintype ν] :
    Fintype.card (AoyagiProductDifferenceCoordinateIndex ι μ ν) =
      Fintype.card ι * Fintype.card ι +
        Fintype.card ι * Fintype.card ν +
          Fintype.card μ * Fintype.card ι +
            Fintype.card μ * Fintype.card ν := by
  simp [AoyagiProductDifferenceCoordinateIndex, AoyagiRegularBlockCoordinateIndex,
    AoyagiResidualBlockCoordinateIndex, add_assoc]

/-- The scalar value attached to a full product-difference coordinate. -/
def value
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R) :
    AoyagiProductDifferenceCoordinateIndex ι μ ν → R
  | Sum.inl c => AoyagiRegularBlockCoordinateIndex.value X F2 F3 c
  | Sum.inr c => AoyagiResidualBlockCoordinateIndex.value D c

/-- The scalar value attached to the literal signed/corrected p. 13
product-difference block
`fromBlocks X (-F2) (-F3) (D - F3 * F2)`. -/
def literalValue [CommRing R] [Fintype ι]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R) :
    AoyagiProductDifferenceCoordinateIndex ι μ ν → R
  | Sum.inl c => AoyagiRegularBlockCoordinateIndex.value X (-F2) (-F3) c
  | Sum.inr c => AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2) c

@[simp]
theorem value_regular
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R)
    (c : AoyagiRegularBlockCoordinateIndex ι μ ν) :
    value X F2 F3 D (Sum.inl c) =
      AoyagiRegularBlockCoordinateIndex.value X F2 F3 c :=
  rfl

@[simp]
theorem value_residual
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R)
    (c : AoyagiResidualBlockCoordinateIndex μ ν) :
    value X F2 F3 D (Sum.inr c) =
      AoyagiResidualBlockCoordinateIndex.value D c :=
  rfl

@[simp]
theorem literalValue_regular [CommRing R] [Fintype ι]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R)
    (c : AoyagiRegularBlockCoordinateIndex ι μ ν) :
    literalValue X F2 F3 D (Sum.inl c) =
      AoyagiRegularBlockCoordinateIndex.value X (-F2) (-F3) c :=
  rfl

@[simp]
theorem literalValue_residual [CommRing R] [Fintype ι]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R)
    (c : AoyagiResidualBlockCoordinateIndex μ ν) :
    literalValue X F2 F3 D (Sum.inr c) =
      AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2) c :=
  rfl

/-- The ideal generated by the scalar product-difference coordinates. -/
def entryIdeal [CommRing R]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R) : Ideal R :=
  Ideal.span (Set.range (value X F2 F3 D))

/-- The scalar product-difference coordinate ideal is exactly the four-block
entry ideal from Aoyagi's p. 13 product-difference split. -/
theorem entryIdeal_eq_fourMatrixEntryIdeal [CommRing R]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R) :
    entryIdeal X F2 F3 D = fourMatrixEntryIdeal X F2 F3 D := by
  refine le_antisymm ?_ ?_
  · rw [entryIdeal, Ideal.span_le]
    rintro _ ⟨c, rfl⟩
    cases c with
    | inl c =>
        have hreg :
            AoyagiRegularBlockCoordinateIndex.value X F2 F3 c ∈
              regularBlockEntryIdeal X F2 F3 := by
          rw [← AoyagiRegularBlockCoordinateIndex.entryIdeal_eq_regularBlockEntryIdeal]
          exact Ideal.subset_span ⟨c, rfl⟩
        exact
          (show regularBlockEntryIdeal X F2 F3 ≤ fourMatrixEntryIdeal X F2 F3 D from
            le_sup_left) hreg
    | inr c =>
        have hres :
            AoyagiResidualBlockCoordinateIndex.value D c ∈ matrixEntryIdeal D := by
          rw [← AoyagiResidualBlockCoordinateIndex.entryIdeal_eq_matrixEntryIdeal]
          exact Ideal.subset_span ⟨c, rfl⟩
        exact
          (show matrixEntryIdeal D ≤ fourMatrixEntryIdeal X F2 F3 D from
            le_sup_right) hres
  · unfold fourMatrixEntryIdeal
    refine sup_le ?_ ?_
    · rw [← AoyagiRegularBlockCoordinateIndex.entryIdeal_eq_regularBlockEntryIdeal]
      rw [AoyagiRegularBlockCoordinateIndex.entryIdeal, entryIdeal, Ideal.span_le]
      rintro _ ⟨c, rfl⟩
      exact Ideal.subset_span ⟨Sum.inl c, rfl⟩
    · rw [← AoyagiResidualBlockCoordinateIndex.entryIdeal_eq_matrixEntryIdeal]
      rw [AoyagiResidualBlockCoordinateIndex.entryIdeal, entryIdeal, Ideal.span_le]
      rintro _ ⟨c, rfl⟩
      exact Ideal.subset_span ⟨Sum.inr c, rfl⟩

/-- The literal signed p. 13 product-difference block generates the scalar
product-difference coordinate ideal. -/
theorem matrixEntryIdeal_fromBlocks_neg_neg_sub_mul_eq_entryIdeal [CommRing R]
    [Fintype ι]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R) :
    matrixEntryIdeal (fromBlocks X (-F2) (-F3) (D - F3 * F2)) =
      entryIdeal X F2 F3 D := by
  calc
    matrixEntryIdeal (fromBlocks X (-F2) (-F3) (D - F3 * F2)) =
        fourMatrixEntryIdeal X F2 F3 D :=
      matrixEntryIdeal_fromBlocks_neg_neg_sub_mul_eq_fourMatrixEntryIdeal
        X F2 F3 D
    _ = entryIdeal X F2 F3 D :=
      (entryIdeal_eq_fourMatrixEntryIdeal X F2 F3 D).symm

/-- Centered continuity of the regular and residual blocks combines into
centered continuity for every product-difference scalar coordinate. -/
theorem value_centered_continuousAt
    [Zero R] [TopologicalSpace α] [TopologicalSpace R]
    {x₀ : α}
    (X : α → Matrix ι ι R)
    (F2 : α → Matrix ι ν R)
    (F3 : α → Matrix μ ι R)
    (D : α → Matrix μ ν R)
    (hX0 : X x₀ = 0) (hF20 : F2 x₀ = 0) (hF30 : F3 x₀ = 0)
    (hD0 : D x₀ = 0)
    (hX : ContinuousAt X x₀)
    (hF2 : ContinuousAt F2 x₀)
    (hF3 : ContinuousAt F3 x₀)
    (hD : ContinuousAt D x₀) :
    ∀ c : AoyagiProductDifferenceCoordinateIndex ι μ ν,
      value (X x₀) (F2 x₀) (F3 x₀) (D x₀) c = 0 ∧
        ContinuousAt
          (fun x : α => value (X x) (F2 x) (F3 x) (D x) c) x₀ := by
  intro c
  cases c with
  | inl c =>
      exact
        AoyagiRegularBlockCoordinateIndex.value_centered_continuousAt
          X F2 F3 hX0 hF20 hF30 hX hF2 hF3 c
  | inr c =>
      exact
        AoyagiResidualBlockCoordinateIndex.value_centered_continuousAt
          D hD0 hD c

/-- The cleaned product-difference coordinate square-sum splits into the
regular-coordinate square-sum plus the residual-coordinate square-sum. -/
theorem coordinateSquareSum_eq_regular_add_residual
    [CommSemiring R] [Fintype ι] [Fintype μ] [Fintype ν]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R) :
    aoyagiCoordinateSquareSum (value X F2 F3 D) =
      aoyagiCoordinateSquareSum (AoyagiRegularBlockCoordinateIndex.value X F2 F3) +
        aoyagiCoordinateSquareSum (AoyagiResidualBlockCoordinateIndex.value D) := by
  simp [aoyagiCoordinateSquareSum, value, Fintype.sum_sum_type]

/-- The literal signed/corrected p. 13 product-difference square-sum splits
as the regular block square-sum plus the corrected residual square-sum.

This only expands the finite scalar family
`X, -F2, -F3, D - F3 * F2`; it does not compare this loss with the cleaned
family `X, F2, F3, D`. -/
theorem literalCoordinateSquareSum_eq_regular_add_correctedResidual
    [CommRing R] [Fintype ι] [Fintype μ] [Fintype ν]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R) :
    aoyagiCoordinateSquareSum (literalValue X F2 F3 D) =
      aoyagiCoordinateSquareSum (AoyagiRegularBlockCoordinateIndex.value X F2 F3) +
        aoyagiCoordinateSquareSum
          (AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2)) := by
  simp [aoyagiCoordinateSquareSum, literalValue, AoyagiRegularBlockCoordinateIndex.value,
    AoyagiResidualBlockCoordinateIndex.value, Fintype.sum_sum_type]

/-- The corrected residual square-sum is bounded by twice the cleaned residual
square-sum plus twice the product-correction square-sum.

This is a finite ordered-ring estimate only. -/
theorem correctedResidualSquareSum_le_two_mul_residual_add_two_mul_product
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] [Fintype μ] [Fintype ν]
    (F2 : Matrix ι ν R) (F3 : Matrix μ ι R) (D : Matrix μ ν R) :
    aoyagiCoordinateSquareSum
        (AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2)) ≤
      2 * aoyagiCoordinateSquareSum (AoyagiResidualBlockCoordinateIndex.value D) +
        2 * aoyagiCoordinateSquareSum
          (AoyagiResidualBlockCoordinateIndex.value (F3 * F2)) := by
  simpa [AoyagiResidualBlockCoordinateIndex.value] using
    (aoyagiCoordinateSquareSum_sub_le_two_mul_add_two_mul
      (AoyagiResidualBlockCoordinateIndex.value D)
      (AoyagiResidualBlockCoordinateIndex.value (F3 * F2)))

/-- The cleaned residual square-sum is bounded by twice the corrected residual
square-sum plus twice the product-correction square-sum.

This is the reverse finite estimate needed for two-sided comparison. -/
theorem residualSquareSum_le_two_mul_correctedResidual_add_two_mul_product
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] [Fintype μ] [Fintype ν]
    (F2 : Matrix ι ν R) (F3 : Matrix μ ι R) (D : Matrix μ ν R) :
    aoyagiCoordinateSquareSum (AoyagiResidualBlockCoordinateIndex.value D) ≤
      2 * aoyagiCoordinateSquareSum
          (AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2)) +
        2 * aoyagiCoordinateSquareSum
          (AoyagiResidualBlockCoordinateIndex.value (F3 * F2)) := by
  simpa [AoyagiResidualBlockCoordinateIndex.value] using
    (aoyagiCoordinateSquareSum_add_le_two_mul_add_two_mul
      (AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2))
      (AoyagiResidualBlockCoordinateIndex.value (F3 * F2)))

/-- Frobenius-style finite matrix-product estimate for the p. 13 product
correction. -/
theorem productCorrectionSquareSum_le_f3SquareSum_mul_f2SquareSum
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] [Fintype μ] [Fintype ν]
    (F2 : Matrix ι ν R) (F3 : Matrix μ ι R) :
    aoyagiCoordinateSquareSum
        (AoyagiResidualBlockCoordinateIndex.value (F3 * F2)) ≤
      aoyagiCoordinateSquareSum (fun ij : μ × ι => F3 ij.1 ij.2) *
        aoyagiCoordinateSquareSum (fun ij : ι × ν => F2 ij.1 ij.2) := by
  classical
  unfold aoyagiCoordinateSquareSum AoyagiResidualBlockCoordinateIndex.value
  calc
    ∑ ij : μ × ν, (F3 * F2) ij.1 ij.2 ^ 2 ≤
        ∑ ij : μ × ν,
          (∑ k : ι, F3 ij.1 k ^ 2) * ∑ k : ι, F2 k ij.2 ^ 2 := by
      exact Finset.sum_le_sum (fun ij _ => by
        simpa [Matrix.mul_apply] using
          (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
            (fun k => F3 ij.1 k) (fun k => F2 k ij.2)))
    _ =
        (∑ ij : μ × ι, F3 ij.1 ij.2 ^ 2) *
          ∑ ij : ι × ν, F2 ij.1 ij.2 ^ 2 := by
      simp only [Fintype.sum_prod_type]
      calc
        ∑ i : μ, ∑ j : ν,
            (∑ k : ι, F3 i k ^ 2) * ∑ k : ι, F2 k j ^ 2 =
            ∑ i : μ, (∑ k : ι, F3 i k ^ 2) *
              ∑ j : ν, ∑ k : ι, F2 k j ^ 2 := by
          simp [Finset.mul_sum]
        _ =
            (∑ i : μ, ∑ k : ι, F3 i k ^ 2) *
              ∑ j : ν, ∑ k : ι, F2 k j ^ 2 := by
          rw [Finset.sum_mul]
        _ =
            (∑ i : μ, ∑ k : ι, F3 i k ^ 2) *
              ∑ k : ι, ∑ j : ν, F2 k j ^ 2 := by
          have hcomm :
              (∑ j : ν, ∑ k : ι, F2 k j ^ 2) =
                ∑ k : ι, ∑ j : ν, F2 k j ^ 2 := by
            rw [Finset.sum_comm]
          rw [hcomm]

/-- If the `F2` and `F3` square-sums are small, then the product correction is
controlled by one quarter of the regular-coordinate square-sum. -/
theorem four_mul_productCorrectionSquareSum_le_regular_of_f2_f3_squareSum_add_le_one
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] [Fintype μ] [Fintype ν]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (hsmall :
      aoyagiCoordinateSquareSum (fun ij : ι × ν => F2 ij.1 ij.2) +
          aoyagiCoordinateSquareSum (fun ij : μ × ι => F3 ij.1 ij.2) ≤
        1) :
    4 * aoyagiCoordinateSquareSum
        (AoyagiResidualBlockCoordinateIndex.value (F3 * F2)) ≤
      aoyagiCoordinateSquareSum
        (AoyagiRegularBlockCoordinateIndex.value X F2 F3) := by
  let A :=
    aoyagiCoordinateSquareSum
      (AoyagiRegularBlockCoordinateIndex.value X F2 F3)
  let SF2 := aoyagiCoordinateSquareSum (fun ij : ι × ν => F2 ij.1 ij.2)
  let SF3 := aoyagiCoordinateSquareSum (fun ij : μ × ι => F3 ij.1 ij.2)
  let P :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value (F3 * F2))
  have hP : P ≤ SF3 * SF2 := by
    simpa [P, SF2, SF3] using
      productCorrectionSquareSum_le_f3SquareSum_mul_f2SquareSum F2 F3
  have hSF20 : 0 ≤ SF2 := by
    exact aoyagiCoordinateSquareSum_nonneg (fun ij : ι × ν => F2 ij.1 ij.2)
  have hSF30 : 0 ≤ SF3 := by
    exact aoyagiCoordinateSquareSum_nonneg (fun ij : μ × ι => F3 ij.1 ij.2)
  have hsum_small : SF2 + SF3 ≤ 1 := by
    simpa [SF2, SF3] using hsmall
  have hfour_prod : 4 * (SF3 * SF2) ≤ SF2 + SF3 := by
    have hfour_le_sq : 4 * SF3 * SF2 ≤ (SF2 + SF3) ^ 2 := by
      nlinarith [sq_nonneg (SF2 - SF3)]
    have hsumsq_le : (SF2 + SF3) ^ 2 ≤ SF2 + SF3 := by
      nlinarith
    nlinarith
  have hsum_le_A : SF2 + SF3 ≤ A := by
    let SX := aoyagiCoordinateSquareSum (fun ij : ι × ι => X ij.1 ij.2)
    have hsplit : A = SX + (SF2 + SF3) := by
      simpa [A, SX, SF2, SF3] using
        AoyagiRegularBlockCoordinateIndex.coordinateSquareSum_eq_ctop_add_f2_add_f3 X F2 F3
    have hSX : 0 ≤ SX := by
      exact aoyagiCoordinateSquareSum_nonneg (fun ij : ι × ι => X ij.1 ij.2)
    rw [hsplit]
    nlinarith
  nlinarith

/-- Conditional finite comparison: if the product correction `F3 * F2` is
controlled by the regular square-sum, then the literal p. 13 square-sum is at
most three times the cleaned square-sum.

This theorem does not prove the required local small-neighborhood control of
`F3 * F2`; it only records the finite algebra once that control is supplied. -/
theorem literalCoordinateSquareSum_le_three_mul_coordinateSquareSum_of_product_le_regular
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] [Fintype μ] [Fintype ν]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R)
    (hproduct :
      aoyagiCoordinateSquareSum
          (AoyagiResidualBlockCoordinateIndex.value (F3 * F2)) ≤
        aoyagiCoordinateSquareSum
          (AoyagiRegularBlockCoordinateIndex.value X F2 F3)) :
    aoyagiCoordinateSquareSum (literalValue X F2 F3 D) ≤
      3 * aoyagiCoordinateSquareSum (value X F2 F3 D) := by
  let A :=
    aoyagiCoordinateSquareSum
      (AoyagiRegularBlockCoordinateIndex.value X F2 F3)
  let B :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value D)
  let P :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value (F3 * F2))
  let E :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2))
  have hE : E ≤ 2 * B + 2 * P := by
    simpa [E, B, P] using
      correctedResidualSquareSum_le_two_mul_residual_add_two_mul_product F2 F3 D
  have hP : P ≤ A := by
    simpa [A, P] using hproduct
  have hB0 : 0 ≤ B := by
    exact aoyagiCoordinateSquareSum_nonneg
      (AoyagiResidualBlockCoordinateIndex.value D)
  calc
    aoyagiCoordinateSquareSum (literalValue X F2 F3 D) = A + E := by
      simpa [A, E] using
        literalCoordinateSquareSum_eq_regular_add_correctedResidual X F2 F3 D
    _ ≤ A + (2 * B + 2 * P) := by
      linarith
    _ ≤ A + (2 * B + 2 * A) := by
      linarith
    _ ≤ 3 * (A + B) := by
      nlinarith
    _ = 3 * aoyagiCoordinateSquareSum (value X F2 F3 D) := by
      rw [coordinateSquareSum_eq_regular_add_residual X F2 F3 D]

/-- Conditional finite comparison in the reverse direction: under the same
product-control hypothesis, the cleaned square-sum is at most three times the
literal p. 13 square-sum. -/
theorem coordinateSquareSum_le_three_mul_literalCoordinateSquareSum_of_product_le_regular
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] [Fintype μ] [Fintype ν]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R)
    (hproduct :
      aoyagiCoordinateSquareSum
          (AoyagiResidualBlockCoordinateIndex.value (F3 * F2)) ≤
        aoyagiCoordinateSquareSum
          (AoyagiRegularBlockCoordinateIndex.value X F2 F3)) :
    aoyagiCoordinateSquareSum (value X F2 F3 D) ≤
      3 * aoyagiCoordinateSquareSum (literalValue X F2 F3 D) := by
  let A :=
    aoyagiCoordinateSquareSum
      (AoyagiRegularBlockCoordinateIndex.value X F2 F3)
  let B :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value D)
  let P :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value (F3 * F2))
  let E :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2))
  have hB : B ≤ 2 * E + 2 * P := by
    simpa [B, E, P] using
      residualSquareSum_le_two_mul_correctedResidual_add_two_mul_product F2 F3 D
  have hP : P ≤ A := by
    simpa [A, P] using hproduct
  have hE0 : 0 ≤ E := by
    exact aoyagiCoordinateSquareSum_nonneg
      (AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2))
  calc
    aoyagiCoordinateSquareSum (value X F2 F3 D) = A + B := by
      simpa [A, B] using
        coordinateSquareSum_eq_regular_add_residual X F2 F3 D
    _ ≤ A + (2 * E + 2 * P) := by
      linarith
    _ ≤ A + (2 * E + 2 * A) := by
      linarith
    _ ≤ 3 * (A + E) := by
      nlinarith
    _ = 3 * aoyagiCoordinateSquareSum (literalValue X F2 F3 D) := by
      rw [literalCoordinateSquareSum_eq_regular_add_correctedResidual X F2 F3 D]

/-- Small-neighborhood finite comparison: if the sum of the `F2` and `F3`
regular square-sums is at most `1`, then the literal p. 13 square-sum is
bounded by twice the cleaned square-sum. -/
theorem literalCoordinateSquareSum_le_two_mul_coordinateSquareSum_of_f2_f3_squareSum_add_le_one
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] [Fintype μ] [Fintype ν]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R)
    (hsmall :
      aoyagiCoordinateSquareSum (fun ij : ι × ν => F2 ij.1 ij.2) +
          aoyagiCoordinateSquareSum (fun ij : μ × ι => F3 ij.1 ij.2) ≤
        1) :
    aoyagiCoordinateSquareSum (literalValue X F2 F3 D) ≤
      2 * aoyagiCoordinateSquareSum (value X F2 F3 D) := by
  let A :=
    aoyagiCoordinateSquareSum
      (AoyagiRegularBlockCoordinateIndex.value X F2 F3)
  let B :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value D)
  let P :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value (F3 * F2))
  let E :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2))
  have hE : E ≤ 2 * B + 2 * P := by
    simpa [E, B, P] using
      correctedResidualSquareSum_le_two_mul_residual_add_two_mul_product F2 F3 D
  have hP4 : 4 * P ≤ A := by
    simpa [P, A] using
      four_mul_productCorrectionSquareSum_le_regular_of_f2_f3_squareSum_add_le_one
        X F2 F3 hsmall
  have hP0 : 0 ≤ P := by
    exact aoyagiCoordinateSquareSum_nonneg
      (AoyagiResidualBlockCoordinateIndex.value (F3 * F2))
  have hA0 : 0 ≤ A := by
    exact aoyagiCoordinateSquareSum_nonneg
      (AoyagiRegularBlockCoordinateIndex.value X F2 F3)
  calc
    aoyagiCoordinateSquareSum (literalValue X F2 F3 D) = A + E := by
      simpa [A, E] using
        literalCoordinateSquareSum_eq_regular_add_correctedResidual X F2 F3 D
    _ ≤ A + (2 * B + 2 * P) := by
      linarith
    _ ≤ 2 * (A + B) := by
      nlinarith
    _ = 2 * aoyagiCoordinateSquareSum (value X F2 F3 D) := by
      rw [coordinateSquareSum_eq_regular_add_residual X F2 F3 D]

/-- Reverse small-neighborhood finite comparison: if the sum of the `F2` and
`F3` regular square-sums is at most `1`, then the cleaned square-sum is bounded
by twice the literal p. 13 square-sum. -/
theorem coordinateSquareSum_le_two_mul_literalCoordinateSquareSum_of_f2_f3_squareSum_add_le_one
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] [Fintype μ] [Fintype ν]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R)
    (hsmall :
      aoyagiCoordinateSquareSum (fun ij : ι × ν => F2 ij.1 ij.2) +
          aoyagiCoordinateSquareSum (fun ij : μ × ι => F3 ij.1 ij.2) ≤
        1) :
    aoyagiCoordinateSquareSum (value X F2 F3 D) ≤
      2 * aoyagiCoordinateSquareSum (literalValue X F2 F3 D) := by
  let A :=
    aoyagiCoordinateSquareSum
      (AoyagiRegularBlockCoordinateIndex.value X F2 F3)
  let B :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value D)
  let P :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value (F3 * F2))
  let E :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2))
  have hB : B ≤ 2 * E + 2 * P := by
    simpa [B, E, P] using
      residualSquareSum_le_two_mul_correctedResidual_add_two_mul_product F2 F3 D
  have hP4 : 4 * P ≤ A := by
    simpa [P, A] using
      four_mul_productCorrectionSquareSum_le_regular_of_f2_f3_squareSum_add_le_one
        X F2 F3 hsmall
  have hP0 : 0 ≤ P := by
    exact aoyagiCoordinateSquareSum_nonneg
      (AoyagiResidualBlockCoordinateIndex.value (F3 * F2))
  have hE0 : 0 ≤ E := by
    exact aoyagiCoordinateSquareSum_nonneg
      (AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2))
  calc
    aoyagiCoordinateSquareSum (value X F2 F3 D) = A + B := by
      simpa [A, B] using
        coordinateSquareSum_eq_regular_add_residual X F2 F3 D
    _ ≤ A + (2 * E + 2 * P) := by
      linarith
    _ ≤ 2 * (A + E) := by
      nlinarith
    _ = 2 * aoyagiCoordinateSquareSum (literalValue X F2 F3 D) := by
      rw [literalCoordinateSquareSum_eq_regular_add_correctedResidual X F2 F3 D]

/-- The cleaned p. 13 product-difference scalar-coordinate count is the
endpoint product entry count. -/
theorem card_eq_endpointProductEntryCount
    [Fintype ι] [Fintype μ] [Fintype ν]
    {L : ℕ} {H : ℕ → ℕ} {r : ℕ}
    (hι : Fintype.card ι = r)
    (hμ : Fintype.card μ = H 1 - r)
    (hν : Fintype.card ν = H (L + 1) - r)
    (hsource : r ≤ H 1) (htarget : r ≤ H (L + 1)) :
    Fintype.card (AoyagiProductDifferenceCoordinateIndex ι μ ν) =
      H 1 * H (L + 1) := by
  rw [card, hι, hμ, hν]
  have hsource_decomp : H 1 = r + (H 1 - r) := by omega
  have htarget_decomp : H (L + 1) = r + (H (L + 1) - r) := by omega
  calc
    r * r + r * (H (L + 1) - r) + (H 1 - r) * r +
        (H 1 - r) * (H (L + 1) - r) =
        (r + (H 1 - r)) * (r + (H (L + 1) - r)) := by
      ring
    _ = H 1 * H (L + 1) := by
      rw [← hsource_decomp, ← htarget_decomp]

end AoyagiProductDifferenceCoordinateIndex

section FixedBaseCanonicalCertificate

universe u v

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  {N : ℕ}
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)]
  [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, Module K (W i)]
  [∀ i, ContinuousSMul K (W i)]
  (B : ∀ i : Fin N, W i.succ →ₗ[K] W i.castSucc)

omit [CompleteSpace K] [∀ i, TopologicalSpace (W i)]
  [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- The endpoint-compatible complement at a reversed vertex has dimension
`dim vertex - rank`, where the rank is `finrank U₀`.

This is the finite-dimensional complement count behind the p. 13 endpoint
residual block sizes. -/
theorem paperEndpointEndpointComplementIndex_card_eq_layerSubRank
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (j : Fin (N + 1)) :
    Fintype.card
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ j) =
      Module.finrank K (reverseVertex W j) - Module.finrank K U₀ := by
  classical
  let hUrev :=
    isCompl_ker_reverse_total_of_isCompl_ker_paperChainMap W B U₀ hU₀
  have hcompl :
      IsCompl (throughSubspace (reverseVertex W) (reverseEdge W B) U₀ j)
        (throughSubspaceEndpointComplement
          (reverseVertex W) (reverseEdge W B) U₀ j) :=
    throughSubspace_isCompl_endpointComplement
      (reverseVertex W) (reverseEdge W B) U₀ hUrev j
  have hfactor :
      chainMap (reverseVertex W) (reverseEdge W B) 0 (Fin.last N)
          ((Fin.zero_le j).trans j.le_last) =
        (chainMap (reverseVertex W) (reverseEdge W B) j (Fin.last N) j.le_last).comp
          (chainMap (reverseVertex W) (reverseEdge W B) 0 j (Fin.zero_le j)) :=
    chainMap_zero_last_eq_suffix_comp_prefix (reverseVertex W) (reverseEdge W B) j
  have hdisj :
      Disjoint U₀
        (LinearMap.ker
          ((chainMap (reverseVertex W) (reverseEdge W B) j (Fin.last N) j.le_last).comp
            (chainMap (reverseVertex W) (reverseEdge W B) 0 j (Fin.zero_le j)))) := by
    simpa [← hfactor] using hUrev.disjoint
  have hthrough :
      Module.finrank K
          (throughSubspace (reverseVertex W) (reverseEdge W B) U₀ j) =
        Module.finrank K U₀ :=
    finrank_throughSubspace_eq_of_disjoint_ker_comp
      (reverseVertex W) (reverseEdge W B) U₀ j hdisj
  have hadd := Submodule.finrank_add_eq_of_isCompl hcompl
  have hcard :
      Fintype.card
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ j) =
        Module.finrank K
          (throughSubspaceEndpointComplement
            (reverseVertex W) (reverseEdge W B) U₀ j) := by
    simp [throughSubspaceEndpointComplementIndex]
  rw [hcard]
  omega

omit [CompleteSpace K] [∀ i, TopologicalSpace (W i)]
  [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- The endpoint-compatible scalar regular-coordinate index has exactly
Aoyagi's p. 13 regular-variable count, once the base product rank and layer
dimension convention are supplied. -/
theorem paperEndpointRegularBlockCoordinateIndex_card_eq_regularVariableCount
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    {H : ℕ → ℕ} {r : ℕ}
    (hprod : Module.finrank K (LinearMap.range (paperTotalMap W B)) = r)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    Fintype.card
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank K U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) =
      aoyagiTheorem2RegularVariableCount N H r := by
  classical
  have hU :
      Fintype.card (Fin (Module.finrank K U₀)) = r := by
    simp [(paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀).finrank_eq_range,
      hprod]
  have htarget :
      Fintype.card
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0) =
        H (N + 1) - r := by
    rw [paperEndpointEndpointComplementIndex_card_eq_layerSubRank W B U₀ hU₀ 0]
    have hvertex :
        Module.finrank K (reverseVertex W 0) = H (N + 1) := by
      simpa [reverseVertex] using (hH (Fin.last N)).symm
    have hUfin :
        Module.finrank K U₀ = r :=
      (paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀).finrank_eq_range.trans hprod
    rw [hvertex, hUfin]
  have hsource :
      Fintype.card
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) =
        H 1 - r := by
    rw [paperEndpointEndpointComplementIndex_card_eq_layerSubRank W B U₀ hU₀ (Fin.last N)]
    have hvertex :
        Module.finrank K (reverseVertex W (Fin.last N)) = H 1 := by
      have hrev : (Fin.last N).rev = (0 : Fin (N + 1)) := by
        simp
      change Module.finrank K (W ((Fin.last N).rev)) = H 1
      rw [hrev]
      exact (hH (0 : Fin (N + 1))).symm
    have hUfin :
        Module.finrank K U₀ = r :=
      (paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀).finrank_eq_range.trans hprod
    rw [hvertex, hUfin]
  exact
    AoyagiRegularBlockCoordinateIndex.card_eq_aoyagiTheorem2RegularVariableCount
      (ι := Fin (Module.finrank K U₀))
      (μ := throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (ν := throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
      (L := N) (H := H) (r := r) hU hsource htarget

omit [CompleteSpace K] [∀ i, TopologicalSpace (W i)]
  [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- The endpoint-compatible residual scalar-coordinate index has the product
of the row/left and column/right residual endpoint dimensions. -/
theorem paperEndpointResidualBlockCoordinateIndex_card_eq_endpointResidualEntryCount
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    {H : ℕ → ℕ} {r : ℕ}
    (hprod : Module.finrank K (LinearMap.range (paperTotalMap W B)) = r)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    Fintype.card
        (AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) =
      (H 1 - r) * (H (N + 1) - r) := by
  classical
  have htarget :
      Fintype.card
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0) =
        H (N + 1) - r := by
    rw [paperEndpointEndpointComplementIndex_card_eq_layerSubRank W B U₀ hU₀ 0]
    have hvertex :
        Module.finrank K (reverseVertex W 0) = H (N + 1) := by
      simpa [reverseVertex] using (hH (Fin.last N)).symm
    have hUfin :
        Module.finrank K U₀ = r :=
      (paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀).finrank_eq_range.trans hprod
    rw [hvertex, hUfin]
  have hsource :
      Fintype.card
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) =
        H 1 - r := by
    rw [paperEndpointEndpointComplementIndex_card_eq_layerSubRank W B U₀ hU₀ (Fin.last N)]
    have hvertex :
        Module.finrank K (reverseVertex W (Fin.last N)) = H 1 := by
      have hrev : (Fin.last N).rev = (0 : Fin (N + 1)) := by
        simp
      change Module.finrank K (W ((Fin.last N).rev)) = H 1
      rw [hrev]
      exact (hH (0 : Fin (N + 1))).symm
    have hUfin :
        Module.finrank K U₀ = r :=
      (paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀).finrank_eq_range.trans hprod
    rw [hvertex, hUfin]
  exact
    AoyagiResidualBlockCoordinateIndex.card_eq_endpointResidualEntryCount
      (μ := throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (ν := throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
      (L := N) (H := H) (r := r) hsource htarget

omit [CompleteSpace K] [∀ i, TopologicalSpace (W i)]
  [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- The endpoint-compatible full product-difference scalar-coordinate index
has exactly the number of entries in an `H 1` by `H(N+1)` endpoint product. -/
theorem paperEndpointProductDifferenceCoordinateIndex_card_eq_endpointProductEntryCount
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    {H : ℕ → ℕ} {r : ℕ}
    (hprod : Module.finrank K (LinearMap.range (paperTotalMap W B)) = r)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    Fintype.card
        (AoyagiProductDifferenceCoordinateIndex
          (Fin (Module.finrank K U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) =
      H 1 * H (N + 1) := by
  classical
  have hU :
      Fintype.card (Fin (Module.finrank K U₀)) = r := by
    simp [(paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀).finrank_eq_range,
      hprod]
  have htarget :
      Fintype.card
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0) =
        H (N + 1) - r := by
    rw [paperEndpointEndpointComplementIndex_card_eq_layerSubRank W B U₀ hU₀ 0]
    have hvertex :
        Module.finrank K (reverseVertex W 0) = H (N + 1) := by
      simpa [reverseVertex] using (hH (Fin.last N)).symm
    have hUfin :
        Module.finrank K U₀ = r :=
      (paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀).finrank_eq_range.trans hprod
    rw [hvertex, hUfin]
  have hsource :
      Fintype.card
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) =
        H 1 - r := by
    rw [paperEndpointEndpointComplementIndex_card_eq_layerSubRank W B U₀ hU₀ (Fin.last N)]
    have hvertex :
        Module.finrank K (reverseVertex W (Fin.last N)) = H 1 := by
      have hrev : (Fin.last N).rev = (0 : Fin (N + 1)) := by
        simp
      change Module.finrank K (W ((Fin.last N).rev)) = H 1
      rw [hrev]
      exact (hH (0 : Fin (N + 1))).symm
    have hUfin :
        Module.finrank K U₀ = r :=
      (paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀).finrank_eq_range.trans hprod
    rw [hvertex, hUfin]
  have hsource_le : r ≤ H 1 := by
    have hle :
        r ≤ Module.finrank K (W (0 : Fin (N + 1))) :=
      paperTotalMap_rank_le_layer_finrank W B hprod (0 : Fin (N + 1))
    simpa using hle.trans_eq (hH (0 : Fin (N + 1))).symm
  have htarget_le : r ≤ H (N + 1) := by
    have hle :
        r ≤ Module.finrank K (W (Fin.last N)) :=
      paperTotalMap_rank_le_layer_finrank W B hprod (Fin.last N)
    simpa using hle.trans_eq (hH (Fin.last N)).symm
  exact
    AoyagiProductDifferenceCoordinateIndex.card_eq_endpointProductEntryCount
      (ι := Fin (Module.finrank K U₀))
      (μ := throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (ν := throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
      (L := N) (H := H) (r := r) hU hsource htarget hsource_le htarget_le

namespace PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks

set_option linter.unusedSectionVars false in
/-- The canonical product-difference entry ideal splits as the scalar
regular-coordinate ideal joined with the residual `D`-block entry ideal. -/
theorem canonicalProductDifferenceEntryIdeal_eq_regularCoordinateIdeal_sup_matrixEntryIdeal
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {x : α}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks
        W B U₀ hU₀ Cedge r rEdge x) :
    let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
      fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
    let S := ChartLocalSuffixState.suffixState EMat
      (Fin.last N) 0 (Fin.zero_le (Fin.last N))
    matrixEntryIdeal
        (paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E -
          fromBlocks
            (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
            0
            (0 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (Fin (Module.finrank K U₀)) K)
            (0 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0) K)) =
        AoyagiRegularBlockCoordinateIndex.entryIdeal
          (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) ⊔
        matrixEntryIdeal S.D := by
  intro E EMat S
  calc
    matrixEntryIdeal
        (paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E -
          fromBlocks
            (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
            0
            (0 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (Fin (Module.finrank K U₀)) K)
            (0 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0) K)) =
        regularBlockEntryIdeal (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) ⊔
          matrixEntryIdeal S.D := by
      simpa [E, EMat, S] using
        cert.canonicalProductDifferenceEntryIdeal_eq_regularBlockEntryIdeal_sup_matrixEntryIdeal
    _ = AoyagiRegularBlockCoordinateIndex.entryIdeal
          (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) ⊔
        matrixEntryIdeal S.D := by
      rw [AoyagiRegularBlockCoordinateIndex.entryIdeal_eq_regularBlockEntryIdeal]

set_option linter.unusedSectionVars false in
/-- The canonical product-difference entry ideal is generated by the combined
p. 13 scalar product-difference coordinate family. -/
theorem canonicalProductDifferenceEntryIdeal_eq_productDifferenceCoordinateIdeal
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {x : α}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks
        W B U₀ hU₀ Cedge r rEdge x) :
    let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
      fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
    let S := ChartLocalSuffixState.suffixState EMat
      (Fin.last N) 0 (Fin.zero_le (Fin.last N))
    matrixEntryIdeal
        (paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E -
          fromBlocks
            (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
            0
            (0 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (Fin (Module.finrank K U₀)) K)
            (0 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0) K)) =
      AoyagiProductDifferenceCoordinateIndex.entryIdeal
        (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) S.D := by
  intro E EMat S
  calc
    matrixEntryIdeal
        (paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E -
          fromBlocks
            (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
            0
            (0 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (Fin (Module.finrank K U₀)) K)
            (0 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0) K)) =
        fourMatrixEntryIdeal (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) S.D := by
      simpa [E, EMat, S] using
        cert.canonicalProductDifferenceEntryIdeal
    _ = AoyagiProductDifferenceCoordinateIndex.entryIdeal
        (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) S.D := by
      rw [AoyagiProductDifferenceCoordinateIndex.entryIdeal_eq_fourMatrixEntryIdeal]

end PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks

set_option linter.unusedSectionVars false in
/-- A fixed-base source-side neighborhood where the canonical product-difference
entry ideal is split into scalar regular-coordinate entries and the residual
`D`-block entries. -/
def PaperEndpointFixedBaseRegularCoordinateIdealSourceNeighborhood
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ) : Prop :=
  ∃ U : Set α,
    U ∈ nhds x₀ ∧
    x₀ ∈ U ∧
    ∀ x, x ∈ U →
      x ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge →
        let E : ∀ p : Fin N,
            reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
          fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
        let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
        let S := ChartLocalSuffixState.suffixState EMat
          (Fin.last N) 0 (Fin.zero_le (Fin.last N))
        matrixEntryIdeal
            (paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E -
              fromBlocks
                (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                0
                (0 : Matrix
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (Fin (Module.finrank K U₀)) K)
                (0 : Matrix
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0) K)) =
          AoyagiRegularBlockCoordinateIndex.entryIdeal
              (S.Ctop - 1) (-(S.B)) (lowerLeftBlock S.L) ⊔
            matrixEntryIdeal S.D

set_option linter.unusedSectionVars false in
/-- A fixed-base source-side neighborhood where the canonical product-difference
entry ideal is generated by the combined p. 13 scalar coordinate family. -/
def PaperEndpointFixedBaseProductDifferenceCoordinateIdealSourceNeighborhood
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ) : Prop :=
  ∃ U : Set α,
    U ∈ nhds x₀ ∧
    x₀ ∈ U ∧
    ∀ x, x ∈ U →
      x ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge →
        let E : ∀ p : Fin N,
            reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
          fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
        let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
        let S := ChartLocalSuffixState.suffixState EMat
          (Fin.last N) 0 (Fin.zero_le (Fin.last N))
        matrixEntryIdeal
            (paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E -
              fromBlocks
                (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                0
                (0 : Matrix
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (Fin (Module.finrank K U₀)) K)
                (0 : Matrix
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0) K)) =
          AoyagiProductDifferenceCoordinateIndex.entryIdeal
            (S.Ctop - 1) (-(S.B)) (lowerLeftBlock S.L) S.D

namespace PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate

set_option linter.unusedSectionVars false in
/-- The local source certificate exposes an ordinary neighborhood where, on
the source-shaped rank stratum, the canonical product-difference entry ideal
splits as the scalar regular-coordinate ideal joined with the residual
`D`-block entry ideal. -/
theorem exists_regularCoordinateIdeal_source_neighborhood
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge) :
    PaperEndpointFixedBaseRegularCoordinateIdealSourceNeighborhood
      W B U₀ hU₀ x₀ Cedge r rEdge := by
  rcases cert.exists_source_neighborhood with ⟨U, hU, hx₀U, hsource⟩
  refine ⟨U, hU, hx₀U, ?_⟩
  intro x hxU hxsrc
  exact
    (hsource x hxU hxsrc)
      |>.canonicalProductDifferenceEntryIdeal_eq_regularCoordinateIdeal_sup_matrixEntryIdeal

/-- Alias for the named regular-coordinate/residual ideal source-neighborhood
predicate. -/
theorem regularCoordinateIdealSourceNeighborhood
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge) :
    PaperEndpointFixedBaseRegularCoordinateIdealSourceNeighborhood
      W B U₀ hU₀ x₀ Cedge r rEdge :=
  cert.exists_regularCoordinateIdeal_source_neighborhood

set_option linter.unusedSectionVars false in
/-- The local source certificate exposes an ordinary neighborhood where, on
the source-shaped rank stratum, the canonical product-difference entry ideal
is generated by the combined p. 13 scalar coordinate family. -/
theorem exists_productDifferenceCoordinateIdeal_source_neighborhood
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge) :
    PaperEndpointFixedBaseProductDifferenceCoordinateIdealSourceNeighborhood
      W B U₀ hU₀ x₀ Cedge r rEdge := by
  rcases cert.exists_source_neighborhood with ⟨U, hU, hx₀U, hsource⟩
  refine ⟨U, hU, hx₀U, ?_⟩
  intro x hxU hxsrc
  exact
    (hsource x hxU hxsrc)
      |>.canonicalProductDifferenceEntryIdeal_eq_productDifferenceCoordinateIdeal

/-- Alias for the named product-difference coordinate ideal source-neighborhood
predicate. -/
theorem productDifferenceCoordinateIdealSourceNeighborhood
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge) :
    PaperEndpointFixedBaseProductDifferenceCoordinateIdealSourceNeighborhood
      W B U₀ hU₀ x₀ Cedge r rEdge :=
  cert.exists_productDifferenceCoordinateIdeal_source_neighborhood

end PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate

namespace PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate

set_option linter.unusedSectionVars false in
/-- The canonical local certificate gives centered continuous scalar
coordinates for the three p. 13 regular blocks `Ctop - 1`, `-B`, and
`lowerLeftBlock L`.

The residual block `D` is intentionally not part of this regular-coordinate
index. -/
theorem regularBlockScalarCoordinates_centered_continuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge) :
    let E : α → ∀ p : Fin N,
        Matrix
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
      fun x p ↦
        LinearMap.toMatrix
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
          (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let S : α →
        ChartLocalSuffixState (Fin (Module.finrank K U₀))
          (fun j : Fin (N + 1) ↦
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
          K (Fin.last N) 0 :=
      fun x ↦ ChartLocalSuffixState.suffixState (E x) (Fin.last N) 0
        (Fin.zero_le (Fin.last N))
    ∀ c : AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0),
      AoyagiRegularBlockCoordinateIndex.value
          ((S x₀).Ctop - 1) (-(S x₀).B) (lowerLeftBlock (S x₀).L) c = 0 ∧
        ContinuousAt
          (fun x : α =>
            AoyagiRegularBlockCoordinateIndex.value
              ((S x).Ctop - 1) (-(S x).B) (lowerLeftBlock (S x).L) c) x₀ := by
  intro E S c
  rcases cert.coefficientFields_centered_continuous with
    ⟨hCtop0, hB0, hF30, _hD0, _hunit, hCtop, hB, hF3, _hD⟩
  exact
    AoyagiRegularBlockCoordinateIndex.value_centered_continuousAt
      (X := fun x : α ↦ (S x).Ctop - 1)
      (F2 := fun x : α ↦ -(S x).B)
      (F3 := fun x : α ↦ lowerLeftBlock (S x).L)
      hCtop0 hB0 hF30 hCtop hB hF3 c

omit [CompleteSpace K] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- The local source certificate carries enough basepoint rank data to identify
the scalar regular-coordinate index cardinality with Aoyagi's p. 13 regular
variable count. -/
theorem regularBlockCoordinateIndex_card_eq_regularVariableCount
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {H : ℕ → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    Fintype.card
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank K U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) =
      aoyagiTheorem2RegularVariableCount N H r :=
  paperEndpointRegularBlockCoordinateIndex_card_eq_regularVariableCount
    W B U₀ hU₀ cert.source_basepoint.1 hH

end PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate

namespace PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate

set_option linter.unusedSectionVars false in
/-- The canonical local certificate gives centered continuous scalar
coordinates for the p. 13 residual `D` block.

These coordinates describe the reduced block entries only; they are not part
of the regular-coordinate index. -/
theorem residualBlockScalarCoordinates_centered_continuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge) :
    let E : α → ∀ p : Fin N,
        Matrix
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
      fun x p ↦
        LinearMap.toMatrix
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
          (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let S : α →
        ChartLocalSuffixState (Fin (Module.finrank K U₀))
          (fun j : Fin (N + 1) ↦
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
          K (Fin.last N) 0 :=
      fun x ↦ ChartLocalSuffixState.suffixState (E x) (Fin.last N) 0
        (Fin.zero_le (Fin.last N))
    ∀ c : AoyagiResidualBlockCoordinateIndex
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀
          (Fin.last N))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0),
      AoyagiResidualBlockCoordinateIndex.value ((S x₀).D) c = 0 ∧
        ContinuousAt
          (fun x : α =>
            AoyagiResidualBlockCoordinateIndex.value ((S x).D) c) x₀ := by
  intro E S c
  rcases cert.coefficientFields_centered_continuous with
    ⟨_hCtop0, _hB0, _hF30, hD0, _hunit, _hCtop, _hB, _hF3, hD⟩
  exact
    AoyagiResidualBlockCoordinateIndex.value_centered_continuousAt
      (D := fun x : α ↦ (S x).D) hD0 hD c

omit [CompleteSpace K] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- The local source certificate carries enough basepoint rank data to identify
the residual scalar-coordinate index cardinality with the product of the
row/left and column/right residual endpoint dimensions. -/
theorem residualBlockCoordinateIndex_card_eq_endpointResidualEntryCount
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {H : ℕ → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    Fintype.card
        (AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) =
      (H 1 - r) * (H (N + 1) - r) :=
  paperEndpointResidualBlockCoordinateIndex_card_eq_endpointResidualEntryCount
    W B U₀ hU₀ cert.source_basepoint.1 hH

set_option linter.unusedSectionVars false in
/-- The canonical local certificate gives centered continuous scalar
coordinates for the cleaned p. 13 product-difference ideal family. -/
theorem productDifferenceScalarCoordinates_centered_continuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge) :
    let E : α → ∀ p : Fin N,
        Matrix
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
      fun x p ↦
        LinearMap.toMatrix
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
          (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let S : α →
        ChartLocalSuffixState (Fin (Module.finrank K U₀))
          (fun j : Fin (N + 1) ↦
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
          K (Fin.last N) 0 :=
      fun x ↦ ChartLocalSuffixState.suffixState (E x) (Fin.last N) 0
        (Fin.zero_le (Fin.last N))
    ∀ c : AoyagiProductDifferenceCoordinateIndex
        (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀
          (Fin.last N))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0),
      AoyagiProductDifferenceCoordinateIndex.value
          ((S x₀).Ctop - 1) (-(S x₀).B) (lowerLeftBlock (S x₀).L) ((S x₀).D) c = 0 ∧
        ContinuousAt
          (fun x : α =>
            AoyagiProductDifferenceCoordinateIndex.value
              ((S x).Ctop - 1) (-(S x).B) (lowerLeftBlock (S x).L) ((S x).D) c) x₀ := by
  intro E S c
  rcases cert.coefficientFields_centered_continuous with
    ⟨hCtop0, hB0, hF30, hD0, _hunit, hCtop, hB, hF3, hD⟩
  exact
    AoyagiProductDifferenceCoordinateIndex.value_centered_continuousAt
      (X := fun x : α ↦ (S x).Ctop - 1)
      (F2 := fun x : α ↦ -(S x).B)
      (F3 := fun x : α ↦ lowerLeftBlock (S x).L)
      (D := fun x : α ↦ (S x).D)
      hCtop0 hB0 hF30 hD0 hCtop hB hF3 hD c

omit [CompleteSpace K] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- The local source certificate carries enough basepoint rank data to identify
the full product-difference scalar-coordinate index cardinality with the
endpoint product entry count. -/
theorem productDifferenceCoordinateIndex_card_eq_endpointProductEntryCount
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {H : ℕ → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    Fintype.card
        (AoyagiProductDifferenceCoordinateIndex
          (Fin (Module.finrank K U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) =
      H 1 * H (N + 1) :=
  paperEndpointProductDifferenceCoordinateIndex_card_eq_endpointProductEntryCount
    W B U₀ hU₀ cert.source_basepoint.1 hH

end PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate

/-- Centered continuity of the scalar regular coordinates determined by the
fixed-base canonical product-difference suffix state. -/
def PaperEndpointFixedBaseRegularBlockScalarCoordinatesCenteredContinuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ) : Prop :=
  let E : α → ∀ p : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
    fun x p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  let S : α →
      ChartLocalSuffixState (Fin (Module.finrank K U₀))
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        K (Fin.last N) 0 :=
    fun x ↦ ChartLocalSuffixState.suffixState (E x) (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  ∀ c : AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0),
    AoyagiRegularBlockCoordinateIndex.value
        ((S x₀).Ctop - 1) (-(S x₀).B) (lowerLeftBlock (S x₀).L) c = 0 ∧
      ContinuousAt
        (fun x : α =>
          AoyagiRegularBlockCoordinateIndex.value
            ((S x).Ctop - 1) (-(S x).B) (lowerLeftBlock (S x).L) c) x₀

/-- Centered continuity of the scalar residual `D`-block coordinates determined
by the fixed-base canonical product-difference suffix state. -/
def PaperEndpointFixedBaseResidualBlockScalarCoordinatesCenteredContinuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ) : Prop :=
  let E : α → ∀ p : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
    fun x p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  let S : α →
      ChartLocalSuffixState (Fin (Module.finrank K U₀))
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        K (Fin.last N) 0 :=
    fun x ↦ ChartLocalSuffixState.suffixState (E x) (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  ∀ c : AoyagiResidualBlockCoordinateIndex
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀
        (Fin.last N))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0),
    AoyagiResidualBlockCoordinateIndex.value ((S x₀).D) c = 0 ∧
      ContinuousAt
        (fun x : α =>
          AoyagiResidualBlockCoordinateIndex.value ((S x).D) c) x₀

/-- Centered continuity of the scalar coordinates for the cleaned p. 13
product-difference ideal family. -/
def PaperEndpointFixedBaseProductDifferenceScalarCoordinatesCenteredContinuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ) : Prop :=
  let E : α → ∀ p : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
    fun x p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  let S : α →
      ChartLocalSuffixState (Fin (Module.finrank K U₀))
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        K (Fin.last N) 0 :=
    fun x ↦ ChartLocalSuffixState.suffixState (E x) (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  ∀ c : AoyagiProductDifferenceCoordinateIndex
      (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀
        (Fin.last N))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0),
    AoyagiProductDifferenceCoordinateIndex.value
        ((S x₀).Ctop - 1) (-(S x₀).B) (lowerLeftBlock (S x₀).L) ((S x₀).D) c = 0 ∧
      ContinuousAt
        (fun x : α =>
          AoyagiProductDifferenceCoordinateIndex.value
            ((S x).Ctop - 1) (-(S x).B) (lowerLeftBlock (S x).L) ((S x).D) c) x₀

/-- The Pi-valued map collecting the p. 13 regular block coordinates from the
fixed-base canonical product-difference suffix state.

This is only the coordinate family as a function into a product type.  It does
not assert that these coordinates form a chart. -/
def paperEndpointFixedBaseRegularBlockCoordinateMap
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α) :
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) → K :=
  let E : ∀ p : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
    fun p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  let S :
      ChartLocalSuffixState (Fin (Module.finrank K U₀))
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        K (Fin.last N) 0 :=
    ChartLocalSuffixState.suffixState E (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  AoyagiRegularBlockCoordinateIndex.value
    (S.Ctop - 1) (-(S.B)) (lowerLeftBlock S.L)

/-- The Pi-valued map collecting the residual `D`-block coordinates from the
fixed-base canonical product-difference suffix state. -/
def paperEndpointFixedBaseResidualBlockCoordinateMap
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α) :
    AoyagiResidualBlockCoordinateIndex
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀
        (Fin.last N))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) → K :=
  let E : ∀ p : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
    fun p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  let S :
      ChartLocalSuffixState (Fin (Module.finrank K U₀))
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        K (Fin.last N) 0 :=
    ChartLocalSuffixState.suffixState E (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  AoyagiResidualBlockCoordinateIndex.value S.D

/-- The Pi-valued map collecting the cleaned p. 13 product-difference
coordinates: regular block coordinates together with the residual `D` block. -/
def paperEndpointFixedBaseProductDifferenceCoordinateMap
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α) :
    AoyagiProductDifferenceCoordinateIndex
      (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀
        (Fin.last N))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) → K :=
  let E : ∀ p : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
    fun p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  let S :
      ChartLocalSuffixState (Fin (Module.finrank K U₀))
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        K (Fin.last N) 0 :=
    ChartLocalSuffixState.suffixState E (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  AoyagiProductDifferenceCoordinateIndex.value
    (S.Ctop - 1) (-(S.B)) (lowerLeftBlock S.L) S.D

/-- The Pi-valued map collecting the literal signed/corrected p. 13
product-difference coordinates:
`Ctop - 1`, `-B`, `lowerLeftBlock L`, and `D - F3 * F2`.

This is finite scalar bookkeeping for the literal block, not analytic
generator transport. -/
def paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α) :
    AoyagiProductDifferenceCoordinateIndex
      (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀
        (Fin.last N))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) → K :=
  let E : ∀ p : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
    fun p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  let S :
      ChartLocalSuffixState (Fin (Module.finrank K U₀))
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        K (Fin.last N) 0 :=
    ChartLocalSuffixState.suffixState E (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  AoyagiProductDifferenceCoordinateIndex.literalValue
    (S.Ctop - 1) (-(S.B)) (lowerLeftBlock S.L) S.D

set_option linter.unusedSectionVars false in
/-- The fixed-base cleaned product-difference coordinate map is the disjoint
sum of the regular block coordinate map and the residual coordinate map. -/
theorem paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_sumElim
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α) :
    paperEndpointFixedBaseProductDifferenceCoordinateMap W B U₀ hU₀ Cedge x =
      Sum.elim
        (paperEndpointFixedBaseRegularBlockCoordinateMap W B U₀ hU₀ Cedge x)
        (paperEndpointFixedBaseResidualBlockCoordinateMap W B U₀ hU₀ Cedge x) := by
  funext c
  cases c <;>
    simp [paperEndpointFixedBaseProductDifferenceCoordinateMap,
      paperEndpointFixedBaseRegularBlockCoordinateMap,
      paperEndpointFixedBaseResidualBlockCoordinateMap]

set_option linter.unusedSectionVars false in
/-- The fixed-base cleaned product-difference coordinate square-sum splits into
the regular coordinate square-sum plus the residual coordinate square-sum.

This is only finite square-sum bookkeeping for the cleaned p. 13 coordinate
family; it is not analytic generator transport from the literal signed block. -/
theorem paperEndpointFixedBaseProductDifferenceCoordinateMap_squareSum_eq_regular_add_residual
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α) :
    aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseProductDifferenceCoordinateMap W B U₀ hU₀ Cedge x) =
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseRegularBlockCoordinateMap W B U₀ hU₀ Cedge x) +
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap W B U₀ hU₀ Cedge x) := by
  rw [paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_sumElim]
  exact aoyagiCoordinateSquareSum_sumElim
    (paperEndpointFixedBaseRegularBlockCoordinateMap W B U₀ hU₀ Cedge x)
    (paperEndpointFixedBaseResidualBlockCoordinateMap W B U₀ hU₀ Cedge x)

/-- Fixed-base source data for Aoyagi's p. 13 scalar regular coordinates.

This packages the source-produced local certificate, the regular/residual ideal
split, centered continuous scalar regular and residual coordinates, and the
regular-variable/residual-entry counts.  Analytic ideal transport, chart
coverage, Jacobian compatibility, regular-suspension chart construction,
normal crossings, and RLCT remain outside this source-side package. -/
structure PaperEndpointFixedBaseRegularCoordinateSourceData
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (H : ℕ → ℕ) (r : ℕ) (rEdge : Fin N → ℕ) : Prop where
  dimensionConvention :
    ∀ k : Fin (N + 1), H (k.val + 1) = Module.finrank K (W k)
  localSourceCertificate :
    PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
      W B U₀ hU₀ x₀ Cedge r rEdge
  regularCoordinateIdealSourceNeighborhood :
    PaperEndpointFixedBaseRegularCoordinateIdealSourceNeighborhood
      W B U₀ hU₀ x₀ Cedge r rEdge
  productDifferenceCoordinateIdealSourceNeighborhood :
    PaperEndpointFixedBaseProductDifferenceCoordinateIdealSourceNeighborhood
      W B U₀ hU₀ x₀ Cedge r rEdge
  scalarCoordinates_centered_continuousAt :
    PaperEndpointFixedBaseRegularBlockScalarCoordinatesCenteredContinuousAt
      W B U₀ hU₀ x₀ Cedge
  residualScalarCoordinates_centered_continuousAt :
    PaperEndpointFixedBaseResidualBlockScalarCoordinatesCenteredContinuousAt
      W B U₀ hU₀ x₀ Cedge
  productDifferenceScalarCoordinates_centered_continuousAt :
    PaperEndpointFixedBaseProductDifferenceScalarCoordinatesCenteredContinuousAt
      W B U₀ hU₀ x₀ Cedge
  regularCoordinateIndex_card_eq_regularVariableCount :
    Fintype.card
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank K U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) =
      aoyagiTheorem2RegularVariableCount N H r
  residualCoordinateIndex_card_eq_endpointResidualEntryCount :
    Fintype.card
        (AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) =
      (H 1 - r) * (H (N + 1) - r)
  productDifferenceCoordinateIndex_card_eq_endpointProductEntryCount :
    Fintype.card
        (AoyagiProductDifferenceCoordinateIndex
          (Fin (Module.finrank K U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) =
      H 1 * H (N + 1)

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

set_option linter.unusedSectionVars false in
/-- The source-data package supplies a centered continuous Pi-valued regular
block coordinate map. -/
theorem regularBlockCoordinateMap_centered_continuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        W B U₀ hU₀ x₀ Cedge H r rEdge) :
    paperEndpointFixedBaseRegularBlockCoordinateMap W B U₀ hU₀ Cedge x₀ = 0 ∧
      ContinuousAt
        (paperEndpointFixedBaseRegularBlockCoordinateMap W B U₀ hU₀ Cedge)
        x₀ := by
  constructor
  · funext c
    simpa [paperEndpointFixedBaseRegularBlockCoordinateMap,
      PaperEndpointFixedBaseRegularBlockScalarCoordinatesCenteredContinuousAt] using
      (sourceData.scalarCoordinates_centered_continuousAt c).1
  · refine continuousAt_pi.2 ?_
    intro c
    simpa [paperEndpointFixedBaseRegularBlockCoordinateMap,
      PaperEndpointFixedBaseRegularBlockScalarCoordinatesCenteredContinuousAt] using
      (sourceData.scalarCoordinates_centered_continuousAt c).2

set_option linter.unusedSectionVars false in
/-- The source-data package supplies a centered continuous Pi-valued residual
block coordinate map. -/
theorem residualBlockCoordinateMap_centered_continuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        W B U₀ hU₀ x₀ Cedge H r rEdge) :
    paperEndpointFixedBaseResidualBlockCoordinateMap W B U₀ hU₀ Cedge x₀ = 0 ∧
      ContinuousAt
        (paperEndpointFixedBaseResidualBlockCoordinateMap W B U₀ hU₀ Cedge)
        x₀ := by
  constructor
  · funext c
    simpa [paperEndpointFixedBaseResidualBlockCoordinateMap,
      PaperEndpointFixedBaseResidualBlockScalarCoordinatesCenteredContinuousAt] using
      (sourceData.residualScalarCoordinates_centered_continuousAt c).1
  · refine continuousAt_pi.2 ?_
    intro c
    simpa [paperEndpointFixedBaseResidualBlockCoordinateMap,
      PaperEndpointFixedBaseResidualBlockScalarCoordinatesCenteredContinuousAt] using
      (sourceData.residualScalarCoordinates_centered_continuousAt c).2

set_option linter.unusedSectionVars false in
/-- The source-data package supplies a centered continuous Pi-valued
product-difference coordinate map. -/
theorem productDifferenceCoordinateMap_centered_continuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        W B U₀ hU₀ x₀ Cedge H r rEdge) :
    paperEndpointFixedBaseProductDifferenceCoordinateMap W B U₀ hU₀ Cedge x₀ = 0 ∧
      ContinuousAt
        (paperEndpointFixedBaseProductDifferenceCoordinateMap W B U₀ hU₀ Cedge)
        x₀ := by
  constructor
  · funext c
    simpa [paperEndpointFixedBaseProductDifferenceCoordinateMap,
      PaperEndpointFixedBaseProductDifferenceScalarCoordinatesCenteredContinuousAt] using
      (sourceData.productDifferenceScalarCoordinates_centered_continuousAt c).1
  · refine continuousAt_pi.2 ?_
    intro c
    simpa [paperEndpointFixedBaseProductDifferenceCoordinateMap,
      PaperEndpointFixedBaseProductDifferenceScalarCoordinatesCenteredContinuousAt] using
      (sourceData.productDifferenceScalarCoordinates_centered_continuousAt c).2

end PaperEndpointFixedBaseRegularCoordinateSourceData

namespace PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate

set_option linter.unusedSectionVars false in
/-- A fixed-base local source certificate supplies the regular-coordinate
source-data package once the layer-dimension convention is supplied. -/
theorem regularCoordinateSourceData
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    PaperEndpointFixedBaseRegularCoordinateSourceData
      W B U₀ hU₀ x₀ Cedge H r rEdge where
  dimensionConvention := hH
  localSourceCertificate := cert
  regularCoordinateIdealSourceNeighborhood :=
    cert.regularCoordinateIdealSourceNeighborhood
  productDifferenceCoordinateIdealSourceNeighborhood :=
    cert.productDifferenceCoordinateIdealSourceNeighborhood
  scalarCoordinates_centered_continuousAt := by
    simpa [PaperEndpointFixedBaseRegularBlockScalarCoordinatesCenteredContinuousAt] using
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.regularBlockScalarCoordinates_centered_continuousAt
        (W := W) (B := B) cert.localCertificate
  residualScalarCoordinates_centered_continuousAt := by
    simpa [PaperEndpointFixedBaseResidualBlockScalarCoordinatesCenteredContinuousAt] using
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.residualBlockScalarCoordinates_centered_continuousAt
        (W := W) (B := B) cert.localCertificate
  productDifferenceScalarCoordinates_centered_continuousAt := by
    simpa [PaperEndpointFixedBaseProductDifferenceScalarCoordinatesCenteredContinuousAt] using
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.productDifferenceScalarCoordinates_centered_continuousAt
        (W := W) (B := B) cert.localCertificate
  regularCoordinateIndex_card_eq_regularVariableCount :=
    PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.regularBlockCoordinateIndex_card_eq_regularVariableCount
      (W := W) (B := B) cert hH
  residualCoordinateIndex_card_eq_endpointResidualEntryCount :=
    PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.residualBlockCoordinateIndex_card_eq_endpointResidualEntryCount
      (W := W) (B := B) cert hH
  productDifferenceCoordinateIndex_card_eq_endpointProductEntryCount :=
    PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.productDifferenceCoordinateIndex_card_eq_endpointProductEntryCount
      (W := W) (B := B) cert hH

end PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate

set_option linter.unusedSectionVars false in
/-- Source rank data based at `B` produce fixed-base regular/residual coordinate
source data after choosing a total-kernel complement.

The theorem exposes the regular and residual coordinates, their centered
continuity, the regular/residual ideal split, the p. 13 regular-variable
count, and the residual endpoint entry count.  It does not assert exact-rank
openness or any analytic regular-suspension transport field. -/
theorem exists_paperEndpointFixedBaseRegularCoordinateSourceData_of_rank_eq
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (H : ℕ → ℕ) (r : ℕ) (rEdge : Fin N → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p))
    (hprod :
      Module.finrank K (LinearMap.range (paperTotalMap W B)) = r)
    (hedge :
      ∀ p : Fin N,
        Module.finrank K (LinearMap.range (reverseEdge W B p)) = rEdge p)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    ∃ U₀ : Submodule K (reverseVertex W 0),
      ∃ hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)),
        PaperEndpointFixedBaseRegularCoordinateSourceData
          W B U₀ hU₀ x₀ Cedge H r rEdge := by
  rcases exists_paperEndpointCanonicalProductDifferenceLocalSourceCertificate_of_rank_eq
      W B Cedge r rEdge hCedge hbase hprod hedge with
    ⟨U₀, hU₀, cert⟩
  exact
    ⟨U₀, hU₀,
      cert.regularCoordinateSourceData (W := W) (B := B) hH⟩

end FixedBaseCanonicalCertificate

section FixedBaseRealSmallness

variable {N : ℕ}
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)]
  [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, Module ℝ (W i)]
  [∀ i, ContinuousSMul ℝ (W i)]
  (B : ∀ i : Fin N, W i.succ →ₗ[ℝ] W i.castSucc)

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

set_option linter.unusedSectionVars false in
/-- The real fixed-base source-data package gives a neighborhood where the
actual p. 13 `F2` and `F3` regular-coordinate square-sums are jointly small. -/
theorem regularBlockCoordinateMap_f2_f3_squareSum_eventually_le_one
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge) :
    let ι := Fin (Module.finrank ℝ U₀)
    let μ :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)
    let ν :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0
    ∀ᶠ x in nhds x₀,
      aoyagiCoordinateSquareSum
          (fun ij : ι × ν =>
            paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x
              (Sum.inr (α := ι × ι) (Sum.inl (β := μ × ι) ij))) +
        aoyagiCoordinateSquareSum
          (fun ij : μ × ι =>
            paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x
              (Sum.inr (α := ι × ι) (Sum.inr (α := ι × ν) ij))) ≤
          1 := by
  let ι := Fin (Module.finrank ℝ U₀)
  let μ :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)
  let ν :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ 0
  let coord : α → AoyagiRegularBlockCoordinateIndex ι μ ν → ℝ :=
    paperEndpointFixedBaseRegularBlockCoordinateMap (K := ℝ) W B U₀ hU₀ Cedge
  have hcenter :
      coord x₀ = 0 ∧ ContinuousAt coord x₀ := by
    simpa [coord, ι, μ, ν] using
      regularBlockCoordinateMap_centered_continuousAt
        (W := W) (B := B) sourceData
  have hcoord :
      ∀ c : AoyagiRegularBlockCoordinateIndex ι μ ν,
        coord x₀ c = 0 ∧ ContinuousAt (fun x : α => coord x c) x₀ := by
    intro c
    exact
      ⟨congrFun hcenter.1 c,
        (continuous_apply c).continuousAt.comp hcenter.2⟩
  simpa [coord, ι, μ, ν] using
    AoyagiRegularBlockCoordinateIndex.f2_f3_squareSum_eventually_le_one_of_forall_centered_continuousAt
        (coord := coord) (x₀ := x₀) hcoord

set_option linter.unusedSectionVars false in
/-- The same smallness conclusion holds relative to the source-rank stratum,
because it has already been proved in an ambient neighborhood. -/
theorem regularBlockCoordinateMap_f2_f3_squareSum_eventually_le_one_nhdsWithin_source
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge) :
    let ι := Fin (Module.finrank ℝ U₀)
    let μ :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)
    let ν :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0
    ∀ᶠ x in
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
      aoyagiCoordinateSquareSum
          (fun ij : ι × ν =>
            paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x
              (Sum.inr (α := ι × ι) (Sum.inl (β := μ × ι) ij))) +
        aoyagiCoordinateSquareSum
          (fun ij : μ × ι =>
            paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x
              (Sum.inr (α := ι × ι) (Sum.inr (α := ι × ν) ij))) ≤
          1 := by
  exact
    (inf_le_left :
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge) ≤ nhds x₀)
      (regularBlockCoordinateMap_f2_f3_squareSum_eventually_le_one
        (W := W) (B := B) sourceData)

set_option linter.unusedSectionVars false in
/-- For the actual real fixed-base product-difference coordinate maps, the
literal signed/corrected square-sum and the cleaned square-sum are locally
equivalent up to factor `2`. -/
theorem literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge) :
    ∀ᶠ x in nhds x₀,
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) ≤
          2 * aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseProductDifferenceCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) ∧
        aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseProductDifferenceCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) ≤
          2 * aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) := by
  let ι := Fin (Module.finrank ℝ U₀)
  let μ :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)
  let ν :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ 0
  have hsmall :=
    regularBlockCoordinateMap_f2_f3_squareSum_eventually_le_one
      (W := W) (B := B) sourceData
  filter_upwards [hsmall] with x hxsmall
  let E : ∀ p : Fin N,
      Matrix
        (ι ⊕ throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (ι ⊕ throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) ℝ :=
    fun p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)
  let S :
      ChartLocalSuffixState ι
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        ℝ (Fin.last N) 0 :=
    ChartLocalSuffixState.suffixState E (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  have hsmallS :
      aoyagiCoordinateSquareSum
          (fun ij : ι × ν => (-(S.B)) ij.1 ij.2) +
        aoyagiCoordinateSquareSum
          (fun ij : μ × ι => lowerLeftBlock S.L ij.1 ij.2) ≤
          1 := by
    simpa [paperEndpointFixedBaseRegularBlockCoordinateMap, E, S, ι, μ, ν] using hxsmall
  constructor
  · simpa [paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap,
      paperEndpointFixedBaseProductDifferenceCoordinateMap, E, S, ι, μ, ν] using
      AoyagiProductDifferenceCoordinateIndex.literalCoordinateSquareSum_le_two_mul_coordinateSquareSum_of_f2_f3_squareSum_add_le_one
          (X := S.Ctop - 1) (F2 := -(S.B)) (F3 := lowerLeftBlock S.L) (D := S.D)
          hsmallS
  · simpa [paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap,
      paperEndpointFixedBaseProductDifferenceCoordinateMap, E, S, ι, μ, ν] using
      AoyagiProductDifferenceCoordinateIndex.coordinateSquareSum_le_two_mul_literalCoordinateSquareSum_of_f2_f3_squareSum_add_le_one
          (X := S.Ctop - 1) (F2 := -(S.B)) (F3 := lowerLeftBlock S.L) (D := S.D)
          hsmallS

set_option linter.unusedSectionVars false in
/-- Directional form of the local factor-`2` comparison: the literal
signed/corrected square-sum is bounded by twice the cleaned square-sum. -/
theorem literalProductDifferenceCoordinateMap_squareSum_eventually_le_two_mul_productDifferenceCoordinateMap_squareSum
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge) :
    ∀ᶠ x in nhds x₀,
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) ≤
        2 * aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) := by
  exact
    (literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two
      (W := W) (B := B) sourceData).mono (fun _ hx => hx.1)

set_option linter.unusedSectionVars false in
/-- Directional form of the local factor-`2` comparison: the cleaned square-sum
is bounded by twice the literal signed/corrected square-sum. -/
theorem productDifferenceCoordinateMap_squareSum_eventually_le_two_mul_literalProductDifferenceCoordinateMap_squareSum
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge) :
    ∀ᶠ x in nhds x₀,
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) ≤
        2 * aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) := by
  exact
    (literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two
      (W := W) (B := B) sourceData).mono (fun _ hx => hx.2)

set_option linter.unusedSectionVars false in
/-- The same factor-`2` comparison holds relative to the source-rank stratum,
as a filter weakening of the ambient comparison. -/
theorem literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two_nhdsWithin_source
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge) :
    ∀ᶠ x in
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) ≤
          2 * aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseProductDifferenceCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) ∧
        aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseProductDifferenceCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) ≤
          2 * aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) := by
  exact
    (inf_le_left :
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge) ≤ nhds x₀)
      (literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two
        (W := W) (B := B) sourceData)

set_option linter.unusedSectionVars false in
/-- Relative directional form: on the source-rank stratum filter, the literal
signed/corrected square-sum is bounded by twice the cleaned square-sum. -/
theorem literalProductDifferenceCoordinateMap_squareSum_eventually_le_two_mul_productDifferenceCoordinateMap_squareSum_nhdsWithin_source
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge) :
    ∀ᶠ x in
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) ≤
        2 * aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) := by
  exact
    (literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two_nhdsWithin_source
      (W := W) (B := B) sourceData).mono (fun _ hx => hx.1)

set_option linter.unusedSectionVars false in
/-- Relative directional form: on the source-rank stratum filter, the cleaned
square-sum is bounded by twice the literal signed/corrected square-sum. -/
theorem productDifferenceCoordinateMap_squareSum_eventually_le_two_mul_literalProductDifferenceCoordinateMap_squareSum_nhdsWithin_source
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge) :
    ∀ᶠ x in
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) ≤
        2 * aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) := by
  exact
    (literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two_nhdsWithin_source
      (W := W) (B := B) sourceData).mono (fun _ hx => hx.2)

end PaperEndpointFixedBaseRegularCoordinateSourceData

set_option linter.unusedSectionVars false in
/-- Source rank data produce fixed-base regular-coordinate source data and the
source-stratum factor-`2` comparison between the literal and cleaned p. 13
product-difference square-sums.

This is only a source-side finite square-sum wrapper.  It does not construct a
regular-suspension chart, prove analytic ideal transport, compute a Jacobian,
produce normal crossings, or extract an RLCT. -/
theorem exists_paperEndpointFixedBaseRegularCoordinateSourceData_literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two_nhdsWithin_source_of_rank_eq
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)
    (H : ℕ → ℕ) (r : ℕ) (rEdge : Fin N → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p))
    (hprod :
      Module.finrank ℝ (LinearMap.range (paperTotalMap W B)) = r)
    (hedge :
      ∀ p : Fin N,
        Module.finrank ℝ (LinearMap.range (reverseEdge W B p)) = rEdge p)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank ℝ (W k)) :
    ∃ U₀ : Submodule ℝ (reverseVertex W 0),
      ∃ hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)),
        PaperEndpointFixedBaseRegularCoordinateSourceData
            (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge ∧
          ∀ᶠ x in
            nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B Cedge r rEdge),
            aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) ≤
                2 * aoyagiCoordinateSquareSum
                  (paperEndpointFixedBaseProductDifferenceCoordinateMap
                    (K := ℝ) W B U₀ hU₀ Cedge x) ∧
              aoyagiCoordinateSquareSum
                  (paperEndpointFixedBaseProductDifferenceCoordinateMap
                    (K := ℝ) W B U₀ hU₀ Cedge x) ≤
                2 * aoyagiCoordinateSquareSum
                  (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
                    (K := ℝ) W B U₀ hU₀ Cedge x) := by
  rcases exists_paperEndpointFixedBaseRegularCoordinateSourceData_of_rank_eq
      (K := ℝ) W B Cedge H r rEdge hCedge hbase hprod hedge hH with
    ⟨U₀, hU₀, sourceData⟩
  exact
    ⟨U₀, hU₀, sourceData,
      PaperEndpointFixedBaseRegularCoordinateSourceData.literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two_nhdsWithin_source
          (W := W) (B := B) sourceData⟩

end FixedBaseRealSmallness

end Aoyagi
end DLN
end DLNFibre
