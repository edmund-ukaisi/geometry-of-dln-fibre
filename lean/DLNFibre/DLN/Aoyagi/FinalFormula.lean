import DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector
import Mathlib.Data.Rat.Lemmas

/-!
# Source-facing final formula notation for Aoyagi Theorem 2

This file names the finite arithmetic appearing in Aoyagi Definition 3 and
Theorem 2.  It is a notation/translation layer only: it does not prove the
normal-crossing resolution, identify a statistical RLCT, prove the pole order,
or use the quiver-geometric paper.
-/

open scoped BigOperators

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- Aoyagi's reduced layer width `M^(s)=H^(s)-r`, with source layers numbered
from `1`.  It is kept integer-valued to avoid truncating `H s - r` before the
source rank hypothesis has been supplied. -/
def aoyagiReducedWidthInt (H : ℕ → ℕ) (r s : ℕ) : ℤ :=
  (H s : ℤ) - (r : ℤ)

/-- Under the rank-width bound at `s`, the integer reduced width is ordinary
Nat subtraction coerced to `Int`. -/
theorem aoyagiReducedWidthInt_eq_natCast_sub_of_rank_le
    (H : ℕ → ℕ) {r s : ℕ} (hr : r ≤ H s) :
    aoyagiReducedWidthInt H r s = ((H s - r : ℕ) : ℤ) := by
  unfold aoyagiReducedWidthInt
  exact (Int.natCast_sub hr).symm

/-- Under the rank-width bound at `s`, the reduced width is nonnegative. -/
theorem aoyagiReducedWidthInt_nonneg_of_rank_le
    (H : ℕ → ℕ) {r s : ℕ} (hr : r ≤ H s) :
    0 ≤ aoyagiReducedWidthInt H r s := by
  unfold aoyagiReducedWidthInt
  exact sub_nonneg.mpr (by exact_mod_cast hr)

/-- The selected reduced widths `M^(S_j)` attached to selected cutpoints. -/
def aoyagiSelectedReducedWidths {ell : ℕ}
    (H : ℕ → ℕ) (r : ℕ) (C : AoyagiSelectedCutpoints ell) :
    Fin (ell + 1) → ℤ :=
  fun j ↦ aoyagiReducedWidthInt H r (C.cut j)

/-- Selected reduced widths are pointwise reduced widths at the cutpoints. -/
@[simp] theorem aoyagiSelectedReducedWidths_apply {ell : ℕ}
    (H : ℕ → ℕ) (r : ℕ) (C : AoyagiSelectedCutpoints ell)
    (j : Fin (ell + 1)) :
    aoyagiSelectedReducedWidths H r C j =
      aoyagiReducedWidthInt H r (C.cut j) :=
  rfl

/-- Pointwise rank-width bounds give the Nat-subtraction form of selected
reduced widths. -/
theorem aoyagiSelectedReducedWidths_eq_natCast_sub_of_rank_le {ell : ℕ}
    (H : ℕ → ℕ) (r : ℕ) (C : AoyagiSelectedCutpoints ell)
    (hr : ∀ j : Fin (ell + 1), r ≤ H (C.cut j)) (j : Fin (ell + 1)) :
    aoyagiSelectedReducedWidths H r C j = ((H (C.cut j) - r : ℕ) : ℤ) := by
  unfold aoyagiSelectedReducedWidths
  exact aoyagiReducedWidthInt_eq_natCast_sub_of_rank_le H (hr j)

/-- Pointwise rank-width bounds make selected reduced widths nonnegative. -/
theorem aoyagiSelectedReducedWidths_nonneg_of_rank_le {ell : ℕ}
    (H : ℕ → ℕ) (r : ℕ) (C : AoyagiSelectedCutpoints ell)
    (hr : ∀ j : Fin (ell + 1), r ≤ H (C.cut j)) (j : Fin (ell + 1)) :
    0 ≤ aoyagiSelectedReducedWidths H r C j := by
  unfold aoyagiSelectedReducedWidths
  exact aoyagiReducedWidthInt_nonneg_of_rank_le H (hr j)

/-- Nat-indexed selected reduced widths agree with the finite selected family
on source-range indices. -/
@[simp] theorem aoyagiSelectedWidthNat_selectedReducedWidths_of_lt {ell : ℕ}
    (H : ℕ → ℕ) (r i : ℕ) (C : AoyagiSelectedCutpoints ell)
    (hi : i < ell + 1) :
    aoyagiSelectedWidthNat ell (aoyagiSelectedReducedWidths H r C) i =
      aoyagiReducedWidthInt H r (C.cut ⟨i, hi⟩) := by
  rw [aoyagiSelectedWidthNat_of_lt hi]
  rfl

/-- Fin-indexed form of the Nat-indexed selected reduced-width accessor. -/
@[simp] theorem aoyagiSelectedWidthNat_selectedReducedWidths_fin {ell : ℕ}
    (H : ℕ → ℕ) (r : ℕ) (C : AoyagiSelectedCutpoints ell)
    (j : Fin (ell + 1)) :
    aoyagiSelectedWidthNat ell (aoyagiSelectedReducedWidths H r C) j.val =
      aoyagiReducedWidthInt H r (C.cut j) := by
  rw [aoyagiSelectedWidthNat_selectedReducedWidths_of_lt H r j.val C j.isLt]

/-- Pointwise rank-width bounds make Nat-indexed selected reduced widths
nonnegative, including the zero extension outside the selected range. -/
theorem aoyagiSelectedWidthNat_selectedReducedWidths_nonneg_of_rank_le
    {ell : ℕ} (H : ℕ → ℕ) {r i : ℕ} (C : AoyagiSelectedCutpoints ell)
    (hr : ∀ j : Fin (ell + 1), r ≤ H (C.cut j)) :
    0 ≤ aoyagiSelectedWidthNat ell (aoyagiSelectedReducedWidths H r C) i := by
  by_cases hi : i < ell + 1
  · rw [aoyagiSelectedWidthNat_selectedReducedWidths_of_lt H r i C hi]
    exact aoyagiReducedWidthInt_nonneg_of_rank_le H (hr ⟨i, hi⟩)
  · unfold aoyagiSelectedWidthNat
    simp [hi]

/-- The selected value set called `M` in Aoyagi Definition 3.

Aoyagi also uses `M` for the ceiling-like integer below; Lean keeps these
names separate. -/
def aoyagiSelectedWidthValueSet {ell : ℕ}
    (m : Fin (ell + 1) → ℤ) : Finset ℤ :=
  Finset.univ.image m

/-- Definition 3's ceiling/excess arithmetic for a selected width family.

The source integer named `M` is called `ceilWidth`; the source integer `a` is
called `aParam`.  The field `selectedSum_eq` is the integral form of the
source definition `a = sum_j M^(S_j) - (ceilWidth-1)ell`; `aParam_pos` and
`aParam_le` record the residue bounds forced by
`ceilWidth - 1 < (sum_j M^(S_j))/ell <= ceilWidth`. -/
structure AoyagiDefinition3CeilData
    (ell : ℕ) (m : Fin (ell + 1) → ℤ) where
  ell_pos : 0 < ell
  ceilWidth : ℤ
  aParam : ℕ
  selectedSum_eq :
    (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (ceilWidth - 1) + aParam
  aParam_pos : 0 < aParam
  aParam_le : aParam ≤ ell

namespace AoyagiDefinition3CeilData

/-- Aoyagi Theorem 2's displayed order/multiplicity expression, named as an
order formula to avoid confusion with this repository's component-count
`theta`. -/
def theorem2OrderFormula {ell : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m) : ℕ :=
  data.aParam * (ell - data.aParam) + 1

@[simp] theorem theorem2OrderFormula_eq {ell : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m) :
    data.theorem2OrderFormula = data.aParam * (ell - data.aParam) + 1 :=
  rfl

end AoyagiDefinition3CeilData

/-- The regular-variable contribution in Aoyagi Theorem 2:
`(-r^2+r(H^(1)+H^(L+1)))/2`. -/
def aoyagiTheorem2RegularTerm (L : ℕ) (H : ℕ → ℕ) (r : ℕ) : ℚ :=
  (-((r : ℚ) ^ 2) + (r : ℚ) * ((H 1 : ℚ) + (H (L + 1) : ℚ))) / 2

/-- The scalar count of the three regular block families after Aoyagi Theorem 3:
`C1-Er`, `F2`, and `F3`. -/
def aoyagiTheorem2RegularVariableCount (L : ℕ) (H : ℕ → ℕ) (r : ℕ) : ℕ :=
  r * r + r * (H (L + 1) - r) + (H 1 - r) * r

/-- The finite regular block-entry count gives the regular term in the
displayed Theorem 2 lambda formula.

This is only arithmetic for the count of the three regular block families.  It
does not prove regular-suspension normal crossings or RLCT additivity. -/
theorem aoyagiTheorem2RegularTerm_eq_half_regularVariableCount
    (L : ℕ) (H : ℕ → ℕ) {r : ℕ}
    (hsource : r ≤ H 1) (htarget : r ≤ H (L + 1)) :
    aoyagiTheorem2RegularTerm L H r =
      (aoyagiTheorem2RegularVariableCount L H r : ℚ) / 2 := by
  unfold aoyagiTheorem2RegularTerm aoyagiTheorem2RegularVariableCount
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_sub htarget, Nat.cast_sub hsource]
  ring

/-- The selected-width average appearing in the first displayed form of
Aoyagi Theorem 2.  The denominator is Aoyagi's `ell`, although there are
`ell+1` selected widths. -/
def aoyagiSelectedWidthAverage (ell : ℕ) (m : Fin (ell + 1) → ℤ) : ℚ :=
  (∑ j : Fin (ell + 1), (m j : ℚ)) / (ell : ℚ)

/-- Definition 3's selected-sum identity rewrites Aoyagi's selected average
as the ceiling integer plus `(a-ell)/ell`. -/
theorem AoyagiDefinition3CeilData.selectedWidthAverage_eq_ceil
    {ell : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m) :
    aoyagiSelectedWidthAverage ell m =
      (data.ceilWidth : ℚ) + (((data.aParam : ℚ) - (ell : ℚ)) / (ell : ℚ)) := by
  have hselectedQ :
      (∑ j : Fin (ell + 1), (m j : ℚ)) =
        (ell : ℚ) * ((data.ceilWidth : ℚ) - 1) + data.aParam := by
    exact_mod_cast data.selectedSum_eq
  have hellQ : (ell : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt data.ell_pos)
  unfold aoyagiSelectedWidthAverage
  rw [hselectedQ]
  field_simp [hellQ]
  ring

/-- The pair sum `sum_{1 <= i < j <= ell+1} M^(S_i)M^(S_j)` in zero-based
Lean indexing. -/
def aoyagiSelectedWidthPairSum (ell : ℕ) (m : Fin (ell + 1) → ℤ) : ℚ :=
  ∑ i : Fin (ell + 1), ∑ j : Fin (ell + 1),
    if i.val < j.val then (m i : ℚ) * (m j : ℚ) else 0

/-- The selected-width pair sum, rewritten with Nat indices and the total
selected-width accessor.

This is only an indexing conversion.  It is useful when comparing the
source-facing Theorem 2 formula with range/Icc summation APIs. -/
theorem aoyagiSelectedWidthPairSum_eq_range_Icc_selectedWidthNat
    (ell : ℕ) (m : Fin (ell + 1) → ℤ) :
    aoyagiSelectedWidthPairSum ell m =
      ∑ i ∈ Finset.range (ell + 1), ∑ j ∈ Finset.Icc (i + 1) ell,
        (aoyagiSelectedWidthNat ell m i : ℚ) *
          (aoyagiSelectedWidthNat ell m j : ℚ) := by
  classical
  unfold aoyagiSelectedWidthPairSum
  set w : ℕ → ℤ := aoyagiSelectedWidthNat ell m with hw
  have hw_fin : ∀ i : Fin (ell + 1), w i.val = m i := by
    intro i
    rw [hw]
    exact aoyagiSelectedWidthNat_of_lt i.isLt
  have hrewrite :
      (∑ i : Fin (ell + 1), ∑ j : Fin (ell + 1),
          if i.val < j.val then (m i : ℚ) * (m j : ℚ) else 0) =
      (∑ i : Fin (ell + 1), ∑ j : Fin (ell + 1),
          if i.val < j.val then (w i.val : ℚ) * (w j.val : ℚ) else 0) := by
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    rw [hw_fin i, hw_fin j]
  rw [hrewrite]
  rw [Fin.sum_univ_eq_sum_range
    (fun i ↦ ∑ j : Fin (ell + 1),
      if i < j.val then (w i : ℚ) * (w j.val : ℚ) else 0) (ell + 1)]
  refine Finset.sum_congr rfl (fun i hi ↦ ?_)
  rw [Finset.mem_range] at hi
  rw [Fin.sum_univ_eq_sum_range
    (fun j ↦ if i < j then (w i : ℚ) * (w j : ℚ) else 0) (ell + 1)]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr ?_ (fun _ _ ↦ rfl)
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  omega

/-- First source-facing display for Aoyagi Theorem 2's `lambda`, using the
selected-width average. -/
def aoyagiTheorem2Lambda_average
    (L ell : ℕ) (H : ℕ → ℕ) (r a : ℕ) (m : Fin (ell + 1) → ℤ) : ℚ :=
  aoyagiTheorem2RegularTerm L H r +
    ((a : ℚ) * ((ell : ℚ) - (a : ℚ))) / (4 * (ell : ℚ)) -
    (((ell : ℚ) * ((ell : ℚ) - 1)) / 4) *
      (aoyagiSelectedWidthAverage ell m) ^ 2 +
    aoyagiSelectedWidthPairSum ell m / 2

/-- Second source-facing display for Aoyagi Theorem 2's `lambda`, using
Definition 3's ceiling integer. -/
def aoyagiTheorem2Lambda_ceil
    (L ell : ℕ) (H : ℕ → ℕ) (r a : ℕ) (ceilWidth : ℤ)
    (m : Fin (ell + 1) → ℤ) : ℚ :=
  aoyagiTheorem2RegularTerm L H r +
    ((a : ℚ) * ((ell : ℚ) - (a : ℚ))) / (4 * (ell : ℚ)) -
    (((ell : ℚ) * ((ell : ℚ) - 1)) / 4) *
      ((ceilWidth : ℚ) + (((a : ℚ) - (ell : ℚ)) / (ell : ℚ))) ^ 2 +
    aoyagiSelectedWidthPairSum ell m / 2

/-- Expanded source-facing display for Aoyagi Theorem 2's `lambda`. -/
def aoyagiTheorem2Lambda_expanded
    (L ell : ℕ) (H : ℕ → ℕ) (r a : ℕ) (ceilWidth : ℤ)
    (m : Fin (ell + 1) → ℤ) : ℚ :=
  aoyagiTheorem2RegularTerm L H r -
    (((ell : ℚ) - (a : ℚ) - 1) * ((ell : ℚ) - (a : ℚ))) / 4 -
    (((ell : ℚ) * ((ell : ℚ) - 1)) / 4) *
      ((ceilWidth : ℚ) ^ 2 +
        2 * (((a : ℚ) - (ell : ℚ)) / (ell : ℚ)) * (ceilWidth : ℚ)) +
    aoyagiSelectedWidthPairSum ell m / 2

/-- The second and third displayed forms of Aoyagi Theorem 2's `lambda`
formula agree by rational arithmetic when `ell > 0`. -/
theorem aoyagiTheorem2Lambda_ceil_eq_expanded
    (L ell : ℕ) (H : ℕ → ℕ) (r a : ℕ) (ceilWidth : ℤ)
    (m : Fin (ell + 1) → ℤ) (hell : 0 < ell) :
    aoyagiTheorem2Lambda_ceil L ell H r a ceilWidth m =
      aoyagiTheorem2Lambda_expanded L ell H r a ceilWidth m := by
  have hellQ : (ell : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hell)
  unfold aoyagiTheorem2Lambda_ceil aoyagiTheorem2Lambda_expanded
  field_simp [hellQ]
  ring

/-- Theorem 2's `lambda` formula using a supplied Definition 3 ceiling datum.

This is still formula notation only; it does not assert that this value is the
statistical RLCT. -/
def aoyagiTheorem2Lambda_fromCeilData
    (L ell : ℕ) (H : ℕ → ℕ) (r : ℕ) (m : Fin (ell + 1) → ℤ)
    (data : AoyagiDefinition3CeilData ell m) : ℚ :=
  aoyagiTheorem2Lambda_ceil L ell H r data.aParam data.ceilWidth m

/-- If Definition 3's selected average is rewritten using the ceiling integer,
the first two displayed `lambda` formulas are definitionally the same
arithmetic expression.

This is formula bookkeeping only.  It does not prove that either value is an
RLCT. -/
theorem aoyagiTheorem2Lambda_average_eq_ceil_of_average_eq
    (L ell : ℕ) (H : ℕ → ℕ) (r a : ℕ) (ceilWidth : ℤ)
    (m : Fin (ell + 1) → ℤ)
    (havg :
      aoyagiSelectedWidthAverage ell m =
        (ceilWidth : ℚ) + (((a : ℚ) - (ell : ℚ)) / (ell : ℚ))) :
    aoyagiTheorem2Lambda_average L ell H r a m =
      aoyagiTheorem2Lambda_ceil L ell H r a ceilWidth m := by
  unfold aoyagiTheorem2Lambda_average aoyagiTheorem2Lambda_ceil
  rw [havg]

/-- For a supplied Definition 3 ceiling datum, the average and ceiling
versions of Aoyagi Theorem 2's displayed `lambda` formula agree.

This is formula bookkeeping only.  It does not prove that either value is an
RLCT. -/
theorem aoyagiTheorem2Lambda_average_eq_fromCeilData
    (L ell : ℕ) (H : ℕ → ℕ) (r : ℕ) (m : Fin (ell + 1) → ℤ)
    (data : AoyagiDefinition3CeilData ell m) :
    aoyagiTheorem2Lambda_average L ell H r data.aParam m =
      aoyagiTheorem2Lambda_fromCeilData L ell H r m data := by
  unfold aoyagiTheorem2Lambda_fromCeilData
  exact aoyagiTheorem2Lambda_average_eq_ceil_of_average_eq
    L ell H r data.aParam data.ceilWidth m data.selectedWidthAverage_eq_ceil

/-- For a supplied Definition 3 ceiling datum, the average and expanded
versions of Aoyagi Theorem 2's displayed `lambda` formula agree.

This is formula bookkeeping only.  It does not prove that either value is an
RLCT. -/
theorem aoyagiTheorem2Lambda_average_eq_expanded_ofCeilData
    (L ell : ℕ) (H : ℕ → ℕ) (r : ℕ) (m : Fin (ell + 1) → ℤ)
    (data : AoyagiDefinition3CeilData ell m) :
    aoyagiTheorem2Lambda_average L ell H r data.aParam m =
      aoyagiTheorem2Lambda_expanded L ell H r data.aParam data.ceilWidth m := by
  rw [aoyagiTheorem2Lambda_average_eq_fromCeilData L ell H r m data]
  unfold aoyagiTheorem2Lambda_fromCeilData
  exact aoyagiTheorem2Lambda_ceil_eq_expanded
    L ell H r data.aParam data.ceilWidth m data.ell_pos

end Aoyagi
end DLN
end DLNFibre
