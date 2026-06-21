import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Interval-size arithmetic for Aoyagi's Lemma 5

This file isolates only the finite arithmetic behind the displayed interval
sizes in Aoyagi's Lemma 5.  It does not formalise the chart-family
construction, admissibility of the displayed vectors, pole order, normal
crossings, or RLCT extraction.
-/

open scoped BigOperators

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- The excess `|I_j|-1` of Aoyagi's Lemma 5 interval-size count, in closed
form.  The source interval size is `1 + excess`.

For source-facing use assume `1 <= ell` and `a <= ell`; the definition itself
is total over natural numbers. -/
def aoyagiLemma5IntervalExcess (ell a j : ℕ) : ℕ :=
  min j (min (ell - j) (min a (ell - a)))

/-- The displayed interval size in the elementary arithmetic layer of Lemma 5. -/
def aoyagiLemma5IntervalSize (ell a j : ℕ) : ℕ :=
  1 + aoyagiLemma5IntervalExcess ell a j

/-- In the initial overlap of the two Lemma 5 arms, the interval excess is
the coordinate index itself.

This is only the finite minimum calculation.  It does not assert that any
displayed source vector is legal or terminal. -/
theorem aoyagiLemma5IntervalExcess_eq_self_of_le_min
    (ell a p : ℕ) (ha : a ≤ ell)
    (hp_a : p ≤ a) (hp_c : p ≤ ell - a) :
    aoyagiLemma5IntervalExcess ell a p = p := by
  unfold aoyagiLemma5IntervalExcess
  apply Nat.min_eq_left
  exact Nat.le_min.mpr ⟨by omega, Nat.le_min.mpr ⟨hp_a, hp_c⟩⟩

/-- The selected-index guard needed by Aoyagi Lemma 5 equation `(4)`.

With `c = ell-a`, the printed tail cutoff `S_(p+c+2)` lies in the selected
list `S_1,...,S_(ell+1)` exactly when `p+1 <= a`.  Thus the printed guard
`p <= a` is one unit too weak at the boundary `p=a`. -/
theorem aoyagiLemma5Eq4_selectedIndexGuard_iff
    (ell a p : ℕ) (ha : a ≤ ell) :
    p + (ell - a) + 2 ≤ ell + 1 ↔ p + 1 ≤ a := by
  omega

/-- Strict form of the equation `(4)` selected-boundary guard.

Under `a<=ell`, the boundary index `p+(ell-a)+1` is strictly before the
terminal selected index `ell` exactly when `p+1<a`. -/
theorem aoyagiLemma5Eq4_boundaryIndex_lt_ell_iff
    (ell a p : ℕ) (ha : a ≤ ell) :
    p + (ell - a) + 1 < ell ↔ p + 1 < a := by
  omega

/-- Terminal form of the equation `(4)` selected-boundary guard.

Under `a<=ell`, the boundary index `p+(ell-a)+1` is the terminal selected
index `ell` exactly when `p+1=a`. -/
theorem aoyagiLemma5Eq4_boundaryIndex_eq_ell_iff
    (ell a p : ℕ) (ha : a ≤ ell) :
    p + (ell - a) + 1 = ell ↔ p + 1 = a := by
  omega

/-- At the strict equation `(4)` boundary block coordinate, the interval excess
has the advertised residual-minimum form. -/
theorem aoyagiLemma5Eq4_boundaryCoordinate_intervalExcess_eq_min
    (ell a p : ℕ) (ha : a ≤ ell) (hp_strict : p + 1 < a) :
    aoyagiLemma5IntervalExcess ell a (p + (ell - a) + 1) =
      min (ell - a) (a - p - 1) := by
  unfold aoyagiLemma5IntervalExcess
  omega

/-- The selected-index guard needed by Aoyagi Lemma 5 equation `(3)`.

With `c = ell-a`, the displayed special cutoff `S_(c+2)` lies in the selected
list `S_1,...,S_(ell+1)` exactly when `1 <= a`. -/
theorem aoyagiLemma5Eq3_selectedIndexGuard_iff
    (ell a : ℕ) (ha : a ≤ ell) :
    (ell - a) + 2 ≤ ell + 1 ↔ 1 ≤ a := by
  omega

/-- A fiber-count model for the same interval excess.  The rectangle has
`a * (ell-a)` points, and the level map is `(p,q) ↦ p+q+1`. -/
def aoyagiLemma5IntervalExcessFiber (ell a j : ℕ) : ℕ :=
  (((Finset.range a) ×ˢ (Finset.range (ell - a))).filter
    (fun p : ℕ × ℕ ↦ p.1 + p.2 + 1 = j)).card

/-- The fiber at level `j` is naturally indexed by the first coordinate in a
half-open interval. -/
theorem aoyagiLemma5IntervalExcessFiber_eq_Ico_card (ell a j : ℕ) :
    aoyagiLemma5IntervalExcessFiber ell a j =
      (Finset.Ico (j - (ell - a)) (min a j)).card := by
  unfold aoyagiLemma5IntervalExcessFiber
  apply Finset.card_bij (fun p _ ↦ p.1)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    rw [Finset.mem_Ico]
    omega
  · intro p hp q hq hpq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp hq
    ext
    · exact hpq
    · omega
  · intro i hi
    refine ⟨(i, j - 1 - i), ?_, rfl⟩
    simp only [Finset.mem_filter]
    constructor
    · rw [Finset.mem_product]
      rw [Finset.mem_Ico] at hi
      constructor <;> rw [Finset.mem_range] <;> omega
    · rw [Finset.mem_Ico] at hi
      omega

/-- The rectangle-fiber model equals the closed interval-excess formula. -/
theorem aoyagiLemma5IntervalExcessFiber_eq_excess (ell a j : ℕ) :
    aoyagiLemma5IntervalExcessFiber ell a j =
      aoyagiLemma5IntervalExcess ell a j := by
  rw [aoyagiLemma5IntervalExcessFiber_eq_Ico_card]
  rw [Nat.card_Ico]
  unfold aoyagiLemma5IntervalExcess
  omega

/-- Summing the fiber excess over all possible levels counts the rectangle. -/
theorem aoyagiLemma5IntervalExcessFiber_sum_range (ell a : ℕ) (ha : a ≤ ell) :
    (∑ j ∈ Finset.range (ell + 1), aoyagiLemma5IntervalExcessFiber ell a j) =
      a * (ell - a) := by
  unfold aoyagiLemma5IntervalExcessFiber
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  have hfilter : (((Finset.range a) ×ˢ (Finset.range (ell - a))).filter
      (fun p : ℕ × ℕ ↦ p.1 + p.2 + 1 ∈ Finset.range (ell + 1))) =
        ((Finset.range a) ×ˢ (Finset.range (ell - a))) := by
    apply Finset.filter_true_of_mem
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    rw [Finset.mem_range]
    omega
  rw [hfilter]
  simp [Finset.card_product]

/-- The closed interval-excess formula sums to `a*(ell-a)` over all levels. -/
theorem aoyagiLemma5IntervalExcess_sum_range (ell a : ℕ) (ha : a ≤ ell) :
    (∑ j ∈ Finset.range (ell + 1), aoyagiLemma5IntervalExcess ell a j) =
      a * (ell - a) := by
  rw [← aoyagiLemma5IntervalExcessFiber_sum_range ell a ha]
  apply Finset.sum_congr rfl
  intro j _
  exact (aoyagiLemma5IntervalExcessFiber_eq_excess ell a j).symm

/-- The lower endpoint has zero excess. -/
theorem aoyagiLemma5IntervalExcess_zero (ell a : ℕ) :
    aoyagiLemma5IntervalExcess ell a 0 = 0 := by
  simp [aoyagiLemma5IntervalExcess]

/-- The upper endpoint has zero excess. -/
theorem aoyagiLemma5IntervalExcess_top (ell a : ℕ) :
    aoyagiLemma5IntervalExcess ell a ell = 0 := by
  simp [aoyagiLemma5IntervalExcess]

/-- Decompose `range (ell+1)` into the two endpoints and the source interval
`1..ell-1`. -/
theorem aoyagiLemma5_range_succ_eq_insert_endpoints_Icc (ell : ℕ) :
    Finset.range (ell + 1) = insert 0 (insert ell (Finset.Icc 1 (ell - 1))) := by
  ext j
  simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
  omega

/-- Aoyagi's nontrivial interval-excess sum over `j=1,...,ell-1`.

This is only the finite excess-cardinality arithmetic used in Lemma 5.  It is
not the chart-family admissibility statement and does not by itself prove the
pole-order count. -/
theorem aoyagiLemma5IntervalExcess_sum_Icc (ell a : ℕ)
    (hell : 1 ≤ ell) (ha : a ≤ ell) :
    (∑ j ∈ Finset.Icc 1 (ell - 1), aoyagiLemma5IntervalExcess ell a j) =
      a * (ell - a) := by
  have hsum := aoyagiLemma5IntervalExcess_sum_range ell a ha
  rw [aoyagiLemma5_range_succ_eq_insert_endpoints_Icc ell] at hsum
  rw [Finset.sum_insert] at hsum
  · rw [Finset.sum_insert] at hsum
    · simpa [aoyagiLemma5IntervalExcess_zero, aoyagiLemma5IntervalExcess_top] using hsum
    · simp only [Finset.mem_Icc]
      omega
  · have hne : (0 : ℕ) ≠ ell := by omega
    simp [hne]

/-- Source-facing form: one baseline contribution plus the nontrivial
interval excesses is `a*(ell-a)+1`.

This proves only the elementary interval-size arithmetic.  The full Lemma 5
order count still requires the chart-family construction and admissibility
proof. -/
theorem aoyagiLemma5IntervalSize_excess_sum_Icc (ell a : ℕ)
    (hell : 1 ≤ ell) (ha : a ≤ ell) :
    1 + (∑ j ∈ Finset.Icc 1 (ell - 1),
        (aoyagiLemma5IntervalSize ell a j - 1)) =
      a * (ell - a) + 1 := by
  have h := aoyagiLemma5IntervalExcess_sum_Icc ell a hell ha
  simp [aoyagiLemma5IntervalSize] at h ⊢
  omega

end Aoyagi
end DLN
end DLNFibre
