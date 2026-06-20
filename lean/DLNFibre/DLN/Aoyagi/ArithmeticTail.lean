import Mathlib.Data.Int.Order.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

/-!
# Arithmetic tail for Aoyagi's Lemma 3

This file isolates the elementary integer arithmetic in Aoyagi's Lemma 3.  It
does not formalise the terminal candidate set, feasibility of exponent chains,
pole order, normal crossings, or RLCT extraction.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- The numerator of Aoyagi's Lemma 3 quadratic after clearing the denominator
`ell^2`.

The source writes
`A(b)/ell^2 = b((ell-a)/ell)^2 + (ell-1-b)(-a/ell)^2
  + (b(ell-a)/ell - (ell-1-b)a/ell)^2`.
This definition is the corresponding integer numerator. -/
def aoyagiLemma3A (ell a b : ℤ) : ℤ :=
  b * (ell - a) ^ 2 +
    (ell - 1 - b) * a ^ 2 +
      (b * (ell - a) - (ell - 1 - b) * a) ^ 2

/-- Aoyagi's Lemma 3 quadratic, in completed-square form over the integers. -/
theorem aoyagiLemma3A_eq_min_add (ell a b : ℤ) :
    aoyagiLemma3A ell a b =
      a * ell * (ell - a) + ell ^ 2 * (b - a) * (b - a + 1) := by
  unfold aoyagiLemma3A
  ring

/-- For any integer `x`, the product of consecutive integers `x(x+1)` is
nonnegative. -/
theorem int_mul_succ_nonneg (x : ℤ) : 0 ≤ x * (x + 1) := by
  by_cases hx : 0 ≤ x
  · exact mul_nonneg hx (by omega)
  · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

/-- The completed-square form gives the universal lower bound in Lemma 3. -/
theorem aoyagiLemma3A_min_le (ell a b : ℤ) :
    a * ell * (ell - a) ≤ aoyagiLemma3A ell a b := by
  rw [aoyagiLemma3A_eq_min_add]
  have hsquare : 0 ≤ ell ^ 2 := sq_nonneg ell
  have hconsecutive : 0 ≤ (b - a) * (b - a + 1) :=
    int_mul_succ_nonneg (b - a)
  have hterm : 0 ≤ ell ^ 2 * ((b - a) * (b - a + 1)) :=
    mul_nonneg hsquare hconsecutive
  nlinarith

/-- The right-hand interior candidate `b=a` attains the Lemma 3 lower bound.

This candidate belongs to the source range `0 <= b <= ell-1` only when
`a <= ell-1`; see `aoyagiLemma3A_minimizer_right_mem`. -/
theorem aoyagiLemma3A_at_right (ell a : ℤ) :
    aoyagiLemma3A ell a a = a * ell * (ell - a) := by
  rw [aoyagiLemma3A_eq_min_add]
  ring

/-- The left-hand interior candidate `b=a-1` attains the Lemma 3 lower bound.

This candidate belongs to the source range `0 <= b <= ell-1` only when
`1 <= a`; see `aoyagiLemma3A_minimizer_left_mem`. -/
theorem aoyagiLemma3A_at_left (ell a : ℤ) :
    aoyagiLemma3A ell a (a - 1) = a * ell * (ell - a) := by
  rw [aoyagiLemma3A_eq_min_add]
  ring

/-- The two adjacent integers `b=a` and `b=a-1` are the only equality cases
for the isolated Lemma 3 integer lower bound when `ell` is nonzero. -/
theorem aoyagiLemma3A_eq_min_iff (ell a b : ℤ) (hell : ell ≠ 0) :
    aoyagiLemma3A ell a b = a * ell * (ell - a) ↔ b = a ∨ b = a - 1 := by
  constructor
  · intro h
    rw [aoyagiLemma3A_eq_min_add] at h
    have hterm : ell ^ 2 * (b - a) * (b - a + 1) = 0 := by
      nlinarith
    have hterm_assoc : ell ^ 2 * ((b - a) * (b - a + 1)) = 0 := by
      nlinarith [hterm]
    have hellsq : ell ^ 2 ≠ 0 := pow_ne_zero 2 hell
    rcases mul_eq_zero.mp hterm_assoc with hsquare | hconsecutive
    · exact False.elim (hellsq hsquare)
    · rcases mul_eq_zero.mp hconsecutive with hright | hleft
      · left
        omega
      · right
        omega
  · intro h
    rcases h with hb | hb
    · rw [hb]
      exact aoyagiLemma3A_at_right ell a
    · rw [hb]
      exact aoyagiLemma3A_at_left ell a

/-- Equality cases for the isolated Lemma 3 lower bound after intersecting
with the source integer interval `0 <= b <= ell-1`.

This is only interval bookkeeping for the integer numerator.  It does not
prove that either equality case is realised by an admissible exponent chain in
Aoyagi's construction. -/
theorem aoyagiLemma3A_eq_min_iff_source_Icc (ell a b : ℤ)
    (hell : 1 ≤ ell) (hb0 : 0 ≤ b) (hbtop : b ≤ ell - 1) :
    aoyagiLemma3A ell a b = a * ell * (ell - a) ↔
      (b = a ∧ a ≤ ell - 1) ∨ (b = a - 1 ∧ 1 ≤ a) := by
  have hellne : ell ≠ 0 := by omega
  rw [aoyagiLemma3A_eq_min_iff ell a b hellne]
  constructor
  · intro h
    rcases h with hright | hleft
    · left
      constructor
      · exact hright
      · omega
    · right
      constructor
      · exact hleft
      · omega
  · intro h
    rcases h with hright | hleft
    · left
      exact hright.1
    · right
      exact hleft.1

/-- At the lower endpoint `a=0`, the source interval removes the formal
candidate `b=-1`, leaving only `b=0`. -/
theorem aoyagiLemma3A_eq_min_iff_source_Icc_zero (ell b : ℤ)
    (hell : 1 ≤ ell) (hb0 : 0 ≤ b) :
    aoyagiLemma3A ell 0 b = 0 ↔ b = 0 := by
  have hellne : ell ≠ 0 := by omega
  constructor
  · intro h
    have hmin : aoyagiLemma3A ell 0 b = 0 * ell * (ell - 0) := by
      simpa using h
    rcases (aoyagiLemma3A_eq_min_iff ell 0 b hellne).mp hmin with hright | hleft
    · exact hright
    · omega
  · intro hb
    have hmin :
        aoyagiLemma3A ell 0 b = 0 * ell * (ell - 0) :=
      (aoyagiLemma3A_eq_min_iff ell 0 b hellne).mpr (Or.inl hb)
    simpa using hmin

/-- At the upper endpoint `a=ell`, the source interval removes the formal
candidate `b=ell`, leaving only `b=ell-1`. -/
theorem aoyagiLemma3A_eq_min_iff_source_Icc_top (ell b : ℤ)
    (hell : 1 ≤ ell) (hbtop : b ≤ ell - 1) :
    aoyagiLemma3A ell ell b = 0 ↔ b = ell - 1 := by
  have hellne : ell ≠ 0 := by omega
  constructor
  · intro h
    have hmin : aoyagiLemma3A ell ell b = ell * ell * (ell - ell) := by
      simpa using h
    rcases (aoyagiLemma3A_eq_min_iff ell ell b hellne).mp hmin with hright | hleft
    · omega
    · exact hleft
  · intro hb
    have hmin :
        aoyagiLemma3A ell ell b = ell * ell * (ell - ell) :=
      (aoyagiLemma3A_eq_min_iff ell ell b hellne).mpr (Or.inr hb)
    simpa using hmin

/-- The finite set of integer `b` in Aoyagi's Lemma 3 source interval that
attain the isolated numerator lower bound. -/
noncomputable def aoyagiLemma3AMinimizerSet (ell a : ℤ) : Finset ℤ :=
  (Finset.Icc (0 : ℤ) (ell - 1)).filter
    (fun b ↦ aoyagiLemma3A ell a b = a * ell * (ell - a))

/-- At `a=0`, the isolated equality set is the singleton `{0}`. -/
theorem aoyagiLemma3AMinimizerSet_eq_zero (ell : ℤ) (hell : 1 ≤ ell) :
    aoyagiLemma3AMinimizerSet ell 0 = {0} := by
  ext b
  simp only [aoyagiLemma3AMinimizerSet, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_singleton]
  constructor
  · intro h
    have hzero : aoyagiLemma3A ell 0 b = 0 := by
      simpa using h.2
    exact (aoyagiLemma3A_eq_min_iff_source_Icc_zero ell b hell h.1.1).mp hzero
  · intro hb
    constructor
    · constructor <;> omega
    · have hzero : aoyagiLemma3A ell 0 b = 0 :=
        (aoyagiLemma3A_eq_min_iff_source_Icc_zero ell b hell (by omega)).mpr hb
      simpa using hzero

/-- At `a=ell`, the isolated equality set is the singleton `{ell-1}`. -/
theorem aoyagiLemma3AMinimizerSet_eq_top (ell : ℤ) (hell : 1 ≤ ell) :
    aoyagiLemma3AMinimizerSet ell ell = {ell - 1} := by
  ext b
  simp only [aoyagiLemma3AMinimizerSet, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_singleton]
  constructor
  · intro h
    have hzero : aoyagiLemma3A ell ell b = 0 := by
      simpa using h.2
    exact (aoyagiLemma3A_eq_min_iff_source_Icc_top ell b hell h.1.2).mp hzero
  · intro hb
    constructor
    · constructor <;> omega
    · have hzero : aoyagiLemma3A ell ell b = 0 :=
        (aoyagiLemma3A_eq_min_iff_source_Icc_top ell b hell (by omega)).mpr hb
      simpa using hzero

/-- In the strict interior `0 < a < ell`, the isolated equality set has the
two adjacent candidates `{a-1,a}`. -/
theorem aoyagiLemma3AMinimizerSet_eq_interior (ell a : ℤ)
    (hell : 1 ≤ ell) (ha0 : 0 < a) (haell : a < ell) :
    aoyagiLemma3AMinimizerSet ell a = {a - 1, a} := by
  ext b
  simp only [aoyagiLemma3AMinimizerSet, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    rcases (aoyagiLemma3A_eq_min_iff_source_Icc ell a b hell h.1.1 h.1.2).mp h.2
      with hright | hleft
    · right
      exact hright.1
    · left
      exact hleft.1
  · intro h
    rcases h with hb | hb
    · rw [hb]
      constructor
      · constructor <;> omega
      · exact aoyagiLemma3A_at_left ell a
    · rw [hb]
      constructor
      · constructor <;> omega
      · exact aoyagiLemma3A_at_right ell a

/-- At the lower endpoint, the isolated equality set has cardinality one. -/
theorem aoyagiLemma3AMinimizerSet_card_zero (ell : ℤ) (hell : 1 ≤ ell) :
    (aoyagiLemma3AMinimizerSet ell 0).card = 1 := by
  rw [aoyagiLemma3AMinimizerSet_eq_zero ell hell, Finset.card_singleton]

/-- At the upper endpoint, the isolated equality set has cardinality one. -/
theorem aoyagiLemma3AMinimizerSet_card_top (ell : ℤ) (hell : 1 ≤ ell) :
    (aoyagiLemma3AMinimizerSet ell ell).card = 1 := by
  rw [aoyagiLemma3AMinimizerSet_eq_top ell hell, Finset.card_singleton]

/-- In the strict interior, the isolated equality set has cardinality two. -/
theorem aoyagiLemma3AMinimizerSet_card_interior (ell a : ℤ)
    (hell : 1 ≤ ell) (ha0 : 0 < a) (haell : a < ell) :
    (aoyagiLemma3AMinimizerSet ell a).card = 2 := by
  rw [aoyagiLemma3AMinimizerSet_eq_interior ell a hell ha0 haell, Finset.card_pair]
  omega

/-- Endpoint-corrected cardinality of the isolated equality set in Aoyagi's
Lemma 3 integer arithmetic.

This counts only the integer parameter `b` in the source interval.  It does not
count admissible exponent chains or prove the Lemma 5 pole-order count. -/
theorem aoyagiLemma3AMinimizerSet_card (ell a : ℤ)
    (hell : 1 ≤ ell) (ha0 : 0 ≤ a) (haell : a ≤ ell) :
    (aoyagiLemma3AMinimizerSet ell a).card =
      1 + if 0 < a ∧ a < ell then 1 else 0 := by
  by_cases hinterior : 0 < a ∧ a < ell
  · rw [aoyagiLemma3AMinimizerSet_card_interior ell a hell hinterior.1 hinterior.2]
    simp [hinterior]
  · have hend : a = 0 ∨ a = ell := by omega
    rcases hend with hzero | htop
    · subst a
      simp [aoyagiLemma3AMinimizerSet_card_zero ell hell]
    · subst a
      simp [aoyagiLemma3AMinimizerSet_card_top ell hell]

/-- If `0 <= a <= ell-1`, the candidate `b=a` is in Aoyagi's Lemma 3
integer range. -/
theorem aoyagiLemma3A_minimizer_right_mem {ell a : ℤ}
    (ha0 : 0 ≤ a) (haell : a ≤ ell - 1) :
    0 ≤ a ∧ a ≤ ell - 1 :=
  ⟨ha0, haell⟩

/-- If `1 <= a <= ell`, the candidate `b=a-1` is in Aoyagi's Lemma 3
integer range. -/
theorem aoyagiLemma3A_minimizer_left_mem {ell a : ℤ}
    (ha0 : 1 ≤ a) (haell : a ≤ ell) :
    0 ≤ a - 1 ∧ a - 1 ≤ ell - 1 := by
  constructor <;> omega

/-- Endpoint-corrected minimum statement for Aoyagi's Lemma 3 numerator.

For `1 <= ell` and `0 <= a <= ell`, the least value of `aoyagiLemma3A ell a b`
over integer `b` satisfying `0 <= b <= ell-1` is `a*ell*(ell-a)`.
The witness is `b=0` when `a=0`, and `b=a-1` when `1 <= a`, including the
endpoint `a=ell`.  This is only the integer algebra of Lemma 3; it does not
prove that the minimizing `b` values are feasible exponent chains. -/
theorem aoyagiLemma3A_isLeast_image_Icc (ell a : ℤ)
    (hell : 1 ≤ ell) (ha0 : 0 ≤ a) (haell : a ≤ ell) :
    IsLeast
      {v : ℤ | ∃ b : ℤ, 0 ≤ b ∧ b ≤ ell - 1 ∧ aoyagiLemma3A ell a b = v}
      (a * ell * (ell - a)) := by
  constructor
  · by_cases hzero : a = 0
    · refine ⟨0, ?_, ?_, ?_⟩
      · omega
      · omega
      · simpa [hzero] using aoyagiLemma3A_at_right ell a
    · have hapos : 1 ≤ a := by omega
      refine ⟨a - 1, ?_, ?_, ?_⟩
      · exact (aoyagiLemma3A_minimizer_left_mem hapos haell).1
      · exact (aoyagiLemma3A_minimizer_left_mem hapos haell).2
      · exact aoyagiLemma3A_at_left ell a
  · intro v hv
    rcases hv with ⟨b, _hb0, _hbtop, rfl⟩
    exact aoyagiLemma3A_min_le ell a b

/-- The conventional lower endpoint `a=0` has witness `b=0`. -/
theorem aoyagiLemma3A_isLeast_image_Icc_zero (ell : ℤ) (hell : 1 ≤ ell) :
    IsLeast
      {v : ℤ | ∃ b : ℤ, 0 ≤ b ∧ b ≤ ell - 1 ∧ aoyagiLemma3A ell 0 b = v}
      0 := by
  simpa using aoyagiLemma3A_isLeast_image_Icc ell 0 hell (by omega) (by omega)

/-- The upper endpoint `a=ell` has witness `b=ell-1`. -/
theorem aoyagiLemma3A_isLeast_image_Icc_top (ell : ℤ) (hell : 1 ≤ ell) :
    IsLeast
      {v : ℤ | ∃ b : ℤ, 0 ≤ b ∧ b ≤ ell - 1 ∧ aoyagiLemma3A ell ell b = v}
      0 := by
  simpa using aoyagiLemma3A_isLeast_image_Icc ell ell hell (by omega) (by omega)

end Aoyagi
end DLN
end DLNFibre
