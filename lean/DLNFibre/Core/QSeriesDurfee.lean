import DLNFibre.Core.QSeries
import Mathlib.Tactic.LinearCombination

/-!
# `DLNFibre.Core.QSeriesDurfee` — the `N = 1` Durfee-square identity (M2)

The single classical `q`-series input the PEEL transfer (M3) rests on (pinned in thread 04 to be the
*only* such input): for `a b : ℕ`, over `ℤ⟦X⟧`,

`P a * P b = ∑_{r=0}^{min a b} X^{(a-r)(b-r)} · P (a-r) · P r · P (b-r)`.

`P` is the LANDED inverse-q-Pochhammer of `Core.QSeries`. The proof is Route B (thread 06, exact-verified
to degree 55, Codex-converged): **induction on `b` via the `(1 − X^{b+1})` descent** — both sides, after
multiplying by `1 − X^{b+1}`, drop from level `b+1` to level `b`, and `1 − X^{b+1}` is a non-zero-divisor
in `ℤ⟦X⟧` (constant term `1`), so the inductive step cancels. No coefficient combinatorics, no Gaussian
binomials (Mathlib v4.29 has no usable `q`-series support).

This chunk: the summand/sum definitions, the peel lemma `P_mul_one_sub_succ`, the base case, the LHS
descent `lhs_desc`, and the scalar split `one_sub_pow_split`. The descent of the RHS sum and the inductive
cancellation are the later chunks.
-/

namespace DLNFibre.Core

open PowerSeries Finset

/-- The Durfee summand `T a b r = X^{(a-r)(b-r)} · P (a-r) · P r · P (b-r)`. -/
noncomputable def durfeeTerm (a b r : ℕ) : ℤ⟦X⟧ :=
  (X : ℤ⟦X⟧) ^ ((a - r) * (b - r)) * P (a - r) * P r * P (b - r)

/-- The Durfee right-hand side `D a b = ∑_{r=0}^{min a b} T a b r`. -/
noncomputable def durfeeSum (a b : ℕ) : ℤ⟦X⟧ :=
  ∑ r ∈ Finset.range (min a b + 1), durfeeTerm a b r

/-- **Peel.** `P (s+1) · (1 − X^{s+1}) = P s`: the top geometric factor telescopes away. -/
theorem P_mul_one_sub_succ (s : ℕ) : P (s + 1) * (1 - X ^ (s + 1)) = P s := by
  rw [P_succ, mul_assoc, geomFactor_mul_one_sub (by omega : 1 ≤ s + 1), mul_one]

/-- **Base case** `b = 0`: `P a * P 0 = D a 0` (the sum has the single term `r = 0`, which is `P a`). -/
theorem durfee_base (a : ℕ) : P a * P 0 = durfeeSum a 0 := by
  rw [durfeeSum, Nat.min_zero, Finset.sum_range_one, durfeeTerm]
  simp [P_zero]

/-- **LHS descent.** `(1 − X^{b+1}) · (P a · P (b+1)) = P a · P b`. -/
theorem lhs_desc (a b : ℕ) :
    (1 - X ^ (b + 1)) * (P a * P (b + 1)) = P a * P b := by
  rw [show (1 - X ^ (b + 1)) * (P a * P (b + 1))
        = P a * (P (b + 1) * (1 - X ^ (b + 1))) by ring, P_mul_one_sub_succ]

/-- **Scalar split.** For `r ≤ b+1`, `1 − X^{b+1} = (1 − X^{(b+1)-r}) + X^{(b+1)-r} · (1 − X^r)`. -/
theorem one_sub_pow_split {r b : ℕ} (hr : r ≤ b + 1) :
    (1 : ℤ⟦X⟧) - X ^ (b + 1)
      = (1 - X ^ ((b + 1) - r)) + X ^ ((b + 1) - r) * (1 - X ^ r) := by
  have hm : (b + 1) - r + r = b + 1 := Nat.sub_add_cancel hr
  rw [mul_sub, mul_one, ← pow_add, hm]
  ring

/-- **A-term shrink.** For `r ≤ b`, `(1 − X^{(b+1)-r}) · T a (b+1) r = X^{a-r} · T a b r`: the factor
telescopes `P ((b+1)-r) = P ((b-r)+1)` down to `P (b-r)`. -/
theorem A_term {a b r : ℕ} (hrb : r ≤ b) :
    (1 - X ^ ((b + 1) - r)) * durfeeTerm a (b + 1) r = X ^ (a - r) * durfeeTerm a b r := by
  have hbr : (b + 1) - r = (b - r) + 1 := by omega
  have hexp : (a - r) * ((b - r) + 1) = (a - r) + (a - r) * (b - r) := by ring
  have hP := P_mul_one_sub_succ (b - r)
  rw [durfeeTerm, durfeeTerm, hbr, hexp]
  linear_combination (X ^ (a - r) * X ^ ((a - r) * (b - r)) * P (a - r) * P r) * hP

/-- **A-top boundary.** When `b+1 ≤ a` the `r = b+1` A-term vanishes (`(b+1)-(b+1) = 0`). -/
theorem A_top_zero (a b : ℕ) :
    (1 - X ^ ((b + 1) - (b + 1))) * durfeeTerm a (b + 1) (b + 1) = 0 := by
  simp

/-- **B-bottom boundary.** The `r = 0` B-term carries the factor `1 − X^0 = 0`. -/
theorem B_zero_at_zero (a b : ℕ) :
    X ^ (b + 1) * (1 - X ^ 0) * durfeeTerm a (b + 1) 0 = 0 := by
  simp

/-- **B-missing-top boundary.** When `a ≤ b` the `r = a` term carries `1 − X^{a-a} = 0`. -/
theorem B_missing_top_zero (a b : ℕ) :
    (1 - X ^ (a - a)) * durfeeTerm a b a = 0 := by
  simp

end DLNFibre.Core
