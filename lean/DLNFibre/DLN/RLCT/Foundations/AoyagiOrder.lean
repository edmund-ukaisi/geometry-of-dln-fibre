import DLNFibre.DLN.RLCT.Foundations.Lambda
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# `DLNFibre.DLN.RLCT.Foundations.AoyagiOrder` — Aoyagi's order `θ = a(ℓ−a)+1`

Aoyagi (2023)'s **second** deliverable (the value `λ` is the first, in `Foundations.Lambda`): the
order `θ` of the largest pole of the zeta function — geometrically the number of top-dimensional
components of the exceptional fibre over the binding stratum — has the closed form `θ = a(ℓ−a)+1`
(`aoyagi-2023-worked.tex`:727-750; Aoyagi Thm 2 / Lemmas 3-5).

This module builds the **elementary** combinatorial content underlying that closed form, on the
abstract `(ℓ, a)` data, with **no resolution-tree dependence and no analytics**:

* **The Lemma-3 within-set balance and its tie** (`Aval`, `Aval_tie`, `Aval_ge_min`,
  `Aval_eq_min_iff`, `Aval_isLeast`; worked.tex:668-693 / Aoyagi p.24, red-team-verified in
  `verify-repro-s4s5.md` Check 1 = PASS). The one-variable integer quadratic `A(b)` that the
  local-coordinate split minimises has minimum `a·ℓ·(ℓ−a)`, attained at the **two adjacent** ints
  `b = a−1` and `b = a` — the tie whose count is what `θ` records. The master identity is
  `Aval_sub_min : A(b) − a·ℓ·(ℓ−a) = ℓ²·(b−a)·(b−a+1)`, from which the minimum, the tie, and the
  exactly-two-minimisers all follow at once.

* **The `(ℓ, a)` selector arithmetic** (`aoyagiMStar`, `aoyagiSelA`, `aoyagiTheta_symm`):
  `M* = ⌈P/ℓ⌉` and `a = P mod ℓ`, where `P` is the sum of the `ℓ+1` smallest reduced widths
  (design-spec §4.3-4.4). The `ℓ`-selection itself (Aoyagi's Def 3 — the non-total outer
  minimisation that `lambdaCore` deliberately does not transcribe) rides with Def 3 (A2) and stays
  out of this clean layer; the count is stated on abstract `(ℓ, a)`.

## Scope guard — NAMED (precision.md: the name denotes exactly what is proven)

* `aoyagiTheta` (`Foundations.Lambda`) is Aoyagi's RLCT **pole order** — **NOT** `Core.cTheta` /
  `numTop`, LR's number of top-dimensional fibre components. Machine-verified distinct at
  `M = (2,2,2,2,2)`: `aoyagiTheta 4 2 = 5` while `cTheta = C(4,2) = 6` (journal tick 321). No result
  here may be read as `numTop`.
* Equating the combinatorial count `a(ℓ−a)+1` to the **analytic** pole multiplicity needs
  meromorphic continuation (Mathlib-absent); that identity is **out of scope** and no result here
  claims it.

Import direction: `AoyagiOrder → Lambda → Mathlib` (acyclic; `Lambda` does not import this).
-/

namespace DLNFibre.DLN.RLCT

/-! ## Lemma 3: the within-set balance `A(b)` and its adjacent-minimiser tie (Aoyagi p.24) -/

/-- Aoyagi's within-set balance quadratic (p.24, verbatim bracket; the printed `A(b)/ℓ²` has `ℓ²`
dividing both sides, so `A(b)` is this bracket). Here `b ∈ {0,…,ℓ−1}` is the integer split parameter
of the local-coordinate construction; over `ℤ` since the cross term is signed. -/
def Aval (ℓ a b : ℤ) : ℤ :=
  b * (ℓ - a) ^ 2 + (ℓ - 1 - b) * a ^ 2 + (b * (ℓ - a) - (ℓ - 1 - b) * a) ^ 2

/-- The expanded form `A(b) = ℓ²b² + ℓ²(1−2a)b + a²ℓ(ℓ−1)` (p.24). -/
theorem Aval_expand (ℓ a b : ℤ) :
    Aval ℓ a b = ℓ ^ 2 * b ^ 2 + ℓ ^ 2 * (1 - 2 * a) * b + a ^ 2 * ℓ * (ℓ - 1) := by
  unfold Aval; ring

/-- `A(a) = a·ℓ·(ℓ−a)` (p.24). -/
theorem Aval_at_a (ℓ a : ℤ) : Aval ℓ a a = a * ℓ * (ℓ - a) := by
  unfold Aval; ring

/-- `A(a−1) = a·ℓ·(ℓ−a)` (p.24). Note `a−1 ∈ {0,…,ℓ−1}` needs `a ≥ 1` (Aoyagi's `a=0` fnote: the
lone admissible `b=0` still gives `0 = a·ℓ·(ℓ−a)|_{a=0}`). -/
theorem Aval_at_a_pred (ℓ a : ℤ) : Aval ℓ a (a - 1) = a * ℓ * (ℓ - a) := by
  unfold Aval; ring

/-- **The Lemma-3 tie**: `A(a−1) = A(a)` (the two integer neighbours of the real minimiser `b = a−½`
tie for the minimum; worked.tex:683-684). This adjacency is exactly what the order `θ` counts. -/
theorem Aval_tie (ℓ a : ℤ) : Aval ℓ a (a - 1) = Aval ℓ a a := by
  rw [Aval_at_a_pred, Aval_at_a]

/-- **The master identity**: `A(b) − a·ℓ·(ℓ−a) = ℓ²·(b−a)·(b−a+1)`. The right side is `ℓ²` times a
product of two consecutive integers, hence `≥ 0` and `= 0` iff `b ∈ {a−1, a}` — giving the minimum,
the tie, and the exactly-two-minimisers together. -/
theorem Aval_sub_min (ℓ a b : ℤ) :
    Aval ℓ a b - a * ℓ * (ℓ - a) = ℓ ^ 2 * (b - a) * (b - a + 1) := by
  unfold Aval; ring

/-- A product of two consecutive integers is nonnegative. -/
private theorem consec_nonneg (k : ℤ) : 0 ≤ k * (k + 1) := by
  rcases (by omega : 0 ≤ k ∨ k + 1 ≤ 0) with h | h
  · exact mul_nonneg h (by omega)
  · have h1 : (0 : ℤ) ≤ -k := by omega
    have h2 : (0 : ℤ) ≤ -(k + 1) := by omega
    linarith [neg_mul_neg k (k + 1), mul_nonneg h1 h2]

private theorem sq_mul_consec_nonneg (ℓ k : ℤ) : 0 ≤ ℓ ^ 2 * k * (k + 1) := by
  have h := mul_nonneg (sq_nonneg ℓ) (consec_nonneg k)
  linarith [mul_assoc (ℓ ^ 2) k (k + 1), h]

/-- **Lemma 3, the minimum**: `a·ℓ·(ℓ−a) ≤ A(b)` for every integer `b` (no hypothesis on `ℓ, a, b`).
So `A(a) = A(a−1) = a·ℓ·(ℓ−a)` is the minimum value (`Aval_at_a`, `Aval_at_a_pred`). -/
theorem Aval_ge_min (ℓ a b : ℤ) : a * ℓ * (ℓ - a) ≤ Aval ℓ a b := by
  have h := Aval_sub_min ℓ a b
  linarith [sq_mul_consec_nonneg ℓ (b - a), h]

/-- **The tie is exactly the two neighbours**: for `ℓ ≠ 0`, `A(b)` attains its minimum `a·ℓ·(ℓ−a)`
**iff** `b = a−1` or `b = a`. (At `ℓ = 0` the quadratic is constantly `0`.) -/
theorem Aval_eq_min_iff (ℓ a b : ℤ) (hℓ : ℓ ≠ 0) :
    Aval ℓ a b = a * ℓ * (ℓ - a) ↔ b = a - 1 ∨ b = a := by
  constructor
  · intro h
    have h0 : ℓ ^ 2 * (b - a) * (b - a + 1) = 0 := by
      have hs := Aval_sub_min ℓ a b
      rw [h, sub_self] at hs
      exact hs.symm
    have hℓ2 : ℓ ^ 2 ≠ 0 := pow_ne_zero 2 hℓ
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hℓ2
      · right; linarith
    · left; linarith
  · rintro (h | h)
    · rw [h]; exact Aval_at_a_pred ℓ a
    · rw [h]; exact Aval_at_a ℓ a

/-- **Aoyagi p.24, verbatim**: `min{A(b) | b = 0,…,ℓ−1} = A(a−1) = A(a) = a·ℓ·(ℓ−a)`, packaged as
`IsLeast`: `a·ℓ·(ℓ−a)` is attained on `{0,…,ℓ−1}` (at `b = a`, since `0 ≤ a ≤ ℓ−1`) and is a lower
bound. When `1 ≤ a ≤ ℓ−1` both minimisers `a−1, a` lie in range (the genuine tie); at `a = 0` only
`b = 0 = a` does (single minimiser, per the p.24 fnote). Full `ℤ`-form: `Aval_eq_min_iff`. -/
theorem Aval_isLeast (ℓ a : ℤ) (ha0 : 0 ≤ a) (ha : a ≤ ℓ - 1) :
    IsLeast (Aval ℓ a '' Set.Icc (0 : ℤ) (ℓ - 1)) (a * ℓ * (ℓ - a)) := by
  constructor
  · exact ⟨a, Set.mem_Icc.mpr ⟨ha0, ha⟩, Aval_at_a ℓ a⟩
  · rintro y ⟨b, _, rfl⟩
    exact Aval_ge_min ℓ a b

/-! ## The `(ℓ, a)` selector arithmetic (design-spec §4.3-4.4) -/

/-- `M* = ⌈P/ℓ⌉` (design-spec §4.4; Aoyagi Thm 2), written for `ℓ ≥ 1` as `(P + (ℓ−1)) / ℓ`. `P` is
the sum of the `ℓ+1` smallest reduced widths; the `ℓ`-selection (Aoyagi Def 3) rides with Def 3
(A2) and is not transcribed here. -/
def aoyagiMStar (P ℓ : ℕ) : ℕ := (P + (ℓ - 1)) / ℓ

/-- `a = P mod ℓ` (design-spec §4.3): the number of balanced-split parts equal to `⌈P/ℓ⌉`. -/
def aoyagiSelA (P ℓ : ℕ) : ℕ := P % ℓ

/-- `aoyagiTheta` is invariant under `a ↦ ℓ − a` (for `a ≤ ℓ`): `a(ℓ−a)+1 = (ℓ−a)(ℓ−(ℓ−a))+1`. This
makes `θ` independent of the two `a`-conventions — `a = P mod ℓ` (design-spec §4.3) vs
`a = P − (M*−1)ℓ` (worked.tex:671) — which differ only when `ℓ ∣ P` (giving `0` vs `ℓ`). -/
theorem aoyagiTheta_symm (ℓ a : ℕ) (h : a ≤ ℓ) : aoyagiTheta ℓ a = aoyagiTheta ℓ (ℓ - a) := by
  unfold aoyagiTheta
  have h1 : ℓ - (ℓ - a) = a := by omega
  rw [h1, Nat.mul_comm a (ℓ - a)]

/-- The two `a`-conventions agree on `θ` at `ℓ ∣ P`: `P mod ℓ = 0` while the worked.tex value is
`ℓ`, and `aoyagiTheta ℓ 0 = aoyagiTheta ℓ ℓ = 1`. -/
theorem aoyagiTheta_conv_wellDef (ℓ : ℕ) : aoyagiTheta ℓ 0 = aoyagiTheta ℓ ℓ := by
  rw [aoyagiTheta_symm ℓ 0 (Nat.zero_le ℓ), Nat.sub_zero]

-- Ground-truth cross-checks (worked.tex §2 Example + verify-repro-s4s5 table).
example : aoyagiTheta 2 2 = 1 := by decide
example : aoyagiTheta 2 1 = 2 := by decide
example : aoyagiTheta 3 1 = 3 := by decide
example : aoyagiTheta 4 2 = 5 := by decide

/-! ## The count `θ = a(ℓ−a)+1` as a lattice-box cardinality (Lemma 5, scoped)

Lemma 5 counts the binding branch-vectors pinned between the two partial-sum envelopes
`H̃_j`, `H̃'_j` (worked.tex:733-750). Reduced to the abstract `(ℓ,a)` data, the two envelopes are
`H̃_j ↦ j − a` and `H̃'_j ↦ min(j, ℓ−a)`, and the region between them (over `j = 0,…,ℓ`) is a
parallelogram of base `a` and height `ℓ−a` — `a(ℓ−a)` lattice cells; together with the single
terminal branch this is `θ = a(ℓ−a)+1`. We record the cardinality identity on the equinumerous
`a × (ℓ−a)` box.

SCOPE (post-spine follow-on): identifying this count with Aoyagi's actual resolution
binding-branch multiplicity needs the Case-1(2) `J`-increment (resolution-tree bookkeeping), and
identifying it with the analytic pole order needs meromorphic continuation — both out of scope
here. The name below claims **only** the lattice identity `θ = |a×(ℓ−a) box| + 1`. -/

/-- The `a × (ℓ−a)` lattice box; its cardinality is the area between the reduced two-envelope
family (`= a(ℓ−a)`). -/
def orderBox (ℓ a : ℕ) : Finset (ℕ × ℕ) := Finset.Icc 1 a ×ˢ Finset.Icc 1 (ℓ - a)

/-- The `a × (ℓ−a)` box has `a(ℓ−a)` cells (holds for all `ℓ, a`; at `a > ℓ` both sides are `0`). -/
theorem orderBox_card (ℓ a : ℕ) : (orderBox ℓ a).card = a * (ℓ - a) := by
  rw [orderBox, Finset.card_product, Nat.card_Icc, Nat.card_Icc, Nat.add_sub_cancel,
    Nat.add_sub_cancel]

/-- **`θ = a(ℓ−a)+1` as a lattice count**: `aoyagiTheta ℓ a` is one more than the number of cells of
the `a × (ℓ−a)` box (the reduced two-envelope band's area). See the section note for what this does
**not** claim (the resolution binding-branch count; the analytic pole order). -/
theorem aoyagiTheta_eq_orderBox_card_succ (ℓ a : ℕ) :
    aoyagiTheta ℓ a = (orderBox ℓ a).card + 1 := by
  rw [aoyagiTheta, orderBox_card]

end DLNFibre.DLN.RLCT
