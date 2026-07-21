import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# `Core.Aoyagi.OrderCount` — Aoyagi Lemmas 4–5: the banded-interval combinatorics (Tier 1, abstract)

**SPECIFY skeleton — statements only, `sorry` bodies, awaiting elder ratification. NOT proved.**

Aoyagi (2023) pp.25–26 counts the binding branch-vectors that attain the RLCT by a two-envelope,
two-condition characterisation (Lemma 4) and a two-sided (union upper bound + explicit
lower-bound construction) argument (Lemma 5), concluding the order `θ = a(ℓ−a)+1`.

This module is **Tier 1** of the E-lane three-tier split (elder-ratified 2026-07-21): the
**abstract banded-interval combinatorics** over the pure `(ℓ, a)` parameters — the mathematical
weight, network-free, `Core`-pure (imports Mathlib only; nothing here imports `DLN`). The θ-name,
the certified `(ℓ, a, M*)` selector objects, and the `aoyagiTheta` identity live at **Tier 2**
(a thin DLN binding, not this file); the tree-ledger binding (`FoldProduced`/`leafOf`/`divExp`)
is **Tier 3**, deferred. Per the tier-binding map, **no `θ`/`order`/`multiplicity` name appears
here** — these are neutral counts over abstract naturals.

## The faithful anchor and the honest seam (fidelity findings, seat-E 2026-07-21)

* **`bandWidth ℓ a j = min(j, a, ℓ−a, ℓ−j)`** is the per-`j` band width. Its `+1` is p.26's
  printed three-range interval cardinality `#{H : H̃_j ≤ H ≤ H̃'_j}` — verified equal to the
  image's piecewise form (`perJCard_eq_paper`). Width-independent: the shared partial-sum term
  `∑_{l=1}^{j+1} M^{(S_l)}` and the integer `M = M*` cancel in `H̃'_j − H̃_j` (checked exactly).

* **`bandArea ℓ a = ∑_j bandWidth ℓ a j = a(ℓ−a)`** (`bandWidth_sum`) — the clean arithmetic core.

* **`bandCount ℓ a = bandArea ℓ a + 1 = a(ℓ−a)+1`** (`bandCount_eq`) — band area plus the single
  terminal branch (the Case-1(2) `J`-increment).

* **Honest seam (NOT claimed here).** `bandCount` is the banded-interval *arithmetic*; that it
  equals the paper's true count of RLCT-attaining branch-vectors is Lemma 5's loose two-sided
  argument, and equating THAT count to the analytic zeta-pole multiplicity `ρ` needs meromorphic
  continuation Mathlib lacks. Neither identification is asserted here (both deferred). The naive
  single-count readings are *provably not* the value: the raw per-`j` sum `∑(bandWidth+1)`
  overcounts (`ℓ=4, a=2` → 7 ≠ 5), and the union cardinality `|⋃_j [H̃_j, H̃'_j]|+1` is
  width-dependent (varies over `{4,6,7,8}` at `ℓ=4, a=2`). Only the band-**area** sum is intrinsic.
-/

namespace DLNFibre.Core.Aoyagi.OrderCount

/-- The per-`j` **band width** `W_j = min(j, a, ℓ−a, ℓ−j)` (Aoyagi p.26, the width of the interval
`[H̃_j, H̃'_j]`; `ℕ`-truncated subtraction, used with `a ≤ ℓ`, `j ≤ ℓ`). -/
def bandWidth (ℓ a j : ℕ) : ℕ := min (min j a) (min (ℓ - a) (ℓ - j))

/-- The per-`j` **interval cardinality** `#{H : H̃_j ≤ H ≤ H̃'_j} = W_j + 1` (p.26). -/
def perJCard (ℓ a j : ℕ) : ℕ := bandWidth ℓ a j + 1

/-- Aoyagi p.26's **printed three-range piecewise** per-`j` interval cardinality (verbatim):
`j+1` for `j ≤ min{a,ℓ−a}`; `min{a,ℓ−a}+1` for `min{a,ℓ−a} < j ≤ max{a,ℓ−a}`;
`min{a,ℓ−a}+1+max{a,ℓ−a}−j` for `max{a,ℓ−a} < j ≤ ℓ`. -/
def perJCardPaper (ℓ a j : ℕ) : ℕ :=
  if j ≤ min a (ℓ - a) then j + 1
  else if j ≤ max a (ℓ - a) then min a (ℓ - a) + 1
  else min a (ℓ - a) + 1 + max a (ℓ - a) - j

/-- **Fidelity anchor**: the closed `min`-form cardinality equals p.26's printed three-range
piecewise form (for `a ≤ ℓ`, `j ≤ ℓ`). -/
theorem perJCard_eq_paper (ℓ a j : ℕ) (ha : a ≤ ℓ) (hj : j ≤ ℓ) :
    perJCard ℓ a j = perJCardPaper ℓ a j := by
  sorry

/-- The **band area** `∑_{j=0}^{ℓ} W_j = a(ℓ−a)` — the width-independent arithmetic core
(Aoyagi p.26). The endpoint widths `W_0 = W_ℓ = 0` make the range choice immaterial. -/
theorem bandWidth_sum (ℓ a : ℕ) (ha : a ≤ ℓ) :
    ∑ j ∈ Finset.range (ℓ + 1), bandWidth ℓ a j = a * (ℓ - a) := by
  sorry

/-- The **banded-interval count** `= band area + 1` (the `+1` is the single terminal branch, the
Case-1(2) `J`-increment; Aoyagi p.26). A neutral arithmetic count over abstract `(ℓ, a)` — NOT
claimed equal to the geometric/analytic multiplicity (see the module seam note). -/
def bandCount (ℓ a : ℕ) : ℕ := (∑ j ∈ Finset.range (ℓ + 1), bandWidth ℓ a j) + 1

/-- **Tier-1 headline**: the banded-interval count is `a(ℓ−a)+1` (Aoyagi Lemma 5's value, as pure
banded-interval arithmetic; for `a ≤ ℓ`). -/
theorem bandCount_eq (ℓ a : ℕ) (ha : a ≤ ℓ) : bandCount ℓ a = a * (ℓ - a) + 1 := by
  sorry

/-! ## Kill-set: build-enforced ground truths (abstract `(ℓ, a)` values) -/

-- Edge corners (elder's Tier-1 kill-set: a = 0 and ℓ = 1 — the Lemma-3 `A(a−1)` domain subtlety).
example : bandCount 1 0 = 1 := by sorry
example : bandCount 1 1 = 1 := by sorry
example : bandCount 5 0 = 1 := by sorry
example : bandCount 5 5 = 1 := by sorry
-- The RRR / §2-Example selector values (K1; the (ℓ,a) come from Def-3, bound at Tier 2):
--   (2,2,2)→(ℓ,a)=(2,2)→1; (2,1,2)→(2,1)→2; (2,2,2,2)→(3,2)→3; ThetaOrderDistinction (4,2)→5.
example : bandCount 2 2 = 1 := by sorry
example : bandCount 2 1 = 2 := by sorry
example : bandCount 3 2 = 3 := by sorry
example : bandCount 4 2 = 5 := by sorry

end DLNFibre.Core.Aoyagi.OrderCount
