import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# `Core.Aoyagi.OrderCount` — Aoyagi Lemmas 4–5: the banded-interval combinatorics (Tier 1, abstract)

**PROVED sorry-free (Tier-1 body); framing awaiting the elder's ratification pass.** The band-area
arithmetic (`bandWidth_sum`, `bandCount_eq`) and the p.26 fidelity anchor (`perJCard_eq_paper`) are
axiom-clean `[propext, Classical.choice, Quot.sound]`; the honest seams below are NOT asserted.

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
  simp only [perJCard, perJCardPaper, bandWidth]
  split_ifs <;> omega

/-! ## The two partial-sum envelopes (Aoyagi p.25) and width-independence

The envelopes are stated over a **free** partial-sum function `P : ℕ → ℤ` (`P j = ∑_{l=1}^{j+1}
M^{(S_l)}`) and a **free** integer `M` (Aoyagi's `M = M*`). Keeping them free is exactly Tier-1
purity: the width-independence theorem `envHi − envLo = bandWidth` shows `P` and `M` cancel, so the
per-`j` band width — hence the whole count — depends only on `(ℓ, a)`. Tier 2 instantiates `P, M`
with the certified selector objects (and only then is the terminal equality `H̃_ℓ = H̃'_ℓ = 0` a
theorem — it needs the Def-3 consistency `P, M*, a` relations, absent at Tier 1). -/

/-- Aoyagi p.25's **lower envelope** `H̃_j` (two pieces): `P j − jM` for `j ≤ a`, else
`P j − aM − (j−a)(M−1)`. -/
def envLo (P : ℕ → ℤ) (M : ℤ) (a j : ℕ) : ℤ :=
  if j ≤ a then P j - j * M else P j - a * M - (j - a) * (M - 1)

/-- Aoyagi p.25's **upper envelope** `H̃'_j` (two pieces): `P j − j(M−1)` for `j ≤ ℓ−a`, else
`P j − (ℓ−a)(M−1) − (j−ℓ+a)M`. -/
def envHi (P : ℕ → ℤ) (M : ℤ) (ℓ a j : ℕ) : ℤ :=
  if j ≤ ℓ - a then P j - j * (M - 1)
  else P j - (ℓ - a) * (M - 1) - (j - (ℓ - a)) * M

/-- **Width-independence (the deep fact).** For `a ≤ ℓ`, `j ≤ ℓ`, and ANY partial-sum data `P` and
integer `M`, the band width `H̃'_j − H̃_j` equals `bandWidth ℓ a j = min(j, a, ℓ−a, ℓ−j)` — the
shared `P j` and the integer `M` cancel. This is why Aoyagi's order depends only on `(ℓ, a)`. -/
theorem envHi_sub_envLo (P : ℕ → ℤ) (M : ℤ) (ℓ a j : ℕ) (ha : a ≤ ℓ) (hj : j ≤ ℓ) :
    envHi P M ℓ a j - envLo P M a j = (bandWidth ℓ a j : ℤ) := by
  simp only [envLo, envHi]
  by_cases hja : j ≤ a <;> by_cases hjla : j ≤ ℓ - a
  · rw [if_pos hjla, if_pos hja]
    have hbw : bandWidth ℓ a j = j := by simp only [bandWidth]; omega
    rw [hbw]; ring
  · rw [if_neg hjla, if_pos hja]
    have hbw : bandWidth ℓ a j = ℓ - a := by simp only [bandWidth]; omega
    rw [hbw]; push_cast [Nat.cast_sub ha]; ring
  · rw [if_pos hjla, if_neg hja]
    have hbw : bandWidth ℓ a j = a := by simp only [bandWidth]; omega
    rw [hbw]; ring
  · rw [if_neg hjla, if_neg hja]
    have hbw : bandWidth ℓ a j = ℓ - j := by simp only [bandWidth]; omega
    rw [hbw]; push_cast [Nat.cast_sub hj, Nat.cast_sub ha]; ring
private theorem sum_Icc_linear (ℓ m : ℕ) (hm : 2 * m ≤ ℓ) :
    ∑ i ∈ Finset.Icc 1 m, (ℓ + 1 - 2 * i) = m * (ℓ - m) := by
  induction m with
  | zero => simp
  | succ n ih =>
    have hn : 2 * n ≤ ℓ := by omega
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih hn]
    obtain ⟨d, hd⟩ : ∃ d, ℓ = (n + 1) + d := ⟨ℓ - (n + 1), by omega⟩
    subst hd
    have h1 : (n + 1 + d) - n = d + 1 := by omega
    have h2 : (n + 1 + d) + 1 - 2 * (n + 1) = d - n := by omega
    have h3 : (n + 1 + d) - (n + 1) = d := by omega
    rw [h1, h2, h3]
    obtain ⟨e, he⟩ := Nat.le.dest (show n ≤ d by omega)
    subst he
    simp only [Nat.add_sub_cancel_left]
    ring

/-- The **band area** `∑_{j=0}^{ℓ} W_j = a(ℓ−a)` — the width-independent arithmetic core
(Aoyagi p.26), UNCONDITIONAL in `a` (for `a > ℓ` both sides are `0` via `ℕ`-truncation). The
endpoint widths `W_0 = W_ℓ = 0` make the range choice immaterial. Proof: double-count
`W_j = #{i∈[1,m] : i ≤ j ∧ i ≤ ℓ−j}` (with `m = min(a,ℓ−a)`), swap the two sums, and count
`#{j : i ≤ j ≤ ℓ−i} = ℓ+1−2i`, giving `∑_{i=1}^{m}(ℓ+1−2i) = m(ℓ−m) = a(ℓ−a)`. -/
theorem bandWidth_sum (ℓ a : ℕ) :
    ∑ j ∈ Finset.range (ℓ + 1), bandWidth ℓ a j = a * (ℓ - a) := by
  set m := min a (ℓ - a) with hm
  have hmle : 2 * m ≤ ℓ := by omega
  have htarget : a * (ℓ - a) = m * (ℓ - m) := by
    rcases le_total a ℓ with hal | hal
    · rcases le_total a (ℓ - a) with h | h
      · rw [hm, min_eq_left h]
      · rw [hm, min_eq_right h, Nat.sub_sub_self hal]; ring
    · have h0 : ℓ - a = 0 := Nat.sub_eq_zero_of_le hal
      rw [h0, hm, h0]; simp
  rw [htarget, ← sum_Icc_linear ℓ m hmle]
  have hstep : ∀ j ∈ Finset.range (ℓ + 1),
      bandWidth ℓ a j = ∑ i ∈ Finset.Icc 1 m, (if i ≤ j ∧ i ≤ ℓ - j then 1 else 0) := by
    intro j _
    have hfilter : (Finset.Icc 1 m).filter (fun i => i ≤ j ∧ i ≤ ℓ - j)
        = Finset.Icc 1 (bandWidth ℓ a j) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_Icc, bandWidth]; omega
    rw [← Finset.card_filter, hfilter, Nat.card_Icc]; omega
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_Icc] at hi
  have hfilter : (Finset.range (ℓ + 1)).filter (fun j => i ≤ j ∧ i ≤ ℓ - j)
      = Finset.Icc i (ℓ - i) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
  rw [← Finset.card_filter, hfilter, Nat.card_Icc]; omega

/-- The **banded-interval count** `= band area + 1` (the `+1` is the single terminal branch, the
Case-1(2) `J`-increment; Aoyagi p.26). A neutral arithmetic count over abstract `(ℓ, a)` — NOT
claimed equal to the geometric/analytic multiplicity (see the module seam note). -/
def bandCount (ℓ a : ℕ) : ℕ := (∑ j ∈ Finset.range (ℓ + 1), bandWidth ℓ a j) + 1

/-- **Tier-1 headline**: the banded-interval count is `a(ℓ−a)+1` (Aoyagi Lemma 5's value, as pure
banded-interval arithmetic; UNCONDITIONAL in `a`). -/
theorem bandCount_eq (ℓ a : ℕ) : bandCount ℓ a = a * (ℓ - a) + 1 := by
  unfold bandCount; rw [bandWidth_sum ℓ a]

/-! ## Kill-set: build-enforced ground truths (abstract `(ℓ, a)` values) -/

-- These `decide` the DEFINITION directly (independent of `bandCount_eq`): a mis-defined `bandWidth`
-- would fail here, not silently agree with the closed form.
-- Edge corners (elder's Tier-1 kill-set: a = 0 and ℓ = 1 — the Lemma-3 `A(a−1)` domain subtlety).
example : bandCount 1 0 = 1 := by decide
example : bandCount 1 1 = 1 := by decide
example : bandCount 5 0 = 1 := by decide
example : bandCount 5 5 = 1 := by decide
-- The RRR / §2-Example selector values (K1; the (ℓ,a) come from Def-3, bound at Tier 2):
--   (2,2,2)→(ℓ,a)=(2,2)→1; (2,1,2)→(2,1)→2; (2,2,2,2)→(3,2)→3; ThetaOrderDistinction (4,2)→5.
example : bandCount 2 2 = 1 := by decide
example : bandCount 2 1 = 2 := by decide
example : bandCount 3 2 = 3 := by decide
example : bandCount 4 2 = 5 := by decide

end DLNFibre.Core.Aoyagi.OrderCount
