import Mathlib.Order.Height
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# `Core.Aoyagi.OrderChain` — Aoyagi Lemmas 4–5: the binding-minimiser poset is chain-height a(ℓ−a)+1

**SPECIFY skeleton — UPPER/ATTAINMENT `sorry`, awaiting the elder's six-check pass. NOT proved.**

P6.2 (pnp-confirmed): Aoyagi's pole order `ρ` is the max **chain** of the binding-minimiser poset
(NOT antichain — the Dilworth dual), and `= a(ℓ−a)+1`. The poset is the a-subsets of `[ℓ]` ≅
partitions in the `a × (ℓ−a)` box (`BoxPart`), graded by the cell-count rank; `|BoxPart| = C(ℓ,a)`
but its `Set.chainHeight` is `a(ℓ−a)+1` (verified 1018 cores; the [2,2,2,2,2] witness: 6 elements,
chain-height 5). This is **Tier 1** of the E-lane split — the (ℓ,a)-parametrised abstract poset,
`Core`-pure. The tree-realization (each leaf's binding set IS a `BoxPart` chain, via the banked
DivChain b-chain nesting) is **Tier 3**; the θ-name and the `lambdaCore`/properness non-degeneracy
fence are **Tier 2** (θ enters there only, K3).

## The rank and the trap (the render's crux)

The grading is the **cell-count rank** `∑ parts ∈ [0, a(ℓ−a)]`. On `BoxPart` (box coordinates) this
IS the coordinate sum `rankBP` — strict-monotone under the pointwise order and bounded by `a(ℓ−a)` —
so UPPER = "strict-mono rank into `[0,a(ℓ−a)]` ⟹ every chain injects into `a(ℓ−a)+1` values". The
recursive-rank TRAP (coord-sum FAILS as a grading — covers jump: [1,1,2,1], [2,2,4,3]) is a
**PROFILE-encoding artifact**: on the profile lattice coord-sum's range exceeds `a(ℓ−a)`, so the
tight bound needs the cell count. In the `BoxPart` encoding the cell count IS the coordinate sum, so
the trap does not bite Tier 1; it is handled at the Tier-3 profile↔box iso (the two trap cores are
Tier-3 kill-set instances). ATTAINMENT is the explicit staircase chain (Aoyagi's eq-(1)/(2)).

Name discipline (K3): this file's names say **chain-height** — never order/multiplicity/θ.
-/

namespace DLNFibre.Core.Aoyagi.OrderChain

open scoped Finset

/-- Partitions fitting in the `a × (ℓ−a)` box: antitone `Fin a → ℕ` bounded by `ℓ−a` (the Aoyagi
Lemma-4/5 binding-minimiser poset, ≅ a-subsets of `[ℓ]`; (ℓ,a)-parametrised). The order is the
`Pi`-pointwise `≤`. -/
def BoxPart (ℓ a : ℕ) : Set (Fin a → ℕ) := {f | (∀ i, f i ≤ ℓ - a) ∧ Antitone f}

/-- The **cell-count rank** `∑ parts` — on `BoxPart` this is the Young-cell / inversion grading (the
coordinate sum in box coordinates), ranging over `[0, a(ℓ−a)]`. NOT the profile coord-sum (see the
module note on the trap). -/
def rankBP (a : ℕ) (f : Fin a → ℕ) : ℕ := ∑ i, f i

/-- `rankBP` is bounded by `a(ℓ−a)` on the box. -/
theorem rankBP_le {ℓ a : ℕ} {f : Fin a → ℕ} (hf : f ∈ BoxPart ℓ a) :
    rankBP a f ≤ a * (ℓ - a) := by
  calc rankBP a f = ∑ _i : Fin a, f _i := rfl
    _ ≤ ∑ _i : Fin a, (ℓ - a) := Finset.sum_le_sum (fun i _ => hf.1 i)
    _ = a * (ℓ - a) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- `rankBP` is strictly monotone under the pointwise order: `f < g ⟹ ∑ f < ∑ g`. -/
theorem rankBP_strictMono {a : ℕ} {f g : Fin a → ℕ} (h : f < g) : rankBP a f < rankBP a g := by
  obtain ⟨hle, hne⟩ := lt_iff_le_and_ne.mp h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  exact Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, lt_of_le_of_ne (hle i) hi⟩

/-- **UPPER** (Lemma 5 bound): every chain of `BoxPart` has at most `a(ℓ−a)+1` elements — `rankBP`
is a strict-monotone rank into `[0, a(ℓ−a)]`, so a chain injects into `a(ℓ−a)+1` rank values. -/
theorem chainHeight_boxPart_le (ℓ a : ℕ) :
    (BoxPart ℓ a).chainHeight (· < ·) ≤ (a * (ℓ - a) + 1 : ℕ∞) := by
  sorry

/-- **ATTAINMENT** (Lemma 5 construction, Aoyagi eq-(1)/(2)): the staircase realises a chain of
`a(ℓ−a)+1` box partitions, so the chain height is at least `a(ℓ−a)+1` (for `a ≤ ℓ`). -/
theorem le_chainHeight_boxPart (ℓ a : ℕ) (ha : a ≤ ℓ) :
    (a * (ℓ - a) + 1 : ℕ∞) ≤ (BoxPart ℓ a).chainHeight (· < ·) := by
  sorry

/-- **Tier-1 headline (P6.2)**: the binding-minimiser box poset has `Set.chainHeight = a(ℓ−a)+1`
(for `a ≤ ℓ`). The count is a CHAIN height, not an antichain/cardinality (pnp-confirmed). -/
theorem chainHeight_boxPart (ℓ a : ℕ) (ha : a ≤ ℓ) :
    (BoxPart ℓ a).chainHeight (· < ·) = (a * (ℓ - a) + 1 : ℕ∞) :=
  le_antisymm (chainHeight_boxPart_le ℓ a) (le_chainHeight_boxPart ℓ a ha)

/-! ## Kill-set ground truths (the headline's values at the K1 + corner `(ℓ, a)`)
`(2,2,2)→(ℓ,a)=(2,2)→1`; `(2,1,2)→(2,1)→2`; `(2,2,2,2)→(3,2)→3`; ThetaOrderDistinction `(4,2)→5`.
Corners: `a=0 → 1` (empty box); `ℓ=1 → 1`; `L=ℓ` depth boundary. The recursive-rank TRAP cores
[1,1,2,1], [2,2,4,3] are PROFILE widths — Tier-3 kill-set (the profile↔box iso), not Tier-1. -/

-- the closed-form value at each K1/corner (a(ℓ−a)+1, decidable):
example : (2 : ℕ) * (2 - 2) + 1 = 1 := by decide   -- (2,2,2)
example : (1 : ℕ) * (2 - 1) + 1 = 2 := by decide   -- (2,1,2)
example : (2 : ℕ) * (3 - 2) + 1 = 3 := by decide   -- (2,2,2,2)
example : (2 : ℕ) * (4 - 2) + 1 = 5 := by decide   -- (4,2) ThetaOrderDistinction
example : (0 : ℕ) * (5 - 0) + 1 = 1 := by decide   -- a=0 corner
example : (1 : ℕ) * (1 - 1) + 1 = 1 := by decide   -- ℓ=1 corner

end DLNFibre.Core.Aoyagi.OrderChain
