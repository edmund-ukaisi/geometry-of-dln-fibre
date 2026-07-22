import Mathlib.Order.Height
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# `Core.Aoyagi.OrderChain` — Aoyagi Lemmas 4–5: the binding-minimiser poset is chain-height a(ℓ−a)+1

**PROVED sorry-free (UPPER + ATTAINMENT); the statement awaits the elder's six-check pass.**

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
    (BoxPart ℓ a).chainHeight (· < ·) ≤ ((a * (ℓ - a) + 1 : ℕ) : ℕ∞) := by
  rw [Set.chainHeight_eq_iSup]
  refine iSup_le ?_
  rintro ⟨t, htsub, htchain⟩
  have hinj : Set.InjOn (rankBP a) t := by
    intro x hx y hy hxy
    by_contra hne
    rcases htchain hx hy hne with h | h
    · exact absurd hxy (ne_of_lt (rankBP_strictMono h))
    · exact absurd hxy.symm (ne_of_lt (rankBP_strictMono h))
  have hsub : rankBP a '' t ⊆ ↑(Finset.range (a * (ℓ - a) + 1)) := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [Finset.coe_range, Set.mem_Iio]
    have := rankBP_le (htsub hx)
    omega
  calc t.encard = (rankBP a '' t).encard := (hinj.encard_image).symm
    _ ≤ (↑(Finset.range (a * (ℓ - a) + 1)) : Set ℕ).encard := Set.encard_mono hsub
    _ = ((a * (ℓ - a) + 1 : ℕ) : ℕ∞) := by
        rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_range]

/-- The row-major **staircase** partition after `k` cells: row `i` holds `min K (k − i·K)` cells
(`K = ℓ−a`). Antitone, bounded by `K`, with `∑ = min(k, a·K)`. -/
def staircase (K : ℕ) (a : ℕ) (k : ℕ) : Fin a → ℕ := fun i => min K (k - (i : ℕ) * K)

/-- The row-major fill sum: `∑ min K (k − i·K) = k` when `k ≤ a·K` (`K` fixed, induct on rows `a`). -/
theorem sum_staircase (K : ℕ) : ∀ (a k : ℕ), k ≤ a * K →
    ∑ i : Fin a, min K (k - (i : ℕ) * K) = k := by
  intro a
  induction a with
  | zero => intro k hk; rw [Nat.zero_mul, Nat.le_zero] at hk; subst hk; simp
  | succ n ih =>
    intro k hk
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.zero_mul, Nat.sub_zero, Fin.val_succ]
    have hcast : ∀ i : Fin n, k - ((i : ℕ) + 1) * K = (k - K) - (i : ℕ) * K := by
      intro i; rw [Nat.add_mul, Nat.one_mul]; omega
    rw [Finset.sum_congr rfl (fun i _ => by rw [hcast i])]
    by_cases hKk : K ≤ k
    · rw [min_eq_left hKk, ih (k - K) (by rw [Nat.succ_mul] at hk; omega)]; omega
    · rw [not_le] at hKk
      rw [min_eq_right (le_of_lt hKk)]
      have hk0 : k - K = 0 := by omega
      rw [hk0]
      have hz : ∑ i : Fin n, min K (0 - (i : ℕ) * K) = 0 := by
        apply Finset.sum_eq_zero; intro i _; simp
      omega

/-- The staircase lies in `BoxPart`: antitone and bounded by `ℓ−a`. -/
theorem staircase_mem (ℓ a k : ℕ) : staircase (ℓ - a) a k ∈ BoxPart ℓ a := by
  refine ⟨fun i => min_le_left _ _, ?_⟩
  intro i j hij
  exact min_le_min le_rfl (Nat.sub_le_sub_left (Nat.mul_le_mul_right _ (by exact_mod_cast hij)) k)

/-- `rankBP` of the staircase is `k` (for `k ≤ a(ℓ−a)`), so distinct `k` give distinct partitions. -/
theorem rankBP_staircase (ℓ a k : ℕ) (hk : k ≤ a * (ℓ - a)) :
    rankBP a (staircase (ℓ - a) a k) = k := sum_staircase (ℓ - a) a k hk

/-- **ATTAINMENT** (Lemma 5 construction, Aoyagi eq-(1)/(2)): the staircase realises a chain of
`a(ℓ−a)+1` box partitions, so the chain height is at least `a(ℓ−a)+1` (unconditional). -/
theorem le_chainHeight_boxPart (ℓ a : ℕ) :
    ((a * (ℓ - a) + 1 : ℕ) : ℕ∞) ≤ (BoxPart ℓ a).chainHeight (· < ·) := by
  -- staircase is strictly monotone in `k` (via `rankBP`), so its image over `Iic (a(ℓ−a))` is a
  -- chain in `BoxPart` of size `a(ℓ−a)+1`.
  have hmono : ∀ {k k' : ℕ}, k ≤ a * (ℓ - a) → k' ≤ a * (ℓ - a) → k < k' →
      staircase (ℓ - a) a k < staircase (ℓ - a) a k' := by
    intro k k' hk hk' hlt
    refine lt_of_le_of_ne
      (Pi.le_def.mpr (fun i => min_le_min le_rfl
        (Nat.sub_le_sub_right (le_of_lt hlt) ((i : ℕ) * (ℓ - a))))) ?_
    intro heq
    have hr := rankBP_staircase ℓ a k hk
    rw [heq, rankBP_staircase ℓ a k' hk'] at hr
    omega
  set C : Set (Fin a → ℕ) := (staircase (ℓ - a) a) '' ↑(Finset.Iic (a * (ℓ - a))) with hC
  have hCsub : C ⊆ BoxPart ℓ a := by
    rintro _ ⟨k, _, rfl⟩; exact staircase_mem ℓ a k
  have hInj : Set.InjOn (staircase (ℓ - a) a) ↑(Finset.Iic (a * (ℓ - a))) := by
    intro k hk k' hk' heq
    simp only [Finset.coe_Iic, Set.mem_Iic] at hk hk'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd heq (ne_of_lt (hmono hk hk' h))
    · exact absurd heq.symm (ne_of_lt (hmono hk' hk h))
  have hChain : IsChain (· < ·) C := by
    rintro _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩ hne
    simp only [Finset.coe_Iic, Set.mem_Iic] at hk hk'
    have hkk : k ≠ k' := by rintro rfl; exact hne rfl
    rcases lt_or_gt_of_ne hkk with h | h
    · exact Or.inl (hmono hk hk' h)
    · exact Or.inr (hmono hk' hk h)
  calc ((a * (ℓ - a) + 1 : ℕ) : ℕ∞)
      = (↑(Finset.Iic (a * (ℓ - a))) : Set ℕ).encard := by
        rw [Set.encard_coe_eq_coe_finsetCard]; simp [Nat.card_Iic]
    _ = C.encard := by rw [hC]; exact (hInj.encard_image).symm
    _ ≤ (BoxPart ℓ a).chainHeight (· < ·) :=
        Set.encard_le_chainHeight_of_isChain _ _ hCsub hChain

/-- **Tier-1 headline (P6.2)**: the binding-minimiser box poset has `Set.chainHeight = a(ℓ−a)+1`
(unconditional in `a`). The count is a CHAIN height, not an antichain/cardinality (pnp-confirmed).
Unconditionality reading (elder-blessed): at `a > ℓ` the truncated `ℓ − a = 0` gives the singleton
box and both sides equal `1` — the ℕ-subtraction here is the statement's honest content, NOT the
guard-form trap (the addition-form rule governs GUARDS; identities may carry truncated values). -/
theorem chainHeight_boxPart (ℓ a : ℕ) :
    (BoxPart ℓ a).chainHeight (· < ·) = ((a * (ℓ - a) + 1 : ℕ) : ℕ∞) :=
  le_antisymm (chainHeight_boxPart_le ℓ a) (le_chainHeight_boxPart ℓ a)

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
