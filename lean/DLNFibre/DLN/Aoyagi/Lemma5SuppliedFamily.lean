import DLNFibre.DLN.Aoyagi.HtildeChainArithmetic

/-!
# Supplied chart-family boundary for Aoyagi's Lemma 5

This file packages the aggregate finite count available once the missing
Lemma 5 chart-family realisation is supplied as data.  It does not construct
Aoyagi's displayed equations `(3)`, `(4)`, or `(5)`, and it does not prove
chart coverage, pole order, normal crossings, or RLCT extraction.
-/

open scoped BigOperators

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- The `j`th interior selected coordinate, viewed as a member of
`Fin (ell+1)`.

The hypothesis is the source summation range `j=1,...,ell-1` from Lemma 5. -/
def aoyagiLemma5InteriorCoord (ell j : ℕ)
    (hj : j ∈ Finset.Icc 1 (ell - 1)) : Fin (ell + 1) :=
  ⟨j, by
    have hjle : j ≤ ell - 1 := (Finset.mem_Icc.mp hj).2
    omega⟩

/-- Supplied nonbase branch values for Aoyagi Lemma 5.

For each interior coordinate `j`, the branch values are required to biject
onto the same-coordinate interval value set with one supplied base value
removed.  This is an explicit supplied-data boundary: the structure does not
derive coverage or nonduplication from Aoyagi's printed formulas. -/
structure AoyagiLemma5SuppliedNonbaseFamily (β : Type*) [DecidableEq β]
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ) where
  branches : ℕ → Finset β
  value : β → ℤ
  baseValue : ℕ → ℤ
  baseValue_mem :
    ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) →
      baseValue j ∈ aoyagiHtildeIntervalValueSetNat ell a M m j
  value_image :
    ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
      (branches j).image value =
        (aoyagiHtildeIntervalValueSetNat ell a M m j).erase (baseValue j)
  value_injective :
    ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
      Set.InjOn value ↑(branches j)
  branches_pairwiseDisjoint :
    ∀ {i j : ℕ}, (hi : i ∈ Finset.Icc 1 (ell - 1)) →
      (hj : j ∈ Finset.Icc 1 (ell - 1)) → i ≠ j →
        Disjoint (branches i) (branches j)

/-- One supplied nonbase branch family has the expected cardinality at a fixed
interior coordinate: the interval cardinality with one supplied base value
removed. -/
theorem aoyagiLemma5SuppliedNonbaseFamily_branch_card_eq_interval_card_sub_one
    {β : Type*} [DecidableEq β] {ell a : ℕ} {M : ℤ}
    {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedNonbaseFamily β ell a M m)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 (ell - 1)) :
    (F.branches j).card =
      (aoyagiHtildeIntervalValueSetNat ell a M m j).card - 1 := by
  have himage_card :
      ((F.branches j).image F.value).card = (F.branches j).card := by
    exact Finset.card_image_of_injOn (s := F.branches j) (f := F.value)
      (F.value_injective hj)
  have herase_card :
      ((aoyagiHtildeIntervalValueSetNat ell a M m j).erase
          (F.baseValue j)).card =
        (aoyagiHtildeIntervalValueSetNat ell a M m j).card - 1 :=
    Finset.card_erase_of_mem (F.baseValue_mem hj)
  calc
    (F.branches j).card = ((F.branches j).image F.value).card := himage_card.symm
    _ =
        ((aoyagiHtildeIntervalValueSetNat ell a M m j).erase
          (F.baseValue j)).card := by
          rw [F.value_image hj]
    _ = (aoyagiHtildeIntervalValueSetNat ell a M m j).card - 1 := herase_card

/-- Aggregate finite count for a supplied nonbase Lemma 5 branch family.

The theorem uses only the supplied coverage/nonduplication fields and the
already-proved interval arithmetic.  It is not a construction of the displayed
chart family. -/
theorem aoyagiLemma5SuppliedNonbaseFamily_count
    {β : Type*} [DecidableEq β] (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ)
    (F : AoyagiLemma5SuppliedNonbaseFamily β ell a M m)
    (hell : 1 ≤ ell) (ha : a ≤ ell) :
    1 + (∑ j ∈ Finset.Icc 1 (ell - 1), (F.branches j).card) =
      a * (ell - a) + 1 := by
  rw [← aoyagiHtildeIntervalValueSetNat_excess_sum_Icc ell a M m hell ha]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact aoyagiLemma5SuppliedNonbaseFamily_branch_card_eq_interval_card_sub_one F hj

/-- Aggregate finite union count for a supplied nonbase Lemma 5 branch family.

This is the branch-union version of `aoyagiLemma5SuppliedNonbaseFamily_count`,
using the supplied cross-coordinate disjointness field. -/
theorem aoyagiLemma5SuppliedNonbaseFamily_biUnion_count
    {β : Type*} [DecidableEq β] (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ)
    (F : AoyagiLemma5SuppliedNonbaseFamily β ell a M m)
    (hell : 1 ≤ ell) (ha : a ≤ ell) :
    1 + ((Finset.Icc 1 (ell - 1)).biUnion F.branches).card =
      a * (ell - a) + 1 := by
  have hpair :
      ((Finset.Icc 1 (ell - 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
        F.branches := by
    intro i hi j hj hij
    exact F.branches_pairwiseDisjoint hi hj hij
  rw [Finset.card_biUnion hpair]
  exact aoyagiLemma5SuppliedNonbaseFamily_count ell a M m F hell ha

/-- Supplied admissible nonbase branch family for Aoyagi Lemma 5.

This extends the finite coverage data with the Lemma 4 witness obligations for
each supplied nonbase branch.  The fields remain hypotheses; this structure
does not prove that Aoyagi's printed equations satisfy them or supply
admissibility data for the separate base branch counted by the leading `1`. -/
structure AoyagiLemma5SuppliedAdmissibleNonbaseFamily (β : Type*) [DecidableEq β]
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    extends AoyagiLemma5SuppliedNonbaseFamily β ell a M m where
  H : β → Fin (ell + 1) → ℤ
  H0 :
    ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
      ∀ {b : β}, b ∈ branches j → H b 0 = m 0
  lower_bound :
    ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
      ∀ {b : β}, b ∈ branches j → aoyagiHtildeLowerChain ell a M m ≤ H b
  upper_bound :
    ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
      ∀ {b : β}, b ∈ branches j → H b ≤ aoyagiHtildeUpperChain ell a M m
  increment_twoValue :
    ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
      ∀ {b : β}, b ∈ branches j →
        ∀ r : Fin ell,
          aoyagiLemma4F ell m (H b) r = M - 1 ∨
            aoyagiLemma4F ell m (H b) r = M
  value_eq_chain :
    ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
      ∀ {b : β}, b ∈ branches j →
        value b = H b (aoyagiLemma5InteriorCoord ell j hj)

namespace AoyagiLemma5SuppliedAdmissibleNonbaseFamily

/-- Each supplied admissible branch satisfies Lemma 4's finite two-value count.

This is a per-branch consequence of the explicit `H`-chain fields.  The
theorem still does not construct the branches or prove source-label legality. -/
theorem branch_twoValueCount
    {β : Type*} [DecidableEq β] {ell a : ℕ} {M : ℤ}
    {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedAdmissibleNonbaseFamily β ell a M m)
    (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 (ell - 1))
    {b : β} (hb : b ∈ F.branches j) :
    ((Finset.univ.filter fun r : Fin ell ↦
        aoyagiLemma4F ell m (F.H b) r = M).card = a) ∧
      ((Finset.univ.filter fun r : Fin ell ↦
        aoyagiLemma4F ell m (F.H b) r = M - 1).card = ell - a) := by
  exact aoyagiLemma4_twoValueCount_of_HtildeChainBounds ell a M m (F.H b)
    (F.H0 hj hb) ha hselected (F.lower_bound hj hb) (F.upper_bound hj hb)
    (F.increment_twoValue hj hb)

end AoyagiLemma5SuppliedAdmissibleNonbaseFamily

end Aoyagi
end DLN
end DLNFibre
