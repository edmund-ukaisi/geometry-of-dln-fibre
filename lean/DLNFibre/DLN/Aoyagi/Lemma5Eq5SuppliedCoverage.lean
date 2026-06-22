import DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector
import DLNFibre.DLN.Aoyagi.Lemma5SuppliedFamily

/-!
# Eq5 supplied endpoint coverage for Aoyagi's Lemma 5

This file packages strict equation `(5)` alpha branches together with supplied
endpoint branches as the coordinate-wise raw coverage input for the supplied
nonbase-family boundary.  It does not construct branch records, prove
source-label legality, prove injectivity or cross-coordinate disjointness,
construct classifiers, prove pole order, normal crossings, or extract RLCT
data.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- Raw one-coordinate branch set for Eq5 strict alpha branches plus supplied
endpoints.

The lower endpoint is explicitly inserted only in the rising branch
`j <= a` and `j <= ell-a`; no distinctness from the other records is claimed. -/
def aoyagiLemma5Eq5EndpointRawBranches
    {β : Type*} [DecidableEq β] (ell a : ℕ)
    (strictBranches : ℕ → Finset β) (upper lower : ℕ → β) (j : ℕ) :
    Finset β :=
  if j ≤ a ∧ j ≤ ell - a then
    insert (upper j) (insert (lower j) (strictBranches j))
  else
    insert (upper j) (strictBranches j)

/-- The Eq5 endpoint raw branch set inherits a supplied coordinate map from
its strict, upper-endpoint, and rising lower-endpoint component records.

This is finite membership bookkeeping only.  It does not construct branches or
prove that the coordinate map is source-produced, and it does not assert
endpoint distinctness. -/
theorem aoyagiLemma5Eq5EndpointRawBranches_branchCoord_eq
    {β : Type*} [DecidableEq β] (ell a : ℕ)
    (strictBranches : ℕ → Finset β) (upper lower : ℕ → β)
    (branchCoord : β → ℕ) {j : ℕ}
    (hstrict : ∀ b ∈ strictBranches j, branchCoord b = j)
    (hupper : branchCoord (upper j) = j)
    (hlower : j ≤ a → j ≤ ell - a → branchCoord (lower j) = j)
    {b : β}
    (hb : b ∈ aoyagiLemma5Eq5EndpointRawBranches
      ell a strictBranches upper lower j) :
    branchCoord b = j := by
  by_cases hrising : j ≤ a ∧ j ≤ ell - a
  · rw [aoyagiLemma5Eq5EndpointRawBranches, if_pos hrising] at hb
    rw [Finset.mem_insert, Finset.mem_insert] at hb
    rcases hb with hb_upper | hb_lower | hb_strict
    · rw [hb_upper]
      exact hupper
    · rw [hb_lower]
      exact hlower hrising.1 hrising.2
    · exact hstrict b hb_strict
  · rw [aoyagiLemma5Eq5EndpointRawBranches, if_neg hrising] at hb
    rw [Finset.mem_insert] at hb
    rcases hb with hb_upper | hb_strict
    · rw [hb_upper]
      exact hupper
    · exact hstrict b hb_strict

/-- Eq5 strict alpha coverage plus supplied endpoint values gives full
same-coordinate interval coverage for the raw branch set.

This proves only the finite value-image field needed by the supplied-family
constructor.  It does not prove branch construction, source-label legality,
base-value membership, injectivity, or cross-coordinate disjointness. -/
theorem aoyagiLemma5Eq5EndpointRawBranches_value_image_eq_intervalValueSetNat
    {β : Type*} [DecidableEq β]
    {ell a : ℕ} {M : ℤ} {m : Fin (ell + 1) → ℤ}
    (strictBranches : ℕ → Finset β) (alphaOf : β → ℕ)
    (value : β → ℤ) (upper lower : ℕ → β)
    (ha : a ≤ ell) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 (ell - 1))
    (halpha_image :
      (strictBranches j).image alphaOf = aoyagiLemma5Eq5AlphaDomain ell a j)
    (hvalue : ∀ b ∈ strictBranches j,
      value b = aoyagiHtildeUpperNat ell a M m j - (alphaOf b : ℤ))
    (hupper :
      value (upper j) = aoyagiHtildeUpperNat ell a M m j)
    (hlower : j ≤ a → j ≤ ell - a →
      value (lower j) = aoyagiHtildeLowerNat ell a M m j) :
    (aoyagiLemma5Eq5EndpointRawBranches ell a strictBranches upper lower j).image
        value =
      aoyagiHtildeIntervalValueSetNat ell a M m j := by
  have hj_pos : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hj_lt : j < ell + 1 := by
    have hj_le : j ≤ ell - 1 := (Finset.mem_Icc.mp hj).2
    omega
  have hoffsets :
      (strictBranches j).image value =
        aoyagiLemma5Eq5OffsetValueSet ell a j M m :=
    aoyagiLemma5Eq5_alphaIndexedBranch_value_image_eq_offsetValueSet
      ell a j M m (strictBranches j) alphaOf value halpha_image hvalue
  have hupper_mem :
      aoyagiHtildeUpperNat ell a M m j ∈
        aoyagiHtildeIntervalValueSetNat ell a M m j :=
    aoyagiLemma5Eq5_upperEndpoint_mem_intervalValueSetNat_of_lt
      ell a j M m ha hj_lt
  by_cases hrising : j ≤ a ∧ j ≤ ell - a
  · rw [aoyagiLemma5Eq5EndpointRawBranches, if_pos hrising]
    calc
      (insert (upper j) (insert (lower j) (strictBranches j))).image value =
          insert (value (upper j))
            (insert (value (lower j)) ((strictBranches j).image value)) := by
            rw [Finset.image_insert, Finset.image_insert]
      _ =
          insert (aoyagiHtildeUpperNat ell a M m j)
            (insert (aoyagiHtildeLowerNat ell a M m j)
              (aoyagiLemma5Eq5OffsetValueSet ell a j M m)) := by
            rw [hupper, hlower hrising.1 hrising.2, hoffsets]
      _ =
          insert (aoyagiHtildeUpperNat ell a M m j)
            ((aoyagiHtildeIntervalValueSetNat ell a M m j).erase
              (aoyagiHtildeUpperNat ell a M m j)) := by
            rw [aoyagiLemma5Eq5_insertLower_offsets_eq_interval_erase_upper_of_le_min
              ell a j M m ha hj_pos hrising.1 hrising.2]
      _ = aoyagiHtildeIntervalValueSetNat ell a M m j :=
          Finset.insert_erase hupper_mem
  · have hexcess_le :
        aoyagiLemma5IntervalExcess ell a j ≤ j - 1 :=
      aoyagiLemma5IntervalExcess_le_pred_of_not_le_min
        ell a j ha hj_pos hrising
    rw [aoyagiLemma5Eq5EndpointRawBranches, if_neg hrising]
    calc
      (insert (upper j) (strictBranches j)).image value =
          insert (value (upper j)) ((strictBranches j).image value) := by
            rw [Finset.image_insert]
      _ =
          insert (aoyagiHtildeUpperNat ell a M m j)
            (aoyagiLemma5Eq5OffsetValueSet ell a j M m) := by
            rw [hupper, hoffsets]
      _ =
          insert (aoyagiHtildeUpperNat ell a M m j)
            ((aoyagiHtildeIntervalValueSetNat ell a M m j).erase
              (aoyagiHtildeUpperNat ell a M m j)) := by
            rw [aoyagiLemma5Eq5_offsets_eq_interval_erase_upper_of_excess_le_pred
              ell a j M m ha hj_lt hexcess_le]
      _ = aoyagiHtildeIntervalValueSetNat ell a M m j :=
          Finset.insert_erase hupper_mem

namespace AoyagiLemma5SuppliedNonbaseFamily

/-- Build the supplied nonbase family from Eq5 alpha-indexed branches and
supplied endpoint branches.

This wrapper proves the coordinate value-image coverage from Eq5 finite
bookkeeping, while keeping base-value membership, raw-branch injectivity, and
cross-coordinate disjointness as explicit supplied hypotheses. -/
def ofEq5AlphaIndexedEndpointCoverage {β : Type*} [DecidableEq β]
    {ell a : ℕ} {M : ℤ} {m : Fin (ell + 1) → ℤ}
    (strictBranches : ℕ → Finset β) (alphaOf : β → ℕ)
    (value : β → ℤ) (upper lower : ℕ → β) (baseValue : ℕ → ℤ)
    (ha : a ≤ ell)
    (baseValue_mem :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) →
        baseValue j ∈ aoyagiHtildeIntervalValueSetNat ell a M m j)
    (halpha_image :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) →
        (strictBranches j).image alphaOf =
          aoyagiLemma5Eq5AlphaDomain ell a j)
    (hvalue :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
        ∀ b ∈ strictBranches j,
          value b = aoyagiHtildeUpperNat ell a M m j - (alphaOf b : ℤ))
    (hupper :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) →
        value (upper j) = aoyagiHtildeUpperNat ell a M m j)
    (hlower :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) → j ≤ a → j ≤ ell - a →
        value (lower j) = aoyagiHtildeLowerNat ell a M m j)
    (value_injective :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
        Set.InjOn value
          ↑(aoyagiLemma5Eq5EndpointRawBranches
            ell a strictBranches upper lower j))
    (branches_pairwiseDisjoint :
      ∀ {i j : ℕ}, (hi : i ∈ Finset.Icc 1 (ell - 1)) →
        (hj : j ∈ Finset.Icc 1 (ell - 1)) → i ≠ j →
          Disjoint
            (aoyagiLemma5Eq5EndpointRawBranches
              ell a strictBranches upper lower i)
            (aoyagiLemma5Eq5EndpointRawBranches
              ell a strictBranches upper lower j)) :
    AoyagiLemma5SuppliedNonbaseFamily β ell a M m :=
  AoyagiLemma5SuppliedNonbaseFamily.ofCoordinateValueCoverage
    (ell := ell) (a := a) (M := M) (m := m)
    (aoyagiLemma5Eq5EndpointRawBranches ell a strictBranches upper lower)
    value baseValue baseValue_mem
    (by
      intro j hj
      exact
        aoyagiLemma5Eq5EndpointRawBranches_value_image_eq_intervalValueSetNat
          (ell := ell) (a := a) (M := M) (m := m)
          strictBranches alphaOf value upper lower ha hj
          (halpha_image hj) (hvalue hj) (hupper hj) (hlower hj))
    value_injective branches_pairwiseDisjoint

/-- Branch-coordinate correctness for the filtered supplied family constructed
from Eq5 alpha-indexed endpoint coverage.

The base-value filter only removes records, so coordinate correctness follows
from the raw branch-coordinate adapter. -/
theorem ofEq5AlphaIndexedEndpointCoverage_branchCoord_eq
    {β : Type*} [DecidableEq β]
    {ell a : ℕ} {M : ℤ} {m : Fin (ell + 1) → ℤ}
    (strictBranches : ℕ → Finset β) (alphaOf : β → ℕ)
    (value : β → ℤ) (upper lower : ℕ → β) (baseValue : ℕ → ℤ)
    (ha : a ≤ ell)
    (baseValue_mem :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) →
        baseValue j ∈ aoyagiHtildeIntervalValueSetNat ell a M m j)
    (halpha_image :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) →
        (strictBranches j).image alphaOf =
          aoyagiLemma5Eq5AlphaDomain ell a j)
    (hvalue :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
        ∀ b ∈ strictBranches j,
          value b = aoyagiHtildeUpperNat ell a M m j - (alphaOf b : ℤ))
    (hupper :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) →
        value (upper j) = aoyagiHtildeUpperNat ell a M m j)
    (hlower :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) → j ≤ a → j ≤ ell - a →
        value (lower j) = aoyagiHtildeLowerNat ell a M m j)
    (value_injective :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
        Set.InjOn value
          ↑(aoyagiLemma5Eq5EndpointRawBranches
            ell a strictBranches upper lower j))
    (branches_pairwiseDisjoint :
      ∀ {i j : ℕ}, (hi : i ∈ Finset.Icc 1 (ell - 1)) →
        (hj : j ∈ Finset.Icc 1 (ell - 1)) → i ≠ j →
          Disjoint
            (aoyagiLemma5Eq5EndpointRawBranches
              ell a strictBranches upper lower i)
            (aoyagiLemma5Eq5EndpointRawBranches
              ell a strictBranches upper lower j))
    (branchCoord : β → ℕ)
    (hstrictCoord :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
        ∀ b ∈ strictBranches j, branchCoord b = j)
    (hupperCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) →
        branchCoord (upper j) = j)
    (hlowerCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) → j ≤ a → j ≤ ell - a →
        branchCoord (lower j) = j)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 (ell - 1)) {b : β}
    (hb :
      b ∈ (AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage
        (ell := ell) (a := a) (M := M) (m := m)
        strictBranches alphaOf value upper lower baseValue ha baseValue_mem
        halpha_image hvalue hupper hlower value_injective
        branches_pairwiseDisjoint).branches j) :
    branchCoord b = j := by
  have hbfilter :
      b ∈ (aoyagiLemma5Eq5EndpointRawBranches
          ell a strictBranches upper lower j).filter
        (fun b ↦ value b ≠ baseValue j) := by
    simpa [ofEq5AlphaIndexedEndpointCoverage,
      AoyagiLemma5SuppliedNonbaseFamily.ofCoordinateValueCoverage] using hb
  have hbraw :
      b ∈ aoyagiLemma5Eq5EndpointRawBranches
        ell a strictBranches upper lower j :=
    (Finset.mem_filter.mp hbfilter).1
  exact aoyagiLemma5Eq5EndpointRawBranches_branchCoord_eq
    ell a strictBranches upper lower branchCoord
    (hstrictCoord hj) (hupperCoord hj) (hlowerCoord hj) hbraw

end AoyagiLemma5SuppliedNonbaseFamily

end Aoyagi
end DLN
end DLNFibre
