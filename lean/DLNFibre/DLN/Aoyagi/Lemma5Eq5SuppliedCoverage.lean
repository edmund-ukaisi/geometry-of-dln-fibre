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

The lower endpoint is included exactly in the rising region
`j <= a` and `j <= ell-a`. -/
def aoyagiLemma5Eq5EndpointRawBranches
    {β : Type*} [DecidableEq β] (ell a : ℕ)
    (strictBranches : ℕ → Finset β) (upper lower : ℕ → β) (j : ℕ) :
    Finset β :=
  if j ≤ a ∧ j ≤ ell - a then
    insert (upper j) (insert (lower j) (strictBranches j))
  else
    insert (upper j) (strictBranches j)

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

end AoyagiLemma5SuppliedNonbaseFamily

end Aoyagi
end DLN
end DLNFibre
