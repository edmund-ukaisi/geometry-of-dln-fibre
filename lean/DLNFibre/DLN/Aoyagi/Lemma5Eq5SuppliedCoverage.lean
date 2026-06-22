import DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector
import DLNFibre.DLN.Aoyagi.Lemma5SuppliedFamily

/-!
# Eq5 supplied endpoint coverage for Aoyagi's Lemma 5

This file packages strict equation `(5)` alpha branches together with supplied
endpoint branches as the coordinate-wise raw coverage input for the supplied
nonbase-family boundary.  It does not construct branch records, prove
source-label legality, or prove the coordinate facts from source.  Raw value
injectivity is derived only from supplied strict alpha injectivity, and
cross-coordinate disjointness is derived only from supplied coordinate facts.
The classifier wrapper constructed here is only for supplied full branches from
the strictest endpoint constructor; this file does not classify source
terminal-minimum labels, prove no-extra coverage, prove pole order, normal
crossings, or extract RLCT data.
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

/-- Raw Eq5 endpoint branch sets at distinct interior coordinates are disjoint
when a supplied coordinate map sends every component record at coordinate `j`
to `j`.

This is finite disjointness bookkeeping only.  It does not prove source
production, endpoint distinctness, or value injectivity. -/
theorem aoyagiLemma5Eq5EndpointRawBranches_pairwiseDisjoint_of_branchCoord_eq
    {β : Type*} [DecidableEq β] (ell a : ℕ)
    (strictBranches : ℕ → Finset β) (upper lower : ℕ → β)
    (branchCoord : β → ℕ)
    (hstrictCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) →
        ∀ b ∈ strictBranches j, branchCoord b = j)
    (hupperCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) →
        branchCoord (upper j) = j)
    (hlowerCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) → j ≤ a → j ≤ ell - a →
      branchCoord (lower j) = j)
    {i j : ℕ} (hi : i ∈ Finset.Icc 1 (ell - 1))
    (hj : j ∈ Finset.Icc 1 (ell - 1)) (hij : i ≠ j) :
    Disjoint
      (aoyagiLemma5Eq5EndpointRawBranches ell a strictBranches upper lower i)
      (aoyagiLemma5Eq5EndpointRawBranches ell a strictBranches upper lower j) := by
  exact Finset.disjoint_left.mpr (by
    intro b hbi hbj
    have hcoord_i : branchCoord b = i :=
      aoyagiLemma5Eq5EndpointRawBranches_branchCoord_eq
        ell a strictBranches upper lower branchCoord
        (hstrictCoord hi) (hupperCoord hi) (hlowerCoord hi) hbi
    have hcoord_j : branchCoord b = j :=
      aoyagiLemma5Eq5EndpointRawBranches_branchCoord_eq
        ell a strictBranches upper lower branchCoord
        (hstrictCoord hj) (hupperCoord hj) (hlowerCoord hj) hbj
    exact hij (hcoord_i.symm.trans hcoord_j))

/-- Raw Eq5 endpoint branch values are injective at one interior coordinate
when strict branch records are injective in their strict alpha parameter.

This is finite endpoint/offset bookkeeping only.  It does not construct the
strict or endpoint branch records, prove source-label legality, or prove that
the supplied alpha map is source-produced. -/
theorem aoyagiLemma5Eq5EndpointRawBranches_value_injective_of_alpha_injective
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
      value (lower j) = aoyagiHtildeLowerNat ell a M m j)
    (halpha_inj : Set.InjOn alphaOf ↑(strictBranches j)) :
    Set.InjOn value
      ↑(aoyagiLemma5Eq5EndpointRawBranches
        ell a strictBranches upper lower j) := by
  intro b hb c hc hbc
  have hj_pos : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hj_lt : j < ell + 1 := by
    have hj_le : j ≤ ell - 1 := (Finset.mem_Icc.mp hj).2
    omega
  have hoffsets :
      (strictBranches j).image value =
        aoyagiLemma5Eq5OffsetValueSet ell a j M m :=
    aoyagiLemma5Eq5_alphaIndexedBranch_value_image_eq_offsetValueSet
      ell a j M m (strictBranches j) alphaOf value halpha_image hvalue
  have hstrict_mem_offset :
      ∀ {x : β}, x ∈ strictBranches j →
        value x ∈ aoyagiLemma5Eq5OffsetValueSet ell a j M m := by
    intro x hx
    rw [← hoffsets]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hstrict_inj :
      ∀ {x y : β}, x ∈ strictBranches j → y ∈ strictBranches j →
        value x = value y → x = y := by
    intro x y hx hy hxy
    have halpha_int : (alphaOf x : ℤ) = (alphaOf y : ℤ) := by
      rw [hvalue x hx, hvalue y hy] at hxy
      linarith
    have halpha_nat : alphaOf x = alphaOf y := by
      exact_mod_cast halpha_int
    exact halpha_inj hx hy halpha_nat
  have hupper_not_strict :
      ∀ {x : β}, x ∈ strictBranches j → value (upper j) ≠ value x := by
    intro x hx hux
    have hupper_mem :
        aoyagiHtildeUpperNat ell a M m j ∈
          aoyagiLemma5Eq5OffsetValueSet ell a j M m := by
      rw [← hupper, hux]
      exact hstrict_mem_offset hx
    exact aoyagiLemma5Eq5_upperEndpoint_not_mem_offsetValueSet
      ell a j M m hupper_mem
  have hstrict_not_upper :
      ∀ {x : β}, x ∈ strictBranches j → value x ≠ value (upper j) := by
    intro x hx hxu
    exact hupper_not_strict hx hxu.symm
  by_cases hrising : j ≤ a ∧ j ≤ ell - a
  · have hlower_not_strict :
        ∀ {x : β}, x ∈ strictBranches j → value (lower j) ≠ value x := by
      intro x hx hlx
      have hlower_mem :
          aoyagiHtildeLowerNat ell a M m j ∈
            aoyagiLemma5Eq5OffsetValueSet ell a j M m := by
        rw [← hlower hrising.1 hrising.2, hlx]
        exact hstrict_mem_offset hx
      exact aoyagiLemma5Eq5_lowerEndpoint_not_mem_offsetValueSet_of_le_min
        ell a j M m ha hrising.1 hrising.2 hlower_mem
    have hstrict_not_lower :
        ∀ {x : β}, x ∈ strictBranches j → value x ≠ value (lower j) := by
      intro x hx hxl
      exact hlower_not_strict hx hxl.symm
    have hupper_ne_lower : value (upper j) ≠ value (lower j) := by
      intro hul
      have hgap := aoyagiHtildeUpper_sub_lower_eq_intervalExcess
        ell a M m ha ⟨j, hj_lt⟩
      have hexcess :
          aoyagiLemma5IntervalExcess ell a j = j :=
        aoyagiLemma5IntervalExcess_eq_self_of_le_min
          ell a j ha hrising.1 hrising.2
      rw [hupper, hlower hrising.1 hrising.2] at hul
      simp [aoyagiHtildeUpperChain, aoyagiHtildeLowerChain, hexcess] at hgap
      omega
    have hlower_ne_upper : value (lower j) ≠ value (upper j) := by
      intro hlu
      exact hupper_ne_lower hlu.symm
    rw [aoyagiLemma5Eq5EndpointRawBranches, if_pos hrising] at hb hc
    simp only [Finset.mem_coe, Finset.mem_insert] at hb hc
    rcases hb with hb_upper | hb_lower | hb_strict
    · subst b
      rcases hc with hc_upper | hc_lower | hc_strict
      · exact hc_upper.symm
      · subst c
        exact (hupper_ne_lower hbc).elim
      · exact (hupper_not_strict hc_strict hbc).elim
    · subst b
      rcases hc with hc_upper | hc_lower | hc_strict
      · subst c
        exact (hlower_ne_upper hbc).elim
      · exact hc_lower.symm
      · exact (hlower_not_strict hc_strict hbc).elim
    · rcases hc with hc_upper | hc_lower | hc_strict
      · subst c
        exact (hstrict_not_upper hb_strict hbc).elim
      · subst c
        exact (hstrict_not_lower hb_strict hbc).elim
      · exact hstrict_inj hb_strict hc_strict hbc
  · rw [aoyagiLemma5Eq5EndpointRawBranches, if_neg hrising] at hb hc
    simp only [Finset.mem_coe, Finset.mem_insert] at hb hc
    rcases hb with hb_upper | hb_strict
    · subst b
      rcases hc with hc_upper | hc_strict
      · exact hc_upper.symm
      · exact (hupper_not_strict hc_strict hbc).elim
    · rcases hc with hc_upper | hc_strict
      · subst c
        exact (hstrict_not_upper hb_strict hbc).elim
      · exact hstrict_inj hb_strict hc_strict hbc

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

/-- Build the supplied nonbase family from Eq5 endpoint coverage, deriving
cross-coordinate raw-branch disjointness from supplied component coordinates.

This wrapper removes only the separate disjointness hypothesis.  Raw value
injectivity, base-value membership, alpha-domain coverage, and endpoint value
equalities remain supplied. -/
def ofEq5AlphaIndexedEndpointCoverage_of_branchCoord {β : Type*} [DecidableEq β]
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
    (branchCoord : β → ℕ)
    (hstrictCoord :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
        ∀ b ∈ strictBranches j, branchCoord b = j)
    (hupperCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) →
        branchCoord (upper j) = j)
    (hlowerCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) → j ≤ a → j ≤ ell - a →
        branchCoord (lower j) = j) :
    AoyagiLemma5SuppliedNonbaseFamily β ell a M m :=
  AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage
    (ell := ell) (a := a) (M := M) (m := m)
    strictBranches alphaOf value upper lower baseValue ha baseValue_mem
    halpha_image hvalue hupper hlower value_injective
    (by
      intro i j hi hj hij
      exact
        aoyagiLemma5Eq5EndpointRawBranches_pairwiseDisjoint_of_branchCoord_eq
          ell a strictBranches upper lower branchCoord
          hstrictCoord hupperCoord hlowerCoord hi hj hij
    )

/-- Build the supplied nonbase family from Eq5 endpoint coverage, deriving
raw value injectivity from strict alpha injectivity and cross-coordinate
raw-branch disjointness from supplied component coordinates.

This wrapper removes only the raw value-injectivity and raw disjointness
hypotheses.  Base-value membership, alpha-domain coverage, endpoint value
equalities, strict alpha injectivity, and component coordinate facts remain
supplied. -/
def ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord
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
    (halpha_inj :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
        Set.InjOn alphaOf ↑(strictBranches j))
    (branchCoord : β → ℕ)
    (hstrictCoord :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
        ∀ b ∈ strictBranches j, branchCoord b = j)
    (hupperCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) →
        branchCoord (upper j) = j)
    (hlowerCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) → j ≤ a → j ≤ ell - a →
        branchCoord (lower j) = j) :
    AoyagiLemma5SuppliedNonbaseFamily β ell a M m :=
  AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_branchCoord
    (ell := ell) (a := a) (M := M) (m := m)
    strictBranches alphaOf value upper lower baseValue ha baseValue_mem
    halpha_image hvalue hupper hlower
    (by
      intro j hj
      exact
        aoyagiLemma5Eq5EndpointRawBranches_value_injective_of_alpha_injective
          (ell := ell) (a := a) (M := M) (m := m)
          strictBranches alphaOf value upper lower ha hj
          (halpha_image hj) (hvalue hj) (hupper hj) (hlower hj)
          (halpha_inj hj))
    branchCoord hstrictCoord hupperCoord hlowerCoord

/-- Branch-coordinate correctness for the stricter Eq5 endpoint constructor
that derives raw value injectivity from strict alpha injectivity and raw
disjointness from component coordinates. -/
theorem ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord_branchCoord_eq
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
    (halpha_inj :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
        Set.InjOn alphaOf ↑(strictBranches j))
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
      b ∈
        (ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord
            (ell := ell) (a := a) (M := M) (m := m)
            strictBranches alphaOf value upper lower baseValue ha
            baseValue_mem halpha_image hvalue hupper hlower halpha_inj
            branchCoord hstrictCoord hupperCoord hlowerCoord).branches j) :
    branchCoord b = j := by
  have hbfilter :
      b ∈ (aoyagiLemma5Eq5EndpointRawBranches
          ell a strictBranches upper lower j).filter
        (fun b ↦ value b ≠ baseValue j) := by
    simpa [ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord,
      ofEq5AlphaIndexedEndpointCoverage_of_branchCoord,
      ofEq5AlphaIndexedEndpointCoverage,
      AoyagiLemma5SuppliedNonbaseFamily.ofCoordinateValueCoverage] using hb
  have hbraw :
      b ∈ aoyagiLemma5Eq5EndpointRawBranches
        ell a strictBranches upper lower j :=
    (Finset.mem_filter.mp hbfilter).1
  exact aoyagiLemma5Eq5EndpointRawBranches_branchCoord_eq
    ell a strictBranches upper lower branchCoord
    (hstrictCoord hj) (hupperCoord hj) (hlowerCoord hj) hbraw

/-- Counted-datum classifier for the supplied full branch set produced by the
stricter Eq5 endpoint constructor.

This is finite supplied-family bookkeeping only.  It does not classify source
terminal-minimum labels or prove no-extra coverage. -/
def countDatumClassifierOfEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord
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
    (halpha_inj :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
        Set.InjOn alphaOf ↑(strictBranches j))
    (branchCoord : β → ℕ)
    (hstrictCoord :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
        ∀ b ∈ strictBranches j, branchCoord b = j)
    (hupperCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) →
        branchCoord (upper j) = j)
    (hlowerCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) → j ≤ a → j ≤ ell - a →
        branchCoord (lower j) = j) :
    AoyagiLemma5CountDatumClassifier
      (Option β) ell a M m baseValue
      (ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord
          (ell := ell) (a := a) (M := M) (m := m)
          strictBranches alphaOf value upper lower baseValue ha
          baseValue_mem halpha_image hvalue hupper hlower halpha_inj
          branchCoord hstrictCoord hupperCoord hlowerCoord).fullBranches :=
  (ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord
      (ell := ell) (a := a) (M := M) (m := m)
      strictBranches alphaOf value upper lower baseValue ha
      baseValue_mem halpha_image hvalue hupper hlower halpha_inj
      branchCoord hstrictCoord hupperCoord hlowerCoord)
    |>.countDatumClassifierOfBranchCoord_of_branchCoord_eq branchCoord
      (by
        intro j hj b hb
        exact
          ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord_branchCoord_eq
              (ell := ell) (a := a) (M := M) (m := m)
              strictBranches alphaOf value upper lower baseValue ha
              baseValue_mem halpha_image hvalue hupper hlower halpha_inj
              branchCoord hstrictCoord hupperCoord hlowerCoord hj hb)

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
