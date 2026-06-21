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

/-- Counted data for Aoyagi Lemma 5's interval upper-bound codomain.

The `none` datum is the base datum standing for the supplied base branch.  A
nonbase datum `some ⟨j,H⟩` records an interior coordinate and a
same-coordinate interval value. -/
abbrev AoyagiLemma5CountDatum : Type :=
  Option (Σ _ : ℕ, ℤ)

/-- The nonbase counted data at one coordinate: interval values with the
supplied base value erased, tagged by their coordinate. -/
def aoyagiLemma5CountDatumNonbaseSet (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (baseValue : ℕ → ℤ) (j : ℕ) :
    Finset AoyagiLemma5CountDatum :=
  ((aoyagiHtildeIntervalValueSetNat ell a M m j).erase (baseValue j)).image
    (fun H : ℤ ↦ some (Sigma.mk j H))

/-- The counted datum set: one base datum plus all tagged nonbase interval
values over the interior coordinates. -/
def aoyagiLemma5CountDatumSet (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (baseValue : ℕ → ℤ) :
    Finset AoyagiLemma5CountDatum :=
  insert none
    ((Finset.Icc 1 (ell - 1)).biUnion
      (aoyagiLemma5CountDatumNonbaseSet ell a M m baseValue))

/-- The base datum belongs to the counted datum set. -/
theorem none_mem_aoyagiLemma5CountDatumSet (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (baseValue : ℕ → ℤ) :
    none ∈ aoyagiLemma5CountDatumSet ell a M m baseValue := by
  simp [aoyagiLemma5CountDatumSet]

/-- Membership for a nonbase counted datum. -/
theorem some_mem_aoyagiLemma5CountDatumSet_iff
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (baseValue : ℕ → ℤ) {j : ℕ} {H : ℤ} :
    some (Sigma.mk j H) ∈ aoyagiLemma5CountDatumSet ell a M m baseValue ↔
      j ∈ Finset.Icc 1 (ell - 1) ∧
        H ∈ (aoyagiHtildeIntervalValueSetNat ell a M m j).erase
          (baseValue j) := by
  constructor
  · intro h
    rw [aoyagiLemma5CountDatumSet, Finset.mem_insert] at h
    rcases h with hnone | hmem
    · cases hnone
    · rw [Finset.mem_biUnion] at hmem
      rcases hmem with ⟨j', hj', himage⟩
      rw [aoyagiLemma5CountDatumNonbaseSet, Finset.mem_image] at himage
      rcases himage with ⟨H', hH', hsome⟩
      cases hsome
      exact ⟨hj', hH'⟩
  · rintro ⟨hj, hH⟩
    rw [aoyagiLemma5CountDatumSet, Finset.mem_insert]
    right
    rw [Finset.mem_biUnion]
    exact ⟨j, hj, Finset.mem_image.mpr ⟨H, hH, rfl⟩⟩

/-- One coordinate of nonbase counted data has interval cardinality minus the
supplied base value. -/
theorem aoyagiLemma5CountDatumNonbaseSet_card
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (baseValue : ℕ → ℤ) {j : ℕ}
    (hbase :
      baseValue j ∈ aoyagiHtildeIntervalValueSetNat ell a M m j) :
    (aoyagiLemma5CountDatumNonbaseSet ell a M m baseValue j).card =
      (aoyagiHtildeIntervalValueSetNat ell a M m j).card - 1 := by
  have himage_card :
      (aoyagiLemma5CountDatumNonbaseSet ell a M m baseValue j).card =
        ((aoyagiHtildeIntervalValueSetNat ell a M m j).erase
          (baseValue j)).card := by
    unfold aoyagiLemma5CountDatumNonbaseSet
    rw [Finset.card_image_of_injOn]
    intro H _ H' _ h
    cases h
    rfl
  rw [himage_card]
  exact Finset.card_erase_of_mem hbase

/-- The counted datum set has Aoyagi's Lemma 5 upper-bound cardinality.

This is only the cardinality of the counted-data codomain.  It does not prove
that source lambda-vectors map into it, nor any branch-label or terminal-label
exactness statement. -/
theorem aoyagiLemma5CountDatumSet_card
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (baseValue : ℕ → ℤ)
    (hell : 1 ≤ ell) (ha : a ≤ ell)
    (hbase :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) →
        baseValue j ∈ aoyagiHtildeIntervalValueSetNat ell a M m j) :
    (aoyagiLemma5CountDatumSet ell a M m baseValue).card =
      a * (ell - a) + 1 := by
  have hnone_not :
      none ∉
        ((Finset.Icc 1 (ell - 1)).biUnion
          (aoyagiLemma5CountDatumNonbaseSet ell a M m baseValue)) := by
    rw [Finset.mem_biUnion]
    rintro ⟨j, _hj, hmem⟩
    rw [aoyagiLemma5CountDatumNonbaseSet, Finset.mem_image] at hmem
    rcases hmem with ⟨H, _hH, hsome⟩
    cases hsome
  have hpair :
      ((Finset.Icc 1 (ell - 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
        (aoyagiLemma5CountDatumNonbaseSet ell a M m baseValue) := by
    intro i _hi j _hj hij
    exact Finset.disjoint_left.mpr (by
      intro x hxi hxj
      rw [aoyagiLemma5CountDatumNonbaseSet, Finset.mem_image] at hxi hxj
      rcases hxi with ⟨Hi, _hHi, rfl⟩
      rcases hxj with ⟨Hj, _hHj, hsome⟩
      cases hsome
      exact (hij rfl).elim)
  have hsum :
      (∑ j ∈ Finset.Icc 1 (ell - 1),
          (aoyagiLemma5CountDatumNonbaseSet ell a M m baseValue j).card) =
        ∑ j ∈ Finset.Icc 1 (ell - 1),
          ((aoyagiHtildeIntervalValueSetNat ell a M m j).card - 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact aoyagiLemma5CountDatumNonbaseSet_card ell a M m baseValue
      (hbase hj)
  rw [aoyagiLemma5CountDatumSet, Finset.card_insert_of_notMem hnone_not]
  rw [Finset.card_biUnion hpair]
  rw [hsum]
  have hcount := aoyagiHtildeIntervalValueSetNat_excess_sum_Icc
    ell a M m hell ha
  omega

/-- Supplied classifier from an abstract finite source-candidate set into the
counted interval datum set.

This is the source-facing upper-bound boundary: it packages interval
membership and nonduplication as supplied data, without constructing them from
Aoyagi's printed Lemma 5 paragraph. -/
structure AoyagiLemma5CountDatumClassifier (α : Type*) [DecidableEq α]
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (baseValue : ℕ → ℤ) (candidates : Finset α) where
  classify : α → AoyagiLemma5CountDatum
  mapsTo :
    ∀ {x : α}, x ∈ candidates →
      classify x ∈ aoyagiLemma5CountDatumSet ell a M m baseValue
  injOn : Set.InjOn classify ↑candidates

namespace AoyagiLemma5CountDatumClassifier

/-- The image of a supplied counted-datum classifier is contained in the
counted datum set. -/
theorem image_subset_countDatumSet {α : Type*} [DecidableEq α]
    {ell a : ℕ} {M : ℤ} {m : Fin (ell + 1) → ℤ}
    {baseValue : ℕ → ℤ} {candidates : Finset α}
    (C : AoyagiLemma5CountDatumClassifier α ell a M m baseValue candidates) :
    candidates.image C.classify ⊆
      aoyagiLemma5CountDatumSet ell a M m baseValue := by
  intro datum hdatum
  rcases Finset.mem_image.mp hdatum with ⟨x, hx, rfl⟩
  exact C.mapsTo hx

/-- A supplied injective classifier into the counted datum set gives the
source-candidate upper count.

This theorem only uses supplied classifier data and the finite counted-datum
codomain count.  It does not construct the classifier from Aoyagi's source. -/
theorem candidates_card_le {α : Type*} [DecidableEq α]
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (baseValue : ℕ → ℤ) (candidates : Finset α)
    (C : AoyagiLemma5CountDatumClassifier α ell a M m baseValue candidates)
    (hell : 1 ≤ ell) (ha : a ≤ ell)
    (hbase :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) →
        baseValue j ∈ aoyagiHtildeIntervalValueSetNat ell a M m j) :
    candidates.card ≤ a * (ell - a) + 1 := by
  calc
    candidates.card = (candidates.image C.classify).card := by
      exact (Finset.card_image_of_injOn (s := candidates) (f := C.classify)
        C.injOn).symm
    _ ≤ (aoyagiLemma5CountDatumSet ell a M m baseValue).card :=
      Finset.card_le_card C.image_subset_countDatumSet
    _ = a * (ell - a) + 1 :=
      aoyagiLemma5CountDatumSet_card ell a M m baseValue hell ha hbase

end AoyagiLemma5CountDatumClassifier

/-- Filtering out elements with value `y` maps to erasing `y` from the image.

This is finite-set bookkeeping for turning full coordinate-value coverage into
coverage with the supplied base value removed. -/
theorem finset_image_filter_value_ne_eq_erase_image
    {β γ : Type*} [DecidableEq γ] (s : Finset β) (f : β → γ) (y : γ) :
    (s.filter fun b ↦ f b ≠ y).image f = (s.image f).erase y := by
  ext z
  constructor
  · intro hz
    rw [Finset.mem_image] at hz
    rcases hz with ⟨b, hb, hfb⟩
    rw [Finset.mem_filter] at hb
    rw [Finset.mem_erase, Finset.mem_image]
    constructor
    · intro hzy
      exact hb.2 (hfb.trans hzy)
    · exact ⟨b, hb.1, hfb⟩
  · intro hz
    rw [Finset.mem_erase] at hz
    rcases hz with ⟨hz_ne, hz_image⟩
    rw [Finset.mem_image] at hz_image
    rcases hz_image with ⟨b, hb, hfb⟩
    rw [Finset.mem_image]
    refine ⟨b, ?_, hfb⟩
    rw [Finset.mem_filter]
    exact ⟨hb, fun hfy ↦ hz_ne (hfb.symm.trans hfy)⟩

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

namespace AoyagiLemma5SuppliedNonbaseFamily

/-- Build a supplied nonbase family from coordinate-wise full value coverage
by filtering out the supplied base value at each coordinate.

This is still supplied-data assembly: it assumes coordinate coverage,
injectivity, base-value membership, and cross-coordinate disjointness. -/
def ofCoordinateValueCoverage {β : Type*} [DecidableEq β]
    {ell a : ℕ} {M : ℤ} {m : Fin (ell + 1) → ℤ}
    (rawBranches : ℕ → Finset β) (value : β → ℤ) (baseValue : ℕ → ℤ)
    (baseValue_mem :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) →
        baseValue j ∈ aoyagiHtildeIntervalValueSetNat ell a M m j)
    (value_image :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) →
        (rawBranches j).image value =
          aoyagiHtildeIntervalValueSetNat ell a M m j)
    (value_injective :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) →
        Set.InjOn value ↑(rawBranches j))
    (branches_pairwiseDisjoint :
      ∀ {i j : ℕ}, i ∈ Finset.Icc 1 (ell - 1) →
        j ∈ Finset.Icc 1 (ell - 1) → i ≠ j →
          Disjoint (rawBranches i) (rawBranches j)) :
    AoyagiLemma5SuppliedNonbaseFamily β ell a M m where
  branches := fun j ↦ (rawBranches j).filter fun b ↦ value b ≠ baseValue j
  value := value
  baseValue := baseValue
  baseValue_mem := baseValue_mem
  value_image := by
    intro j hj
    rw [finset_image_filter_value_ne_eq_erase_image, value_image hj]
  value_injective := by
    intro j hj x hx y hy hxy
    have hx' :
        x ∈ (rawBranches j).filter (fun b ↦ value b ≠ baseValue j) := by
      simpa using hx
    have hy' :
        y ∈ (rawBranches j).filter (fun b ↦ value b ≠ baseValue j) := by
      simpa using hy
    exact value_injective hj (Finset.mem_filter.mp hx').1
      (Finset.mem_filter.mp hy').1 hxy
  branches_pairwiseDisjoint := by
    intro i j hi hj hij
    exact Finset.disjoint_left.mpr (by
      intro b hbi hbj
      rw [Finset.mem_filter] at hbi hbj
      exact Finset.disjoint_left.mp
        (branches_pairwiseDisjoint hi hj hij) hbi.1 hbj.1)
end AoyagiLemma5SuppliedNonbaseFamily

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

namespace AoyagiLemma5SuppliedNonbaseFamily

/-- The full supplied finite branch set: `none` is the supplied base branch,
and `some b` is a supplied nonbase branch. -/
def fullBranches {β : Type*} [DecidableEq β] {ell a : ℕ} {M : ℤ}
    {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedNonbaseFamily β ell a M m) :
    Finset (Option β) :=
  insert none
    ((Finset.Icc 1 (ell - 1)).biUnion fun j ↦ (F.branches j).image some)

/-- The supplied base branch belongs to the full supplied branch set. -/
theorem none_mem_fullBranches {β : Type*} [DecidableEq β] {ell a : ℕ} {M : ℤ}
    {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedNonbaseFamily β ell a M m) :
    none ∈ F.fullBranches := by
  simp [fullBranches]

/-- A supplied nonbase branch belongs to the full supplied branch set after
tagging by `some`. -/
theorem some_mem_fullBranches_of_mem {β : Type*} [DecidableEq β]
    {ell a : ℕ} {M : ℤ} {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedNonbaseFamily β ell a M m)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 (ell - 1)) {b : β}
    (hb : b ∈ F.branches j) :
    some b ∈ F.fullBranches := by
  rw [fullBranches, Finset.mem_insert]
  right
  rw [Finset.mem_biUnion]
  exact ⟨j, hj, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩

/-- Membership of a tagged nonbase branch in the full branch set is exactly
membership in one of the supplied coordinate branch sets. -/
theorem some_mem_fullBranches_iff {β : Type*} [DecidableEq β]
    {ell a : ℕ} {M : ℤ} {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedNonbaseFamily β ell a M m) {b : β} :
    some b ∈ F.fullBranches ↔
      ∃ j ∈ Finset.Icc 1 (ell - 1), b ∈ F.branches j := by
  constructor
  · intro h
    rw [fullBranches, Finset.mem_insert] at h
    rcases h with hnone | hmem
    · cases hnone
    · rw [Finset.mem_biUnion] at hmem
      rcases hmem with ⟨j, hj, himage⟩
      rw [Finset.mem_image] at himage
      rcases himage with ⟨b', hb', hsome⟩
      cases hsome
      exact ⟨j, hj, hb'⟩
  · rintro ⟨j, hj, hb⟩
    exact F.some_mem_fullBranches_of_mem hj hb

/-- The counted datum attached to a full supplied branch once a coordinate
function on nonbase branches is supplied. -/
def countDatumOfBranchCoord {β : Type*} [DecidableEq β]
    {ell a : ℕ} {M : ℤ} {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedNonbaseFamily β ell a M m)
    (branchCoord : β → ℕ) :
    Option β → AoyagiLemma5CountDatum
  | none => none
  | some b => some ((Sigma.mk (branchCoord b) (F.value b)) : Σ _ : ℕ, ℤ)

/-- The counted-datum map is injective on the supplied full branch set once
the supplied coordinate function is correct on each coordinate branch set.

This uses only the supplied branch-coordinate equation and per-coordinate
injectivity of `value`; it does not need cross-coordinate disjointness. -/
theorem countDatumOfBranchCoord_injOn {β : Type*} [DecidableEq β]
    {ell a : ℕ} {M : ℤ} {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedNonbaseFamily β ell a M m)
    (branchCoord : β → ℕ)
    (branchCoord_eq :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
        ∀ {b : β}, b ∈ F.branches j → branchCoord b = j) :
    Set.InjOn (F.countDatumOfBranchCoord branchCoord) ↑F.fullBranches := by
  intro x hx y hy hxy
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some c =>
          simp [countDatumOfBranchCoord] at hxy
  | some b =>
      cases y with
      | none =>
          simp [countDatumOfBranchCoord] at hxy
      | some c =>
          rcases (some_mem_fullBranches_iff F).mp hx with ⟨j, hj, hb⟩
          rcases (some_mem_fullBranches_iff F).mp hy with ⟨k, hk, hc⟩
          have hbcoord : branchCoord b = j := branchCoord_eq hj hb
          have hccoord : branchCoord c = k := branchCoord_eq hk hc
          have hsigma :
              ((Sigma.mk (branchCoord b) (F.value b)) : Σ _ : ℕ, ℤ) =
                ((Sigma.mk (branchCoord c) (F.value c)) : Σ _ : ℕ, ℤ) := by
            simpa [countDatumOfBranchCoord] using Option.some.inj hxy
          have hcoord_pair : branchCoord b = branchCoord c :=
            congrArg Sigma.fst hsigma
          have hvalue : F.value b = F.value c :=
            congrArg Sigma.snd hsigma
          have hjk : j = k := by
            exact hbcoord.symm.trans (hcoord_pair.trans hccoord)
          have hcj : c ∈ F.branches j := by
            simpa [hjk.symm] using hc
          have hbc : b = c := F.value_injective hj hb hcj hvalue
          simp [hbc]

/-- Build a counted-datum classifier from a supplied nonbase family, a supplied
coordinate for every nonbase branch, and supplied injectivity of the tagged
classifier.

This proves only the `mapsTo` part from the supplied family fields.  The
injectivity is kept as a hypothesis because Aoyagi's printed paragraph does
not prove the Case 1(2) nonduplication statement needed to derive it. -/
def countDatumClassifierOfBranchCoord {β : Type*} [DecidableEq β]
    {ell a : ℕ} {M : ℤ} {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedNonbaseFamily β ell a M m)
    (branchCoord : β → ℕ)
    (branchCoord_eq :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
        ∀ {b : β}, b ∈ F.branches j → branchCoord b = j)
    (hinj :
      Set.InjOn (F.countDatumOfBranchCoord branchCoord) ↑F.fullBranches) :
    AoyagiLemma5CountDatumClassifier
      (Option β) ell a M m F.baseValue F.fullBranches where
  classify := F.countDatumOfBranchCoord branchCoord
  mapsTo := by
    intro x hx
    cases x with
    | none =>
        simpa [countDatumOfBranchCoord] using
          none_mem_aoyagiLemma5CountDatumSet ell a M m F.baseValue
    | some b =>
        rcases (some_mem_fullBranches_iff F).mp hx with ⟨j, hj, hb⟩
        have hcoord : branchCoord b = j := branchCoord_eq hj hb
        have hvalue :
            F.value b ∈
              (aoyagiHtildeIntervalValueSetNat ell a M m j).erase
                (F.baseValue j) := by
          rw [← F.value_image hj]
          exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
        change
          some ((Sigma.mk (branchCoord b) (F.value b)) : Σ _ : ℕ, ℤ) ∈
            aoyagiLemma5CountDatumSet ell a M m F.baseValue
        rw [some_mem_aoyagiLemma5CountDatumSet_iff]
        constructor
        · simpa [hcoord] using hj
        · simpa [hcoord] using hvalue
  injOn := hinj

/-- Build the counted-datum classifier from a supplied coordinate map.

The tagged-classifier injectivity is derived from the supplied nonbase-family
fields.  This remains supplied-data assembly: it does not construct those
fields from Aoyagi's printed equations. -/
def countDatumClassifierOfBranchCoord_of_branchCoord_eq {β : Type*} [DecidableEq β]
    {ell a : ℕ} {M : ℤ} {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedNonbaseFamily β ell a M m)
    (branchCoord : β → ℕ)
    (branchCoord_eq :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
        ∀ {b : β}, b ∈ F.branches j → branchCoord b = j) :
    AoyagiLemma5CountDatumClassifier
      (Option β) ell a M m F.baseValue F.fullBranches :=
  F.countDatumClassifierOfBranchCoord branchCoord branchCoord_eq
    (F.countDatumOfBranchCoord_injOn branchCoord branchCoord_eq)

/-- The full supplied branch set has Aoyagi's Lemma 5 count, once the branch
family and its base branch are supplied.

This is still only a supplied-data count.  It does not construct the branch
family from Aoyagi's printed formulas. -/
theorem fullBranches_card {β : Type*} [DecidableEq β] (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ)
    (F : AoyagiLemma5SuppliedNonbaseFamily β ell a M m)
    (hell : 1 ≤ ell) (ha : a ≤ ell) :
    F.fullBranches.card = a * (ell - a) + 1 := by
  have hnone_not :
      none ∉
        ((Finset.Icc 1 (ell - 1)).biUnion
          fun j ↦ (F.branches j).image some) := by
    rw [Finset.mem_biUnion]
    rintro ⟨j, _hj, hmem⟩
    rw [Finset.mem_image] at hmem
    rcases hmem with ⟨b, _hb, hsome⟩
    cases hsome
  have hpair :
      ((Finset.Icc 1 (ell - 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
        (fun j ↦ (F.branches j).image some) := by
    intro i hi j hj hij
    exact Finset.disjoint_left.mpr (by
      intro x hxi hxj
      rw [Finset.mem_image] at hxi hxj
      rcases hxi with ⟨bi, hbi, rfl⟩
      rcases hxj with ⟨bj, hbj, hsome⟩
      cases hsome
      exact Finset.disjoint_left.mp (F.branches_pairwiseDisjoint hi hj hij) hbi hbj)
  have hnonbase :=
    aoyagiLemma5SuppliedNonbaseFamily_count ell a M m F hell ha
  have himage_sum :
      (∑ j ∈ Finset.Icc 1 (ell - 1),
          ((F.branches j).image some).card) =
        ∑ j ∈ Finset.Icc 1 (ell - 1), (F.branches j).card := by
    apply Finset.sum_congr rfl
    intro j _hj
    exact Finset.card_image_of_injective (F.branches j) (Option.some_injective β)
  rw [fullBranches, Finset.card_insert_of_notMem hnone_not]
  rw [Finset.card_biUnion hpair]
  rw [himage_sum]
  omega

end AoyagiLemma5SuppliedNonbaseFamily

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

/-- Supplied admissible full branch family for Aoyagi Lemma 5.

This adds an explicit base branch to the admissible nonbase family.  The base
branch is still supplied data: this structure does not construct it from
Aoyagi's printed formulas. -/
structure AoyagiLemma5SuppliedAdmissibleFamily (β : Type*) [DecidableEq β]
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    extends AoyagiLemma5SuppliedAdmissibleNonbaseFamily β ell a M m where
  baseH : Fin (ell + 1) → ℤ
  baseH0 : baseH 0 = m 0
  base_lower_bound : aoyagiHtildeLowerChain ell a M m ≤ baseH
  base_upper_bound : baseH ≤ aoyagiHtildeUpperChain ell a M m
  base_increment_twoValue :
    ∀ r : Fin ell,
      aoyagiLemma4F ell m baseH r = M - 1 ∨
        aoyagiLemma4F ell m baseH r = M

namespace AoyagiLemma5SuppliedAdmissibleFamily

/-- The full supplied branch set attached to an admissible full family. -/
def fullBranches {β : Type*} [DecidableEq β] {ell a : ℕ} {M : ℤ}
    {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedAdmissibleFamily β ell a M m) :
    Finset (Option β) :=
  F.toAoyagiLemma5SuppliedNonbaseFamily.fullBranches

/-- The `H`-chain attached to a tagged supplied full branch. -/
def fullH {β : Type*} [DecidableEq β] {ell a : ℕ} {M : ℤ}
    {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedAdmissibleFamily β ell a M m) :
    Option β → Fin (ell + 1) → ℤ
  | none => F.baseH
  | some b => F.H b

@[simp] theorem fullH_none {β : Type*} [DecidableEq β] {ell a : ℕ} {M : ℤ}
    {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedAdmissibleFamily β ell a M m) :
    F.fullH none = F.baseH :=
  rfl

@[simp] theorem fullH_some {β : Type*} [DecidableEq β] {ell a : ℕ} {M : ℤ}
    {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedAdmissibleFamily β ell a M m) (b : β) :
    F.fullH (some b) = F.H b :=
  rfl

/-- The full supplied admissible branch set has cardinality
`a * (ell - a) + 1` under the supplied boundary. -/
theorem fullBranches_card {β : Type*} [DecidableEq β] (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ)
    (F : AoyagiLemma5SuppliedAdmissibleFamily β ell a M m)
    (hell : 1 ≤ ell) (ha : a ≤ ell) :
    F.fullBranches.card = a * (ell - a) + 1 := by
  exact AoyagiLemma5SuppliedNonbaseFamily.fullBranches_card ell a M m
    F.toAoyagiLemma5SuppliedNonbaseFamily hell ha

/-- The supplied base branch satisfies Lemma 4's finite two-value count. -/
theorem base_twoValueCount {β : Type*} [DecidableEq β] {ell a : ℕ} {M : ℤ}
    {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedAdmissibleFamily β ell a M m)
    (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a) :
    ((Finset.univ.filter fun r : Fin ell ↦
        aoyagiLemma4F ell m F.baseH r = M).card = a) ∧
      ((Finset.univ.filter fun r : Fin ell ↦
        aoyagiLemma4F ell m F.baseH r = M - 1).card = ell - a) := by
  exact aoyagiLemma4_twoValueCount_of_HtildeChainBounds ell a M m F.baseH
    F.baseH0 ha hselected F.base_lower_bound F.base_upper_bound
    F.base_increment_twoValue

/-- Every tagged supplied full branch satisfies Lemma 4's finite two-value
count.

The theorem dispatches to the supplied base branch fields for `none`, and to
the inherited nonbase branch fields for `some b`.  It does not construct either
kind of branch from Aoyagi's printed formulas. -/
theorem fullBranch_twoValueCount {β : Type*} [DecidableEq β]
    {ell a : ℕ} {M : ℤ} {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedAdmissibleFamily β ell a M m)
    (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    {x : Option β} (hx : x ∈ F.fullBranches) :
    ((Finset.univ.filter fun r : Fin ell ↦
        aoyagiLemma4F ell m (F.fullH x) r = M).card = a) ∧
      ((Finset.univ.filter fun r : Fin ell ↦
        aoyagiLemma4F ell m (F.fullH x) r = M - 1).card = ell - a) := by
  cases x with
  | none =>
      simpa [fullH] using F.base_twoValueCount ha hselected
  | some b =>
      have hx' :
          some b ∈ F.toAoyagiLemma5SuppliedNonbaseFamily.fullBranches := by
        simpa [fullBranches] using hx
      rcases
        (AoyagiLemma5SuppliedNonbaseFamily.some_mem_fullBranches_iff
          F.toAoyagiLemma5SuppliedNonbaseFamily).mp hx'
        with ⟨j, hj, hb⟩
      have h :=
        AoyagiLemma5SuppliedAdmissibleNonbaseFamily.branch_twoValueCount
          F.toAoyagiLemma5SuppliedAdmissibleNonbaseFamily ha hselected hj hb
      simpa [fullH] using h

/-- The full supplied admissible branch family simultaneously has Aoyagi's
Lemma 5 finite count and Lemma 4's finite two-value count on every tagged
branch.

This is a supplied-data certificate wrapper.  It does not construct the
displayed branch family, source labels, terminal exponent vectors, pole order,
normal crossings, or RLCT extraction. -/
theorem fullBranches_card_and_fullBranch_twoValueCount {β : Type*}
    [DecidableEq β] (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (F : AoyagiLemma5SuppliedAdmissibleFamily β ell a M m)
    (hell : 1 ≤ ell) (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a) :
    F.fullBranches.card = a * (ell - a) + 1 ∧
      ∀ {x : Option β}, x ∈ F.fullBranches →
        ((Finset.univ.filter fun r : Fin ell ↦
            aoyagiLemma4F ell m (F.fullH x) r = M).card = a) ∧
          ((Finset.univ.filter fun r : Fin ell ↦
            aoyagiLemma4F ell m (F.fullH x) r = M - 1).card = ell - a) := by
  constructor
  · exact fullBranches_card ell a M m F hell ha
  · intro x hx
    exact F.fullBranch_twoValueCount ha hselected hx

/-- Every tagged branch in a full supplied admissible family attains the
isolated Lemma 3 numerator minimum in the free high-count parameter.

This is the finite Lemma 4-to-Lemma 3 bridge applied branchwise to the supplied
full family.  It does not identify the numerator with a source terminal
exponent, prove `\tilde t=0`, construct source labels, prove chart coverage,
or extract pole order/RLCT data. -/
theorem fullBranch_freeHighCount_lemma3A_eq_min {β : Type*} [DecidableEq β]
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    (F : AoyagiLemma5SuppliedAdmissibleFamily β (n + 1) a M m)
    (ha : a ≤ n + 1)
    (hselected :
      (∑ j : Fin (n + 2), m j) = ((n + 1 : ℕ) : ℤ) * (M - 1) + a)
    {x : Option β} (hx : x ∈ F.fullBranches) :
    aoyagiLemma3A ((n + 1 : ℕ) : ℤ) (a : ℤ)
        ((Finset.univ.filter fun j : Fin n ↦
          aoyagiLemma4F (n + 1) m (F.fullH x) j.castSucc = M).card : ℤ) =
      (a : ℤ) * ((n + 1 : ℕ) : ℤ) *
        (((n + 1 : ℕ) : ℤ) - (a : ℤ)) := by
  have hcount :
      (Finset.univ.filter fun j : Fin (n + 1) ↦
        aoyagiLemma4F (n + 1) m (F.fullH x) j = M).card = a :=
    (F.fullBranch_twoValueCount ha hselected hx).1
  exact aoyagiLemma4_freeHighCount_lemma3A_eq_min_of_totalCount n a M
    (aoyagiLemma4F (n + 1) m (F.fullH x)) hcount

end AoyagiLemma5SuppliedAdmissibleFamily

/-- Supplied nonbase branch family with binary prefix-delta data.

This is a narrower supplied boundary than
`AoyagiLemma5SuppliedAdmissibleNonbaseFamily`: the displayed `Htilde` bounds
and two-value increment obligations are derived from terminal binary prefix
deltas, but the branches, values, terminality, and binary deltas are still
supplied data. -/
structure AoyagiLemma5SuppliedBinaryNonbaseFamily (β : Type*) [DecidableEq β]
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    extends AoyagiLemma5SuppliedNonbaseFamily β ell a M m where
  H : β → Fin (ell + 1) → ℤ
  H0 :
    ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
      ∀ {b : β}, b ∈ branches j → H b 0 = m 0
  Hlast :
    ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
      ∀ {b : β}, b ∈ branches j → H b (Fin.last ell) = 0
  binary_delta :
    ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
      ∀ {b : β}, b ∈ branches j →
        ∀ r : Fin ell,
          aoyagiLemma4IncrementPrefixDelta ell M m (H b) r = 0 ∨
            aoyagiLemma4IncrementPrefixDelta ell M m (H b) r = 1
  value_eq_chain :
    ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
      ∀ {b : β}, b ∈ branches j →
        value b = H b (aoyagiLemma5InteriorCoord ell j hj)

namespace AoyagiLemma5SuppliedBinaryNonbaseFamily

/-- The counted datum attached to a tagged branch in a supplied binary nonbase
family.

The binary fields are not used by this datum; it is the underlying supplied
nonbase-family counted datum. -/
def countDatumOfBranchCoord {β : Type*} [DecidableEq β]
    {ell a : ℕ} {M : ℤ} {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedBinaryNonbaseFamily β ell a M m)
    (branchCoord : β → ℕ) :
    Option β → AoyagiLemma5CountDatum :=
  F.toAoyagiLemma5SuppliedNonbaseFamily.countDatumOfBranchCoord branchCoord

/-- A supplied binary nonbase family gives the counted-datum classifier once a
correct coordinate function on nonbase branches is supplied.

This uses only the underlying supplied nonbase-family fields.  The binary
prefix-delta fields are not needed for this classifier. -/
def countDatumClassifierOfBranchCoord {β : Type*} [DecidableEq β]
    {ell a : ℕ} {M : ℤ} {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedBinaryNonbaseFamily β ell a M m)
    (branchCoord : β → ℕ)
    (branchCoord_eq :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
        ∀ {b : β}, b ∈ F.branches j → branchCoord b = j) :
    AoyagiLemma5CountDatumClassifier
      (Option β) ell a M m F.baseValue
      F.toAoyagiLemma5SuppliedNonbaseFamily.fullBranches := by
  simpa [countDatumOfBranchCoord] using
    (F.toAoyagiLemma5SuppliedNonbaseFamily
      |>.countDatumClassifierOfBranchCoord_of_branchCoord_eq branchCoord
        branchCoord_eq)

/-- Terminal binary prefix deltas convert a supplied binary nonbase family into
the existing admissible nonbase-family boundary. -/
def toAdmissibleNonbaseFamily {β : Type*} [DecidableEq β]
    {ell a : ℕ} {M : ℤ} {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedBinaryNonbaseFamily β ell a M m)
    (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a) :
    AoyagiLemma5SuppliedAdmissibleNonbaseFamily β ell a M m where
  toAoyagiLemma5SuppliedNonbaseFamily := F.toAoyagiLemma5SuppliedNonbaseFamily
  H := F.H
  H0 := F.H0
  lower_bound := by
    intro j hj b hb
    exact (aoyagiHtildeChainBounds_of_terminalH_binaryIncrementPrefixDelta
      ell a M m (F.H b) ha (F.H0 hj hb) (F.Hlast hj hb) hselected
      (F.binary_delta hj hb)).1
  upper_bound := by
    intro j hj b hb
    exact (aoyagiHtildeChainBounds_of_terminalH_binaryIncrementPrefixDelta
      ell a M m (F.H b) ha (F.H0 hj hb) (F.Hlast hj hb) hselected
      (F.binary_delta hj hb)).2
  increment_twoValue := by
    intro j hj b hb
    exact aoyagiLemma4F_twoValue_of_binaryIncrementPrefixDelta
      ell M m (F.H b) (F.binary_delta hj hb)
  value_eq_chain := F.value_eq_chain

end AoyagiLemma5SuppliedBinaryNonbaseFamily

/-- Supplied full branch family with binary prefix-delta data.

This adds a base branch to the binary nonbase family.  The conversion theorem
below derives the existing admissible full-family fields from terminal binary
prefix deltas; it does not construct the source branches or prove that
Aoyagi's displayed vectors satisfy the binary hypotheses. -/
structure AoyagiLemma5SuppliedBinaryFamily (β : Type*) [DecidableEq β]
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    extends AoyagiLemma5SuppliedBinaryNonbaseFamily β ell a M m where
  baseH : Fin (ell + 1) → ℤ
  baseH0 : baseH 0 = m 0
  baseHlast : baseH (Fin.last ell) = 0
  base_binary_delta :
    ∀ r : Fin ell,
      aoyagiLemma4IncrementPrefixDelta ell M m baseH r = 0 ∨
        aoyagiLemma4IncrementPrefixDelta ell M m baseH r = 1

namespace AoyagiLemma5SuppliedBinaryFamily

/-- The full supplied branch set attached to a binary full family. -/
def fullBranches {β : Type*} [DecidableEq β] {ell a : ℕ} {M : ℤ}
    {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedBinaryFamily β ell a M m) :
    Finset (Option β) :=
  F.toAoyagiLemma5SuppliedNonbaseFamily.fullBranches

/-- The `H`-chain attached to a tagged supplied binary full branch. -/
def fullH {β : Type*} [DecidableEq β] {ell a : ℕ} {M : ℤ}
    {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedBinaryFamily β ell a M m) :
    Option β → Fin (ell + 1) → ℤ
  | none => F.baseH
  | some b => F.H b

@[simp] theorem fullH_none {β : Type*} [DecidableEq β] {ell a : ℕ} {M : ℤ}
    {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedBinaryFamily β ell a M m) :
    F.fullH none = F.baseH :=
  rfl

@[simp] theorem fullH_some {β : Type*} [DecidableEq β] {ell a : ℕ} {M : ℤ}
    {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedBinaryFamily β ell a M m) (b : β) :
    F.fullH (some b) = F.H b :=
  rfl

/-- The counted datum attached to a tagged branch in a supplied binary family.

The binary fields are not used by this datum; it is the underlying supplied
nonbase-family counted datum. -/
def countDatumOfBranchCoord {β : Type*} [DecidableEq β]
    {ell a : ℕ} {M : ℤ} {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedBinaryFamily β ell a M m)
    (branchCoord : β → ℕ) :
    Option β → AoyagiLemma5CountDatum :=
  F.toAoyagiLemma5SuppliedBinaryNonbaseFamily.countDatumOfBranchCoord branchCoord

/-- A supplied binary family gives the counted-datum classifier once a correct
coordinate function on nonbase branches is supplied.

This is a convenience wrapper around the binary nonbase-family classifier.  It
does not use the base branch or binary prefix-delta fields. -/
def countDatumClassifierOfBranchCoord {β : Type*} [DecidableEq β]
    {ell a : ℕ} {M : ℤ} {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedBinaryFamily β ell a M m)
    (branchCoord : β → ℕ)
    (branchCoord_eq :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 (ell - 1)) →
        ∀ {b : β}, b ∈ F.branches j → branchCoord b = j) :
    AoyagiLemma5CountDatumClassifier
      (Option β) ell a M m F.baseValue F.fullBranches := by
  simpa [fullBranches, countDatumOfBranchCoord] using
    (F.toAoyagiLemma5SuppliedBinaryNonbaseFamily
      |>.countDatumClassifierOfBranchCoord branchCoord
        branchCoord_eq)

/-- Terminal binary prefix deltas convert a supplied binary full family into
the existing admissible full-family boundary. -/
def toAdmissibleFamily {β : Type*} [DecidableEq β]
    {ell a : ℕ} {M : ℤ} {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedBinaryFamily β ell a M m)
    (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a) :
    AoyagiLemma5SuppliedAdmissibleFamily β ell a M m where
  toAoyagiLemma5SuppliedAdmissibleNonbaseFamily :=
    F.toAoyagiLemma5SuppliedBinaryNonbaseFamily.toAdmissibleNonbaseFamily
      ha hselected
  baseH := F.baseH
  baseH0 := F.baseH0
  base_lower_bound :=
    (aoyagiHtildeChainBounds_of_terminalH_binaryIncrementPrefixDelta
      ell a M m F.baseH ha F.baseH0 F.baseHlast hselected
      F.base_binary_delta).1
  base_upper_bound :=
    (aoyagiHtildeChainBounds_of_terminalH_binaryIncrementPrefixDelta
      ell a M m F.baseH ha F.baseH0 F.baseHlast hselected
      F.base_binary_delta).2
  base_increment_twoValue :=
    aoyagiLemma4F_twoValue_of_binaryIncrementPrefixDelta
      ell M m F.baseH F.base_binary_delta

/-- Binary supplied full families inherit the existing full branch count and
per-branch two-value count after conversion to the admissible boundary. -/
theorem fullBranches_card_and_fullBranch_twoValueCount {β : Type*}
    [DecidableEq β] (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (F : AoyagiLemma5SuppliedBinaryFamily β ell a M m)
    (hell : 1 ≤ ell) (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a) :
    F.fullBranches.card = a * (ell - a) + 1 ∧
      ∀ {x : Option β}, x ∈ F.fullBranches →
        ((Finset.univ.filter fun r : Fin ell ↦
            aoyagiLemma4F ell m (F.fullH x) r = M).card = a) ∧
          ((Finset.univ.filter fun r : Fin ell ↦
            aoyagiLemma4F ell m (F.fullH x) r = M - 1).card = ell - a) := by
  simpa [fullBranches, fullH, AoyagiLemma5SuppliedAdmissibleFamily.fullBranches,
    AoyagiLemma5SuppliedAdmissibleFamily.fullH] using
    AoyagiLemma5SuppliedAdmissibleFamily.fullBranches_card_and_fullBranch_twoValueCount
      ell a M m (F.toAdmissibleFamily ha hselected) hell ha hselected

end AoyagiLemma5SuppliedBinaryFamily

end Aoyagi
end DLN
end DLNFibre
