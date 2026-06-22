import DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector
import DLNFibre.DLN.Aoyagi.Lemma5Eq5EndpointProfile
import DLNFibre.DLN.Aoyagi.Lemma5SourceLabel
import DLNFibre.DLN.Aoyagi.Lemma5SuppliedFamily

/-!
# Eq5 counted-datum bridge for Aoyagi's Lemma 5

This file connects the supplied equation `(5)` nonfirst interval-admissibility
wrappers and terminal-room endpoint-chain binary deltas to the counted-datum
codomain.  It does not construct equation `(5)`, classifiers, injections,
back-to-label maps, pole order, normal crossings, or RLCT extraction.
-/

open scoped BigOperators

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- A nonfirst equation `(5)` block value gives one counted datum under the
strict alpha domain, supplied post-`p` guard, and non-base-value condition. -/
theorem aoyagiLemma5Eq5_nonfirstBlock_countDatumSet_mem_of_alphaDomain_of_postPLowerGuard
    (ell a p alpha : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (halpha : alpha ∈ aoyagiLemma5Eq5AlphaDomain ell a p)
    (hpost : aoyagiLemma5Eq5PostPLowerGuard ell a p alpha)
    {b S : ℕ} (hb_pos : 1 ≤ b) (hS : C.block b S)
    (hne_base : T S ≠ baseValue b) :
    some (Sigma.mk b (T S)) ∈
      aoyagiLemma5CountDatumSet ell a M m baseValue := by
  have hb_lt_ell : b < ell := hS.1
  have hbIcc : b ∈ Finset.Icc 1 (ell - 1) := by
    rw [Finset.mem_Icc]
    exact ⟨hb_pos, by omega⟩
  have hmem :
      T S ∈ aoyagiHtildeIntervalValueSetNat ell a M m b :=
    aoyagiLemma5Eq5_nonfirstBlock_mem_intervalValueSetNat_of_alphaDomain_of_postPLowerGuard
      ell a p alpha M m C layerWidth T hT halpha hpost hb_pos hS
  exact aoyagiLemma5CountDatumSet_mem_of_intervalValueSetNat
    ell a M m baseValue hbIcc hmem hne_base

/-- A nonfirst equation `(5)` block value gives one counted datum under the
strict alpha domain, terminal-room guard, and non-base-value condition. -/
theorem aoyagiLemma5Eq5_nonfirstBlock_countDatumSet_mem_of_alphaDomain_of_terminalRoom
    (ell a p alpha : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (halpha : alpha ∈ aoyagiLemma5Eq5AlphaDomain ell a p)
    (hroom : p + 2 * a - alpha ≤ ell)
    {b S : ℕ} (hb_pos : 1 ≤ b) (hS : C.block b S)
    (hne_base : T S ≠ baseValue b) :
    some (Sigma.mk b (T S)) ∈
      aoyagiLemma5CountDatumSet ell a M m baseValue := by
  have hb_lt_ell : b < ell := hS.1
  have hmem :
      T S ∈ aoyagiHtildeIntervalValueSetNat ell a M m b :=
    aoyagiLemma5Eq5_nonfirstBlock_mem_intervalValueSetNat_of_alphaDomain_of_terminalRoom
      ell a p alpha M m C layerWidth T hT halpha hroom hb_pos hS
  have hbIcc : b ∈ Finset.Icc 1 (ell - 1) := by
    rw [Finset.mem_Icc]
    exact ⟨hb_pos, by omega⟩
  exact aoyagiLemma5CountDatumSet_mem_of_intervalValueSetNat
    ell a M m baseValue hbIcc hmem hne_base

/-- A supplied equation `(5)` terminal-room endpoint chain gives one counted
datum at any interior selected coordinate, provided the chain value is not the
supplied base value. -/
theorem aoyagiLemma5Eq5_endpointChain_countDatumSet_mem_of_terminalRoom
    (ell a p alpha : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (hroom : p + 2 * a - alpha ≤ ell)
    (hH0 : H 0 = m 0)
    (hHlast : H (Fin.last ell) = 0)
    (hselected :
      (∑ i : Fin (ell + 1), m i) = (ell : ℤ) * (M - 1) + a)
    (hH_endpoint :
      ∀ b : Fin (ell + 1), 1 ≤ b.val → b.val < ell →
        H b = T (C.point b.val - 1))
    {j : ℕ} (hj : j ∈ Finset.Icc 1 (ell - 1))
    (hne_base :
      H (aoyagiLemma5InteriorCoord ell j hj) ≠ baseValue j) :
    some (Sigma.mk j (H (aoyagiLemma5InteriorCoord ell j hj))) ∈
      aoyagiLemma5CountDatumSet ell a M m baseValue := by
  exact aoyagiLemma5CountDatumSet_mem_of_terminalH_binaryIncrementPrefixDelta
    ell a M m H baseValue hj hT.a_le_ell hH0 hHlast hselected
    (aoyagiLemma5Eq5_endpointChain_binaryIncrementPrefixDelta_of_terminalRoom
      ell a p alpha M m H C layerWidth T hT hroom hH0 hHlast hselected
      hH_endpoint)
    hne_base

/-- A supplied equation `(5)` terminal-room endpoint value gives one counted
datum at any interior selected coordinate, provided that endpoint value is not
the supplied base value. -/
theorem aoyagiLemma5Eq5_endpointValue_countDatumSet_mem_of_terminalRoom
    (ell a p alpha : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (hroom : p + 2 * a - alpha ≤ ell)
    (hH0 : H 0 = m 0)
    (hHlast : H (Fin.last ell) = 0)
    (hselected :
      (∑ i : Fin (ell + 1), m i) = (ell : ℤ) * (M - 1) + a)
    (hH_endpoint :
      ∀ b : Fin (ell + 1), 1 ≤ b.val → b.val < ell →
        H b = T (C.point b.val - 1))
    {j : ℕ} (hj : j ∈ Finset.Icc 1 (ell - 1))
    (hne_base : T (C.point j - 1) ≠ baseValue j) :
    some (Sigma.mk j (T (C.point j - 1))) ∈
      aoyagiLemma5CountDatumSet ell a M m baseValue := by
  have hj_pos : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hj_lt_ell : j < ell := by
    have hj_le : j ≤ ell - 1 := (Finset.mem_Icc.mp hj).2
    omega
  have hH_eq_T :
      H (aoyagiLemma5InteriorCoord ell j hj) =
        T (C.point j - 1) := by
    simpa [aoyagiLemma5InteriorCoord] using
      hH_endpoint (aoyagiLemma5InteriorCoord ell j hj) hj_pos hj_lt_ell
  have hne_H :
      H (aoyagiLemma5InteriorCoord ell j hj) ≠ baseValue j := by
    rw [hH_eq_T]
    exact hne_base
  have hmem :=
    aoyagiLemma5Eq5_endpointChain_countDatumSet_mem_of_terminalRoom
      ell a p alpha M m H baseValue C layerWidth T hT hroom hH0 hHlast
      hselected hH_endpoint hj hne_H
  simpa [hH_eq_T] using hmem

/-- A supplied equation `(5)` own-block branch gives both a counted datum and
the corresponding introduced source label, provided its own-block value is not
the supplied base value.

This is a one-branch payload adapter.  It does not construct equation `(5)`,
prove nonbase status, or build classifier/back-to-label data. -/
theorem
    aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_widthBound
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected :
      (∑ i : Fin (ell + 1), m i) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    {S k : ℕ} (hp_pos : 1 ≤ p) (hS : C.block p S)
    (hlast : C.point ell ≤ L + 1)
    (hwidth_le : aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ))
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ))
    (hne_base : T S ≠ baseValue p) :
    some (Sigma.mk p (T S)) ∈
        aoyagiLemma5CountDatumSet ell a M m baseValue ∧
      T S = (k : ℤ) - 1 ∧
        Sigma.mk S k ∈ introducedLabelFinset L n S k := by
  have hpIcc : p ∈ Finset.Icc 1 (ell - 1) := by
    have hp_lt_ell : p < ell := hS.1
    rw [Finset.mem_Icc]
    exact ⟨hp_pos, by omega⟩
  have hpayload :=
    aoyagiLemma5Eq5_ownBlock_intervalValue_mem_introducedLabelFinset_of_lastPoint_widthBound
      L ell a p alpha n M m C layerWidth T hell hselected hsource hT hS
      hlast hwidth_le hk
  have hcount :
      some (Sigma.mk p (T S)) ∈
        aoyagiLemma5CountDatumSet ell a M m baseValue :=
    aoyagiLemma5CountDatumSet_mem_of_intervalValueSetNat
      ell a M m baseValue hpIcc hpayload.1 hne_base
  exact ⟨hcount, hpayload.2⟩

/-- A supplied equation `(5)` own-block branch gives both counted-datum and
introduced-label data, deriving the selected-width bound from a block-local
actual-width lower-bound hypothesis.

This is the block-width version of
`aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_widthBound`.
It still does not construct equation `(5)`, prove nonbase status, or build
classifier/back-to-label data. -/
theorem
    aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_blockWidth
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected :
      (∑ i : Fin (ell + 1), m i) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (hactual :
      ∀ i : Fin ell, ∀ r : ℕ,
        C.point i.val ≤ r → r < C.point (i.val + 1) →
          aoyagiSelectedWidthNat ell m i.val ≤ (n r : ℤ))
    {S k : ℕ} (hS : C.block p S)
    (hlast : C.point ell ≤ L + 1)
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ))
    (hne_base : T S ≠ baseValue p) :
    some (Sigma.mk p (T S)) ∈
        aoyagiLemma5CountDatumSet ell a M m baseValue ∧
      T S = (k : ℤ) - 1 ∧
        Sigma.mk S k ∈ introducedLabelFinset L n S k := by
  have hp_pos : 1 ≤ p := by
    have hpos : 1 ≤ alpha := hT.alpha_pos
    have hlt : alpha < p := hT.alpha_lt_p
    omega
  have hwidth_le :
      aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ) :=
    C.selectedWidthNat_le_actualWidth_of_block n m hactual hS
  exact
    aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_widthBound
      L ell a p alpha n M m baseValue C layerWidth T hell hselected hsource hT
      hp_pos hS hlast hwidth_le hk hne_base

/-- Left-endpoint/minimum version of the Eq5 own-block counted/introduced
payload.

The selected-width bound is derived from selected left-endpoint width
identities and a block-local minimum condition.  The theorem is still a
one-branch payload adapter; it does not construct equation `(5)` or prove
nonbase status. -/
theorem
    aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_leftEndpointMin
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected :
      (∑ i : Fin (ell + 1), m i) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (hleft :
      ∀ i : Fin ell,
        (n (C.point i.val) : ℤ) = aoyagiSelectedWidthNat ell m i.val)
    (hmin :
      ∀ i : Fin ell, ∀ r : ℕ,
        C.point i.val ≤ r → r < C.point (i.val + 1) →
          n (C.point i.val) ≤ n r)
    {S k : ℕ} (hS : C.block p S)
    (hlast : C.point ell ≤ L + 1)
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ))
    (hne_base : T S ≠ baseValue p) :
    some (Sigma.mk p (T S)) ∈
        aoyagiLemma5CountDatumSet ell a M m baseValue ∧
      T S = (k : ℤ) - 1 ∧
        Sigma.mk S k ∈ introducedLabelFinset L n S k := by
  have hp_pos : 1 ≤ p := by
    have hpos : 1 ≤ alpha := hT.alpha_pos
    have hlt : alpha < p := hT.alpha_lt_p
    omega
  have hwidth_le :
      aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ) :=
    C.selectedWidthNat_le_actualWidth_of_block_of_leftEndpoint_min
      n m hleft hmin hS
  exact
    aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_widthBound
      L ell a p alpha n M m baseValue C layerWidth T hell hselected hsource hT
      hp_pos hS hlast hwidth_le hk hne_base

/-- Off-selected dominance version of the Eq5 own-block counted/introduced
payload.

The selected-width bound is derived from actual widths at selected cutpoints
and dominance of every off-selected layer over the selected widths. -/
theorem
    aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_offSelected
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected :
      (∑ i : Fin (ell + 1), m i) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (hselectedWidth :
      ∀ i : Fin (ell + 1), (n (C.point i.val) : ℤ) = m i)
    (hoffSelected :
      ∀ t : ℕ, (∀ i : Fin (ell + 1), t ≠ C.point i.val) →
        ∀ i : Fin (ell + 1), m i ≤ (n t : ℤ))
    {S k : ℕ} (hS : C.block p S)
    (hlast : C.point ell ≤ L + 1)
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ))
    (hne_base : T S ≠ baseValue p) :
    some (Sigma.mk p (T S)) ∈
        aoyagiLemma5CountDatumSet ell a M m baseValue ∧
      T S = (k : ℤ) - 1 ∧
        Sigma.mk S k ∈ introducedLabelFinset L n S k := by
  have hp_pos : 1 ≤ p := by
    have hpos : 1 ≤ alpha := hT.alpha_pos
    have hlt : alpha < p := hT.alpha_lt_p
    omega
  have hwidth_le :
      aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ) :=
    C.selectedWidthNat_le_actualWidth_of_block_of_offSelected
      n m hS hselectedWidth hoffSelected
  exact
    aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_widthBound
      L ell a p alpha n M m baseValue C layerWidth T hell hselected hsource hT
      hp_pos hS hlast hwidth_le hk hne_base

/-- Strict off-selected dominance version of
`aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_offSelected`. -/
theorem
    aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_offSelected_lt
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected :
      (∑ i : Fin (ell + 1), m i) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (hselectedWidth :
      ∀ i : Fin (ell + 1), (n (C.point i.val) : ℤ) = m i)
    (hoffSelected :
      ∀ t : ℕ, (∀ i : Fin (ell + 1), t ≠ C.point i.val) →
        ∀ i : Fin (ell + 1), m i < (n t : ℤ))
    {S k : ℕ} (hS : C.block p S)
    (hlast : C.point ell ≤ L + 1)
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ))
    (hne_base : T S ≠ baseValue p) :
    some (Sigma.mk p (T S)) ∈
        aoyagiLemma5CountDatumSet ell a M m baseValue ∧
      T S = (k : ℤ) - 1 ∧
        Sigma.mk S k ∈ introducedLabelFinset L n S k := by
  exact
    aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_offSelected
      L ell a p alpha n M m baseValue C layerWidth T hell hselected hsource hT
      hselectedWidth
      (fun t ht i ↦ le_of_lt (hoffSelected t ht i))
      hS hlast hk hne_base

/-- Build a supplied counted-datum classifier from a finite family of Eq5
own-block source-label payloads with explicit selected-width bounds.

The classifier sends a supplied source label `label = Sigma.mk S k` to the
counted datum `some (pOf label, T label S)`.  Injectivity of this map is kept
as a hypothesis.  This is only classifier packaging; it does not construct Eq5
branches, prove nonbase status, or prove terminal-minimum coverage. -/
def
    aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_widthBound
    (L ell a : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell)
    (labels : Finset (Σ _ : ℕ, ℕ))
    (pOf alphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected :
      (∑ i : Fin (ell + 1), m i) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : ∀ label ∈ labels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        ell a (pOf label) (alphaOf label) M m C
        (layerWidth label) (T label))
    (hblock : ∀ label ∈ labels, C.block (pOf label) label.1)
    (hlast : C.point ell ≤ L + 1)
    (hwidth_le : ∀ label ∈ labels,
      aoyagiSelectedWidthNat ell m (pOf label) ≤
        (n (label.1 + 1) : ℤ))
    (hk : ∀ label ∈ labels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat ell a M m (pOf label) + 1 -
          (alphaOf label : ℤ))
    (hne_base : ∀ label ∈ labels,
      T label label.1 ≠ baseValue (pOf label))
    (hinj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (some (Sigma.mk (pOf label) (T label label.1)) :
            AoyagiLemma5CountDatum))
        ↑labels) :
    AoyagiLemma5CountDatumClassifier (Σ _ : ℕ, ℕ)
      ell a M m baseValue labels where
  classify := fun label ↦
    some (Sigma.mk (pOf label) (T label label.1))
  mapsTo := by
    intro label hlabel
    have hT_label := hT label hlabel
    have hp_pos : 1 ≤ pOf label := by
      have hpos : 1 ≤ alphaOf label := hT_label.alpha_pos
      have hlt : alphaOf label < pOf label := hT_label.alpha_lt_p
      omega
    exact
      (aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_widthBound
        L ell a (pOf label) (alphaOf label) n M m baseValue C
        (layerWidth label) (T label) hell hselected hsource hT_label
        hp_pos (hblock label hlabel) hlast (hwidth_le label hlabel)
        (hk label hlabel) (hne_base label hlabel)).1
  injOn := hinj

/-- Eq5 own-block values make the counted-datum map injective once the
underlying `(p, alpha)` labels are injective.

This is only finite injectivity bookkeeping.  The `(p, alpha)` injectivity is
still supplied; it is not derived from Aoyagi's printed Eq5 source range. -/
theorem aoyagiLemma5Eq5_ownBlock_countDatum_injOn_of_pAlpha_injOn
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell)
    (labels : Finset (Σ _ : ℕ, ℕ))
    (pOf alphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (hT : ∀ label ∈ labels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        ell a (pOf label) (alphaOf label) M m C
        (layerWidth label) (T label))
    (hblock : ∀ label ∈ labels, C.block (pOf label) label.1)
    (hpAlpha_inj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (Sigma.mk (pOf label) (alphaOf label) : Σ _ : ℕ, ℕ))
        ↑labels) :
    Set.InjOn
      (fun label : Σ _ : ℕ, ℕ ↦
        (some (Sigma.mk (pOf label) (T label label.1)) :
          AoyagiLemma5CountDatum))
      ↑labels := by
  intro x hx y hy hxy
  have hsigma :
      ((Sigma.mk (pOf x) (T x x.1)) : Σ _ : ℕ, ℤ) =
        ((Sigma.mk (pOf y) (T y y.1)) : Σ _ : ℕ, ℤ) := by
    simpa using Option.some.inj hxy
  have hp : pOf x = pOf y := congrArg Sigma.fst hsigma
  have hvalue : T x x.1 = T y y.1 := congrArg Sigma.snd hsigma
  have hxOwn :
      AoyagiLemma5Eq5OwnCoordinateBranch
        ell a (pOf x) (alphaOf x) M m C (T x) :=
    aoyagiLemma5Eq5_ownCoordinateBranch_of_piecewiseSourceVector
      ell a (pOf x) (alphaOf x) M m C (layerWidth x) (T x) (hT x hx)
  have hyOwn :
      AoyagiLemma5Eq5OwnCoordinateBranch
        ell a (pOf y) (alphaOf y) M m C (T y) :=
    aoyagiLemma5Eq5_ownCoordinateBranch_of_piecewiseSourceVector
      ell a (pOf y) (alphaOf y) M m C (layerWidth y) (T y) (hT y hy)
  have hxValue :
      T x x.1 =
        aoyagiHtildeUpperNat ell a M m (pOf x) - (alphaOf x : ℤ) :=
    aoyagiLemma5Eq5_ownCoordinate_value
      ell a (pOf x) (alphaOf x) M m C (T x) hxOwn (hblock x hx)
  have hyValue :
      T y y.1 =
        aoyagiHtildeUpperNat ell a M m (pOf y) - (alphaOf y : ℤ) :=
    aoyagiLemma5Eq5_ownCoordinate_value
      ell a (pOf y) (alphaOf y) M m C (T y) hyOwn (hblock y hy)
  have hraw :
      aoyagiHtildeUpperNat ell a M m (pOf x) - (alphaOf x : ℤ) =
        aoyagiHtildeUpperNat ell a M m (pOf y) - (alphaOf y : ℤ) := by
    calc
      aoyagiHtildeUpperNat ell a M m (pOf x) - (alphaOf x : ℤ) =
          T x x.1 := hxValue.symm
      _ = T y y.1 := hvalue
      _ = aoyagiHtildeUpperNat ell a M m (pOf y) - (alphaOf y : ℤ) :=
          hyValue
  have hraw_same :
      aoyagiHtildeUpperNat ell a M m (pOf x) - (alphaOf x : ℤ) =
        aoyagiHtildeUpperNat ell a M m (pOf x) - (alphaOf y : ℤ) := by
    simpa [hp] using hraw
  have halpha_int : (alphaOf x : ℤ) = (alphaOf y : ℤ) := by
    omega
  have halpha : alphaOf x = alphaOf y := by
    exact_mod_cast halpha_int
  apply hpAlpha_inj hx hy
  simp [hp, halpha]

/-- Block-width version of
`aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_widthBound`. -/
def
    aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_blockWidth
    (L ell a : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell)
    (labels : Finset (Σ _ : ℕ, ℕ))
    (pOf alphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected :
      (∑ i : Fin (ell + 1), m i) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : ∀ label ∈ labels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        ell a (pOf label) (alphaOf label) M m C
        (layerWidth label) (T label))
    (hactual :
      ∀ i : Fin ell, ∀ r : ℕ,
        C.point i.val ≤ r → r < C.point (i.val + 1) →
          aoyagiSelectedWidthNat ell m i.val ≤ (n r : ℤ))
    (hblock : ∀ label ∈ labels, C.block (pOf label) label.1)
    (hlast : C.point ell ≤ L + 1)
    (hk : ∀ label ∈ labels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat ell a M m (pOf label) + 1 -
          (alphaOf label : ℤ))
    (hne_base : ∀ label ∈ labels,
      T label label.1 ≠ baseValue (pOf label))
    (hinj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (some (Sigma.mk (pOf label) (T label label.1)) :
            AoyagiLemma5CountDatum))
        ↑labels) :
    AoyagiLemma5CountDatumClassifier (Σ _ : ℕ, ℕ)
      ell a M m baseValue labels :=
  aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_widthBound
    L ell a n M m baseValue C labels pOf alphaOf layerWidth T
    hell hselected hsource hT hblock hlast
    (fun label hlabel ↦
      C.selectedWidthNat_le_actualWidth_of_block n m hactual
        (hblock label hlabel))
    hk hne_base hinj

/-- Left-endpoint/minimum version of the Eq5 own-block counted-datum
classifier adapter. -/
def
    aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_leftEndpointMin
    (L ell a : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell)
    (labels : Finset (Σ _ : ℕ, ℕ))
    (pOf alphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected :
      (∑ i : Fin (ell + 1), m i) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : ∀ label ∈ labels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        ell a (pOf label) (alphaOf label) M m C
        (layerWidth label) (T label))
    (hleft :
      ∀ i : Fin ell,
        (n (C.point i.val) : ℤ) = aoyagiSelectedWidthNat ell m i.val)
    (hmin :
      ∀ i : Fin ell, ∀ r : ℕ,
        C.point i.val ≤ r → r < C.point (i.val + 1) →
          n (C.point i.val) ≤ n r)
    (hblock : ∀ label ∈ labels, C.block (pOf label) label.1)
    (hlast : C.point ell ≤ L + 1)
    (hk : ∀ label ∈ labels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat ell a M m (pOf label) + 1 -
          (alphaOf label : ℤ))
    (hne_base : ∀ label ∈ labels,
      T label label.1 ≠ baseValue (pOf label))
    (hinj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (some (Sigma.mk (pOf label) (T label label.1)) :
            AoyagiLemma5CountDatum))
        ↑labels) :
    AoyagiLemma5CountDatumClassifier (Σ _ : ℕ, ℕ)
      ell a M m baseValue labels :=
  aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_widthBound
    L ell a n M m baseValue C labels pOf alphaOf layerWidth T
    hell hselected hsource hT hblock hlast
    (fun label hlabel ↦
      C.selectedWidthNat_le_actualWidth_of_block_of_leftEndpoint_min
        n m hleft hmin (hblock label hlabel))
    hk hne_base hinj

/-- Off-selected dominance version of the Eq5 own-block counted-datum
classifier adapter. -/
def
    aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_offSelected
    (L ell a : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell)
    (labels : Finset (Σ _ : ℕ, ℕ))
    (pOf alphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected :
      (∑ i : Fin (ell + 1), m i) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : ∀ label ∈ labels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        ell a (pOf label) (alphaOf label) M m C
        (layerWidth label) (T label))
    (hselectedWidth :
      ∀ i : Fin (ell + 1), (n (C.point i.val) : ℤ) = m i)
    (hoffSelected :
      ∀ t : ℕ, (∀ i : Fin (ell + 1), t ≠ C.point i.val) →
        ∀ i : Fin (ell + 1), m i ≤ (n t : ℤ))
    (hblock : ∀ label ∈ labels, C.block (pOf label) label.1)
    (hlast : C.point ell ≤ L + 1)
    (hk : ∀ label ∈ labels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat ell a M m (pOf label) + 1 -
          (alphaOf label : ℤ))
    (hne_base : ∀ label ∈ labels,
      T label label.1 ≠ baseValue (pOf label))
    (hinj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (some (Sigma.mk (pOf label) (T label label.1)) :
            AoyagiLemma5CountDatum))
        ↑labels) :
    AoyagiLemma5CountDatumClassifier (Σ _ : ℕ, ℕ)
      ell a M m baseValue labels :=
  aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_widthBound
    L ell a n M m baseValue C labels pOf alphaOf layerWidth T
    hell hselected hsource hT hblock hlast
    (fun label hlabel ↦
      C.selectedWidthNat_le_actualWidth_of_block_of_offSelected
        n m (hblock label hlabel) hselectedWidth hoffSelected)
    hk hne_base hinj

/-- Strict off-selected dominance version of
`aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_offSelected`. -/
def
    aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_offSelected_lt
    (L ell a : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell)
    (labels : Finset (Σ _ : ℕ, ℕ))
    (pOf alphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected :
      (∑ i : Fin (ell + 1), m i) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : ∀ label ∈ labels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        ell a (pOf label) (alphaOf label) M m C
        (layerWidth label) (T label))
    (hselectedWidth :
      ∀ i : Fin (ell + 1), (n (C.point i.val) : ℤ) = m i)
    (hoffSelected :
      ∀ t : ℕ, (∀ i : Fin (ell + 1), t ≠ C.point i.val) →
        ∀ i : Fin (ell + 1), m i < (n t : ℤ))
    (hblock : ∀ label ∈ labels, C.block (pOf label) label.1)
    (hlast : C.point ell ≤ L + 1)
    (hk : ∀ label ∈ labels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat ell a M m (pOf label) + 1 -
          (alphaOf label : ℤ))
    (hne_base : ∀ label ∈ labels,
      T label label.1 ≠ baseValue (pOf label))
    (hinj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (some (Sigma.mk (pOf label) (T label label.1)) :
            AoyagiLemma5CountDatum))
        ↑labels) :
    AoyagiLemma5CountDatumClassifier (Σ _ : ℕ, ℕ)
      ell a M m baseValue labels :=
  aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_offSelected
    L ell a n M m baseValue C labels pOf alphaOf layerWidth T
    hell hselected hsource hT hselectedWidth
    (fun t ht i ↦ le_of_lt (hoffSelected t ht i))
    hblock hlast hk hne_base hinj

/-- Common-domain version of the Eq5 own-block counted/introduced payload.

The one-branch payload first introduces `(S,k)` at the local state `(S,k)`;
the supplied state comparison then moves it to a later/common introduced-label
domain.  This theorem still does not construct Eq5 branches or prove
terminal-domain coverage. -/
theorem
    aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_widthBound
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected :
      (∑ i : Fin (ell + 1), m i) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    {S k Sfinal Jfinal : ℕ} (hp_pos : 1 ≤ p) (hS : C.block p S)
    (hlast : C.point ell ≤ L + 1)
    (hwidth_le : aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ))
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ))
    (hne_base : T S ≠ baseValue p)
    (hstate : S < Sfinal ∨ S = Sfinal ∧ k ≤ Jfinal) :
    some (Sigma.mk p (T S)) ∈
        aoyagiLemma5CountDatumSet ell a M m baseValue ∧
      T S = (k : ℤ) - 1 ∧
        Sigma.mk S k ∈ introducedLabelFinset L n Sfinal Jfinal := by
  have hpayload :=
    aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_widthBound
      L ell a p alpha n M m baseValue C layerWidth T hell hselected hsource hT
      hp_pos hS hlast hwidth_le hk hne_base
  exact ⟨hpayload.1, hpayload.2.1,
    introducedLabelFinset_subset_of_state_le hstate hpayload.2.2⟩

/-- Block-width version of
`aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_widthBound`. -/
theorem
    aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_blockWidth
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected :
      (∑ i : Fin (ell + 1), m i) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (hactual :
      ∀ i : Fin ell, ∀ r : ℕ,
        C.point i.val ≤ r → r < C.point (i.val + 1) →
          aoyagiSelectedWidthNat ell m i.val ≤ (n r : ℤ))
    {S k Sfinal Jfinal : ℕ} (hS : C.block p S)
    (hlast : C.point ell ≤ L + 1)
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ))
    (hne_base : T S ≠ baseValue p)
    (hstate : S < Sfinal ∨ S = Sfinal ∧ k ≤ Jfinal) :
    some (Sigma.mk p (T S)) ∈
        aoyagiLemma5CountDatumSet ell a M m baseValue ∧
      T S = (k : ℤ) - 1 ∧
        Sigma.mk S k ∈ introducedLabelFinset L n Sfinal Jfinal := by
  have hp_pos : 1 ≤ p := by
    have hpos : 1 ≤ alpha := hT.alpha_pos
    have hlt : alpha < p := hT.alpha_lt_p
    omega
  have hwidth_le :
      aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ) :=
    C.selectedWidthNat_le_actualWidth_of_block n m hactual hS
  exact
    aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_widthBound
      L ell a p alpha n M m baseValue C layerWidth T hell hselected hsource hT
      hp_pos hS hlast hwidth_le hk hne_base hstate

/-- Left-endpoint/minimum version of the Eq5 own-block common-domain payload. -/
theorem
    aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_leftEndpointMin
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected :
      (∑ i : Fin (ell + 1), m i) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (hleft :
      ∀ i : Fin ell,
        (n (C.point i.val) : ℤ) = aoyagiSelectedWidthNat ell m i.val)
    (hmin :
      ∀ i : Fin ell, ∀ r : ℕ,
        C.point i.val ≤ r → r < C.point (i.val + 1) →
          n (C.point i.val) ≤ n r)
    {S k Sfinal Jfinal : ℕ} (hS : C.block p S)
    (hlast : C.point ell ≤ L + 1)
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ))
    (hne_base : T S ≠ baseValue p)
    (hstate : S < Sfinal ∨ S = Sfinal ∧ k ≤ Jfinal) :
    some (Sigma.mk p (T S)) ∈
        aoyagiLemma5CountDatumSet ell a M m baseValue ∧
      T S = (k : ℤ) - 1 ∧
        Sigma.mk S k ∈ introducedLabelFinset L n Sfinal Jfinal := by
  have hp_pos : 1 ≤ p := by
    have hpos : 1 ≤ alpha := hT.alpha_pos
    have hlt : alpha < p := hT.alpha_lt_p
    omega
  have hwidth_le :
      aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ) :=
    C.selectedWidthNat_le_actualWidth_of_block_of_leftEndpoint_min
      n m hleft hmin hS
  exact
    aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_widthBound
      L ell a p alpha n M m baseValue C layerWidth T hell hselected hsource hT
      hp_pos hS hlast hwidth_le hk hne_base hstate

/-- Off-selected dominance version of the Eq5 own-block common-domain payload. -/
theorem
    aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_offSelected
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected :
      (∑ i : Fin (ell + 1), m i) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (hselectedWidth :
      ∀ i : Fin (ell + 1), (n (C.point i.val) : ℤ) = m i)
    (hoffSelected :
      ∀ t : ℕ, (∀ i : Fin (ell + 1), t ≠ C.point i.val) →
        ∀ i : Fin (ell + 1), m i ≤ (n t : ℤ))
    {S k Sfinal Jfinal : ℕ} (hS : C.block p S)
    (hlast : C.point ell ≤ L + 1)
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ))
    (hne_base : T S ≠ baseValue p)
    (hstate : S < Sfinal ∨ S = Sfinal ∧ k ≤ Jfinal) :
    some (Sigma.mk p (T S)) ∈
        aoyagiLemma5CountDatumSet ell a M m baseValue ∧
      T S = (k : ℤ) - 1 ∧
        Sigma.mk S k ∈ introducedLabelFinset L n Sfinal Jfinal := by
  have hp_pos : 1 ≤ p := by
    have hpos : 1 ≤ alpha := hT.alpha_pos
    have hlt : alpha < p := hT.alpha_lt_p
    omega
  have hwidth_le :
      aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ) :=
    C.selectedWidthNat_le_actualWidth_of_block_of_offSelected
      n m hS hselectedWidth hoffSelected
  exact
    aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_widthBound
      L ell a p alpha n M m baseValue C layerWidth T hell hselected hsource hT
      hp_pos hS hlast hwidth_le hk hne_base hstate

/-- Strict off-selected dominance version of
`aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_offSelected`. -/
theorem
    aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_offSelected_lt
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected :
      (∑ i : Fin (ell + 1), m i) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (hselectedWidth :
      ∀ i : Fin (ell + 1), (n (C.point i.val) : ℤ) = m i)
    (hoffSelected :
      ∀ t : ℕ, (∀ i : Fin (ell + 1), t ≠ C.point i.val) →
        ∀ i : Fin (ell + 1), m i < (n t : ℤ))
    {S k Sfinal Jfinal : ℕ} (hS : C.block p S)
    (hlast : C.point ell ≤ L + 1)
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ))
    (hne_base : T S ≠ baseValue p)
    (hstate : S < Sfinal ∨ S = Sfinal ∧ k ≤ Jfinal) :
    some (Sigma.mk p (T S)) ∈
        aoyagiLemma5CountDatumSet ell a M m baseValue ∧
      T S = (k : ℤ) - 1 ∧
        Sigma.mk S k ∈ introducedLabelFinset L n Sfinal Jfinal := by
  exact
    aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_offSelected
      L ell a p alpha n M m baseValue C layerWidth T hell hselected hsource hT
      hselectedWidth
      (fun t ht i ↦ le_of_lt (hoffSelected t ht i))
      hS hlast hk hne_base hstate

end Aoyagi
end DLN
end DLNFibre
