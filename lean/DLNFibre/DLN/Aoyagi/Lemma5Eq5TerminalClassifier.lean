import DLNFibre.DLN.Aoyagi.Lemma5Eq5CountDatumBridge
import DLNFibre.DLN.Aoyagi.Lemma5TerminalBridge

/-!
# Eq5 terminal-minimum counted-datum classifier bridge

This file packages supplied Eq5 own-block common-domain payloads as the
counted-datum classifier needed by the terminal-minimum upper-bound API.  It
does not construct Eq5 branches, prove classifier injectivity, build a
back-to-label map, prove exactness, pole order, normal crossings, or RLCT
extraction.
-/

open scoped BigOperators

namespace DLNFibre
namespace DLN
namespace Aoyagi

namespace AoyagiLemma5SuppliedTerminalCandidateFamily

/-- Build the terminal-minimum counted-datum classifier from supplied Eq5
own-block common-domain payload data.

For each terminal-minimum label `label = (S,k)`, the classifier sends `label`
to `some (pOf label, T label S)`.  The `mapsTo` field is proved from the
Eq5 own-block common-domain payload.  Injectivity of this counted-datum map is
still supplied. -/
def terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_widthBound
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (pOf alphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (hselected :
      (∑ i : Fin (N + 2), m i) = ((N + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (N + 2),
      ((N + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (N + 2), m j)
    (hT : ∀ label ∈ TC.terminalMinimumLabels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        (N + 1) a (pOf label) (alphaOf label) M m cut
        (layerWidth label) (T label))
    (hblock : ∀ label ∈ TC.terminalMinimumLabels,
      cut.block (pOf label) label.1)
    (hlast : cut.point (N + 1) ≤ L + 1)
    (hwidth_le : ∀ label ∈ TC.terminalMinimumLabels,
      aoyagiSelectedWidthNat (N + 1) m (pOf label) ≤
        (width (label.1 + 1) : ℤ))
    (hk : ∀ label ∈ TC.terminalMinimumLabels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat (N + 1) a M m (pOf label) + 1 -
          (alphaOf label : ℤ))
    (hne_base : ∀ label ∈ TC.terminalMinimumLabels,
      T label label.1 ≠ TC.family.baseValue (pOf label))
    (hinj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (some (Sigma.mk (pOf label) (T label label.1)) :
            AoyagiLemma5CountDatum))
        ↑TC.terminalMinimumLabels) :
    TC.TerminalMinimumCountDatumClassifier where
  classify := fun label ↦
    some (Sigma.mk (pOf label) (T label label.1))
  mapsTo := by
    intro label hlabel
    have hT_label := hT label hlabel
    have hp_pos : 1 ≤ pOf label := by
      have hpos : 1 ≤ alphaOf label := hT_label.alpha_pos
      have hlt : alphaOf label < pOf label := hT_label.alpha_lt_p
      omega
    have hstate :
        label.1 < Sfinal ∨ label.1 = Sfinal ∧ label.2 ≤ Jfinal :=
      (TC.mem_terminalMinimumLabels.mp hlabel).1.2
    exact
      (aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_widthBound
        L (N + 1) a (pOf label) (alphaOf label) width M m
        TC.family.baseValue cut (layerWidth label) (T label)
        (Nat.succ_pos N) hselected hsource hT_label hp_pos
        (hblock label hlabel) hlast (hwidth_le label hlabel)
        (hk label hlabel) (hne_base label hlabel) hstate).1
  injOn := hinj

/-- Block-width version of
`terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_widthBound`. -/
def terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_blockWidth
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (pOf alphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (hselected :
      (∑ i : Fin (N + 2), m i) = ((N + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (N + 2),
      ((N + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (N + 2), m j)
    (hT : ∀ label ∈ TC.terminalMinimumLabels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        (N + 1) a (pOf label) (alphaOf label) M m cut
        (layerWidth label) (T label))
    (hactual :
      ∀ i : Fin (N + 1), ∀ r : ℕ,
        cut.point i.val ≤ r → r < cut.point (i.val + 1) →
          aoyagiSelectedWidthNat (N + 1) m i.val ≤ (width r : ℤ))
    (hblock : ∀ label ∈ TC.terminalMinimumLabels,
      cut.block (pOf label) label.1)
    (hlast : cut.point (N + 1) ≤ L + 1)
    (hk : ∀ label ∈ TC.terminalMinimumLabels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat (N + 1) a M m (pOf label) + 1 -
          (alphaOf label : ℤ))
    (hne_base : ∀ label ∈ TC.terminalMinimumLabels,
      T label label.1 ≠ TC.family.baseValue (pOf label))
    (hinj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (some (Sigma.mk (pOf label) (T label label.1)) :
            AoyagiLemma5CountDatum))
        ↑TC.terminalMinimumLabels) :
    TC.TerminalMinimumCountDatumClassifier :=
  TC.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_widthBound
    cut pOf alphaOf layerWidth T hselected hsource hT hblock hlast
    (fun label hlabel ↦
      cut.selectedWidthNat_le_actualWidth_of_block width m hactual
        (hblock label hlabel))
    hk hne_base hinj

/-- Left-endpoint/minimum version of the terminal-minimum counted-datum
classifier adapter. -/
def terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_leftEndpointMin
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (pOf alphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (hselected :
      (∑ i : Fin (N + 2), m i) = ((N + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (N + 2),
      ((N + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (N + 2), m j)
    (hT : ∀ label ∈ TC.terminalMinimumLabels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        (N + 1) a (pOf label) (alphaOf label) M m cut
        (layerWidth label) (T label))
    (hleft :
      ∀ i : Fin (N + 1),
        (width (cut.point i.val) : ℤ) =
          aoyagiSelectedWidthNat (N + 1) m i.val)
    (hmin :
      ∀ i : Fin (N + 1), ∀ r : ℕ,
        cut.point i.val ≤ r → r < cut.point (i.val + 1) →
          width (cut.point i.val) ≤ width r)
    (hblock : ∀ label ∈ TC.terminalMinimumLabels,
      cut.block (pOf label) label.1)
    (hlast : cut.point (N + 1) ≤ L + 1)
    (hk : ∀ label ∈ TC.terminalMinimumLabels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat (N + 1) a M m (pOf label) + 1 -
          (alphaOf label : ℤ))
    (hne_base : ∀ label ∈ TC.terminalMinimumLabels,
      T label label.1 ≠ TC.family.baseValue (pOf label))
    (hinj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (some (Sigma.mk (pOf label) (T label label.1)) :
            AoyagiLemma5CountDatum))
        ↑TC.terminalMinimumLabels) :
    TC.TerminalMinimumCountDatumClassifier :=
  TC.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_widthBound
    cut pOf alphaOf layerWidth T hselected hsource hT hblock hlast
    (fun label hlabel ↦
      cut.selectedWidthNat_le_actualWidth_of_block_of_leftEndpoint_min
        width m hleft hmin (hblock label hlabel))
    hk hne_base hinj

/-- Off-selected dominance version of the terminal-minimum counted-datum
classifier adapter. -/
def terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_offSelected
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (pOf alphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (hselected :
      (∑ i : Fin (N + 2), m i) = ((N + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (N + 2),
      ((N + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (N + 2), m j)
    (hT : ∀ label ∈ TC.terminalMinimumLabels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        (N + 1) a (pOf label) (alphaOf label) M m cut
        (layerWidth label) (T label))
    (hselectedWidth :
      ∀ i : Fin (N + 2), (width (cut.point i.val) : ℤ) = m i)
    (hoffSelected :
      ∀ r : ℕ, (∀ i : Fin (N + 2), r ≠ cut.point i.val) →
        ∀ i : Fin (N + 2), m i ≤ (width r : ℤ))
    (hblock : ∀ label ∈ TC.terminalMinimumLabels,
      cut.block (pOf label) label.1)
    (hlast : cut.point (N + 1) ≤ L + 1)
    (hk : ∀ label ∈ TC.terminalMinimumLabels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat (N + 1) a M m (pOf label) + 1 -
          (alphaOf label : ℤ))
    (hne_base : ∀ label ∈ TC.terminalMinimumLabels,
      T label label.1 ≠ TC.family.baseValue (pOf label))
    (hinj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (some (Sigma.mk (pOf label) (T label label.1)) :
            AoyagiLemma5CountDatum))
        ↑TC.terminalMinimumLabels) :
    TC.TerminalMinimumCountDatumClassifier :=
  TC.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_widthBound
    cut pOf alphaOf layerWidth T hselected hsource hT hblock hlast
    (fun label hlabel ↦
      cut.selectedWidthNat_le_actualWidth_of_block_of_offSelected
        width m (hblock label hlabel) hselectedWidth hoffSelected)
    hk hne_base hinj

/-- Strict off-selected dominance version of
`terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_offSelected`. -/
def terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_offSelected_lt
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (pOf alphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (hselected :
      (∑ i : Fin (N + 2), m i) = ((N + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (N + 2),
      ((N + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (N + 2), m j)
    (hT : ∀ label ∈ TC.terminalMinimumLabels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        (N + 1) a (pOf label) (alphaOf label) M m cut
        (layerWidth label) (T label))
    (hselectedWidth :
      ∀ i : Fin (N + 2), (width (cut.point i.val) : ℤ) = m i)
    (hoffSelected :
      ∀ r : ℕ, (∀ i : Fin (N + 2), r ≠ cut.point i.val) →
        ∀ i : Fin (N + 2), m i < (width r : ℤ))
    (hblock : ∀ label ∈ TC.terminalMinimumLabels,
      cut.block (pOf label) label.1)
    (hlast : cut.point (N + 1) ≤ L + 1)
    (hk : ∀ label ∈ TC.terminalMinimumLabels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat (N + 1) a M m (pOf label) + 1 -
          (alphaOf label : ℤ))
    (hne_base : ∀ label ∈ TC.terminalMinimumLabels,
      T label label.1 ≠ TC.family.baseValue (pOf label))
    (hinj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (some (Sigma.mk (pOf label) (T label label.1)) :
            AoyagiLemma5CountDatum))
        ↑TC.terminalMinimumLabels) :
    TC.TerminalMinimumCountDatumClassifier :=
  TC.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_offSelected
    cut pOf alphaOf layerWidth T hselected hsource hT hselectedWidth
    (fun r hr i ↦ le_of_lt (hoffSelected r hr i))
    hblock hlast hk hne_base hinj

end AoyagiLemma5SuppliedTerminalCandidateFamily

end Aoyagi
end DLN
end DLNFibre
