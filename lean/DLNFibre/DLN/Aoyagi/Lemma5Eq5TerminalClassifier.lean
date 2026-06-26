import DLNFibre.DLN.Aoyagi.Lemma5Eq5CountDatumBridge
import DLNFibre.DLN.Aoyagi.Lemma5Eq5SuppliedCoverage
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

open AoyagiLemma5SuppliedNonbaseFamily

/-- Terminal-minimum Eq5 own-block payloads make the terminal counted-datum
map injective once the `(p, alpha)` data are injective on terminal labels. -/
theorem terminalMinimumCountDatum_injOn_of_eq5OwnBlock_pAlpha_injOn
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
    (hT : ∀ label ∈ TC.terminalMinimumLabels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        (N + 1) a (pOf label) (alphaOf label) M m cut
        (layerWidth label) (T label))
    (hblock : ∀ label ∈ TC.terminalMinimumLabels,
      cut.block (pOf label) label.1)
    (hpAlpha_inj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (Sigma.mk (pOf label) (alphaOf label) : Σ _ : ℕ, ℕ))
        ↑TC.terminalMinimumLabels) :
    Set.InjOn
      (fun label : Σ _ : ℕ, ℕ ↦
        (some (Sigma.mk (pOf label) (T label label.1)) :
          AoyagiLemma5CountDatum))
      ↑TC.terminalMinimumLabels :=
  aoyagiLemma5Eq5_ownBlock_countDatum_injOn_of_pAlpha_injOn
    (N + 1) a M m cut TC.terminalMinimumLabels pOf alphaOf layerWidth T
    hT hblock hpAlpha_inj

/-- Terminal-minimum upper count from supplied Eq5 endpoint-chain data and the
deterministic first-nonbase selector.

For each terminal-minimum label this assumes an Eq5 endpoint chain whose
prefix increments are binary by the existing terminal-room theorem.  The
remaining nonduplication is the explicit injectivity of the deterministic
first-nonbase-or-base counted datum on `TC.terminalMinimumLabels`.  No source
classifier, branch-label injectivity, back-to-label map, or exactness theorem
is constructed here. -/
theorem terminalMinimumLabels_card_le_of_eq5EndpointChain_firstInteriorNonbase
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (ha : a ≤ N + 1)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (pOf alphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (Hlabel : (Σ _ : ℕ, ℕ) → Fin (N + 2) → ℤ)
    (hselected :
      (∑ i : Fin (N + 2), m i) = ((N + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hT : ∀ label ∈ TC.terminalMinimumLabels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        (N + 1) a (pOf label) (alphaOf label) M m cut
        (layerWidth label) (T label))
    (hroom : ∀ label ∈ TC.terminalMinimumLabels,
      pOf label + 2 * a - alphaOf label ≤ N + 1)
    (hH0 : ∀ label ∈ TC.terminalMinimumLabels,
      Hlabel label 0 = m 0)
    (hHlast : ∀ label ∈ TC.terminalMinimumLabels,
      Hlabel label (Fin.last (N + 1)) = 0)
    (hH_endpoint : ∀ label ∈ TC.terminalMinimumLabels,
      ∀ b : Fin (N + 2), 1 ≤ b.val → b.val < N + 1 →
        Hlabel label b = T label (cut.point b.val - 1))
    (hinjFirst :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase
            (N + 1) (Hlabel label) TC.family.baseValue)
        ↑TC.terminalMinimumLabels) :
    TC.terminalMinimumLabels.card ≤ a * (N + 1 - a) + 1 := by
  exact
    aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase_candidates_card_le
      (N + 1) a M m TC.family.baseValue TC.terminalMinimumLabels Hlabel
      (Nat.succ_pos N) ha
      (fun label hlabel ↦ hH0 label hlabel)
      (fun label hlabel ↦ hHlast label hlabel)
      hselected
      (fun label hlabel ↦
        aoyagiLemma5Eq5_endpointChain_binaryIncrementPrefixDelta_of_terminalRoom
          (N + 1) a (pOf label) (alphaOf label) M m (Hlabel label) cut
          (layerWidth label) (T label) (hT label hlabel)
          (hroom label hlabel) (hH0 label hlabel) (hHlast label hlabel)
          hselected (hH_endpoint label hlabel))
      TC.family.baseValue_mem hinjFirst

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

/-- Numeric terminal-minimum upper count from supplied Eq5 own-block
common-domain payload data.

This is only the counted-datum classifier upper bound composed with the Eq5
payload classifier constructor.  Eq5 payload data, nonbase status, and
counted-datum injectivity remain supplied hypotheses. -/
theorem terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_widthBound
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (ha : a ≤ N + 1)
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
    TC.terminalMinimumLabels.card ≤ a * (N + 1 - a) + 1 := by
  exact TC.terminalMinimumLabels_card_le_of_countDatumClassifier ha
    (TC.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_widthBound
      cut pOf alphaOf layerWidth T hselected hsource hT hblock hlast
      hwidth_le hk hne_base hinj)

/-- Block-width version of
`terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_widthBound`. -/
theorem terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_blockWidth
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (ha : a ≤ N + 1)
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
    TC.terminalMinimumLabels.card ≤ a * (N + 1 - a) + 1 := by
  exact TC.terminalMinimumLabels_card_le_of_countDatumClassifier ha
    (TC.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_blockWidth
      cut pOf alphaOf layerWidth T hselected hsource hT hactual hblock
      hlast hk hne_base hinj)

/-- Left-endpoint/minimum version of
`terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_widthBound`. -/
theorem terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_leftEndpointMin
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (ha : a ≤ N + 1)
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
    TC.terminalMinimumLabels.card ≤ a * (N + 1 - a) + 1 := by
  exact TC.terminalMinimumLabels_card_le_of_countDatumClassifier ha
    (TC.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_leftEndpointMin
      cut pOf alphaOf layerWidth T hselected hsource hT hleft hmin hblock
      hlast hk hne_base hinj)

/-- Off-selected dominance version of
`terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_widthBound`. -/
theorem terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_offSelected
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (ha : a ≤ N + 1)
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
    TC.terminalMinimumLabels.card ≤ a * (N + 1 - a) + 1 := by
  exact TC.terminalMinimumLabels_card_le_of_countDatumClassifier ha
    (TC.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_offSelected
      cut pOf alphaOf layerWidth T hselected hsource hT hselectedWidth
      hoffSelected hblock hlast hk hne_base hinj)

/-- Strict off-selected dominance version of
`terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_widthBound`. -/
theorem terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_offSelected_lt
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (ha : a ≤ N + 1)
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
    TC.terminalMinimumLabels.card ≤ a * (N + 1 - a) + 1 := by
  exact TC.terminalMinimumLabels_card_le_of_countDatumClassifier ha
    (TC.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_offSelected_lt
      cut pOf alphaOf layerWidth T hselected hsource hT hselectedWidth
      hoffSelected hblock hlast hk hne_base hinj)

/-- Eq5 own-block common-domain payload data and supplied branch-label
injectivity identify terminal-minimum labels with the supplied branch-label
image.

The counted-datum injectivity hypothesis `hinjCountDatum` and branch-label
injectivity hypothesis `hinjBranchLabel` are independent supplied boundaries.
This theorem proves only the finite cardinal-squeeze consequence. -/
theorem terminalMinimumLabels_eq_branchLabelImage_of_eq5OwnBlockCommon_widthBound_cardSqueeze
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (ha : a ≤ N + 1)
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
    (hinjCountDatum :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (some (Sigma.mk (pOf label) (T label label.1)) :
            AoyagiLemma5CountDatum))
        ↑TC.terminalMinimumLabels)
    (hinjBranchLabel : Set.InjOn TC.branchLabel ↑TC.fullBranches) :
    TC.terminalMinimumLabels = TC.branchLabelImage := by
  exact
    TC.terminalMinimumLabels_eq_branchLabelImage_of_countDatumClassifier_and_branchLabel_injOn
      N a M m ha hselected hinjBranchLabel
      (TC.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_widthBound
        cut pOf alphaOf layerWidth T hselected hsource hT hblock hlast
        hwidth_le hk hne_base hinjCountDatum)

/-- Terminal-minimum exactness from Eq5 own-block common-domain payload data
plus supplied branch-label injectivity.

This packages the cardinal-squeeze equality with the supplied branch-label
injectivity.  It does not construct Eq5 payloads, counted-datum injectivity,
or branch-label injectivity from Aoyagi's source. -/
theorem terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_cardSqueeze
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (ha : a ≤ N + 1)
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
    (hinjCountDatum :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (some (Sigma.mk (pOf label) (T label label.1)) :
            AoyagiLemma5CountDatum))
        ↑TC.terminalMinimumLabels)
    (hinjBranchLabel : Set.InjOn TC.branchLabel ↑TC.fullBranches) :
    TC.TerminalMinimumLabelExactness := by
  exact
    TC.terminalMinimumLabelExactness_of_countDatumClassifier_and_branchLabel_injOn
      N a M m ha hselected hinjBranchLabel
      (TC.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_widthBound
        cut pOf alphaOf layerWidth T hselected hsource hT hblock hlast
        hwidth_le hk hne_base hinjCountDatum)

/-- Exact terminal-minimum count from Eq5 own-block common-domain payload data
plus supplied branch-label injectivity.

This is a finite exact-count wrapper over the terminal counted-datum
classifier and cardinal squeeze. -/
theorem terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_cardSqueeze
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (ha : a ≤ N + 1)
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
    (hinjCountDatum :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (some (Sigma.mk (pOf label) (T label label.1)) :
            AoyagiLemma5CountDatum))
        ↑TC.terminalMinimumLabels)
    (hinjBranchLabel : Set.InjOn TC.branchLabel ↑TC.fullBranches) :
    TC.terminalMinimumLabels.card = a * (N + 1 - a) + 1 := by
  exact
    TC.terminalMinimumLabels_card_of_countDatumClassifier_and_branchLabel_injOn
      N a M m ha hselected hinjBranchLabel
      (TC.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_widthBound
        cut pOf alphaOf layerWidth T hselected hsource hT hblock hlast
        hwidth_le hk hne_base hinjCountDatum)

/-- Branch labels biject with terminal-minimum labels from Eq5 own-block
common-domain payload data plus supplied branch-label injectivity.

This is the finite bijection produced by the cardinal squeeze; it does not
construct a counted-datum-preserving back-to-label map. -/
theorem branchLabel_bijOn_terminalMinimumLabels_of_eq5OwnBlockCommon_widthBound_cardSqueeze
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (ha : a ≤ N + 1)
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
    (hinjCountDatum :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (some (Sigma.mk (pOf label) (T label label.1)) :
            AoyagiLemma5CountDatum))
        ↑TC.terminalMinimumLabels)
    (hinjBranchLabel : Set.InjOn TC.branchLabel ↑TC.fullBranches) :
    Set.BijOn TC.branchLabel ↑TC.fullBranches ↑TC.terminalMinimumLabels := by
  exact
    TC.branchLabel_bijOn_terminalMinimumLabels_of_countDatumClassifier_and_branchLabel_injOn
      ha hselected hinjBranchLabel
      (TC.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_widthBound
        cut pOf alphaOf layerWidth T hselected hsource hT hblock hlast
        hwidth_le hk hne_base hinjCountDatum)

/-- Branch-label injectivity from supplied Eq5 alpha-indexed nonbase branch
data.

The proof separates the base branch from all nonbase branches by the explicit
`hbase_ne` hypothesis.  For two nonbase branches, equality of Sigma labels
puts their source coordinates in the same selected block, and the displayed
Eq5 label formula reduces equality to supplied alpha injectivity on that
block.  This does not construct the branch family or prove counted-datum
injectivity. -/
theorem branchLabel_injOn_of_eq5AlphaIndexed_nonbase
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (alphaOf : β → ℕ)
    (halpha_inj :
      ∀ j ∈ Finset.Icc 1 N,
        Set.InjOn alphaOf ↑(TC.family.branches j))
    (hblock :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        cut.block j (TC.branchLabel (some b)).1)
    (hlabel :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        ((TC.branchLabel (some b)).2 : ℤ) =
          aoyagiHtildeUpperNat (N + 1) a M m j + 1 - (alphaOf b : ℤ))
    (hbase_ne :
      ∀ {b : β}, some b ∈ TC.fullBranches →
        TC.branchLabel none ≠ TC.branchLabel (some b)) :
    Set.InjOn TC.branchLabel ↑TC.fullBranches := by
  refine TC.branchLabel_injOn_fullBranches_of_some_injOn ?_ hbase_ne
  intro b hb c hc hbc_label
  have hb_nonbase :
      some b ∈ TC.family.toAoyagiLemma5SuppliedNonbaseFamily.fullBranches := by
    simpa [AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches,
      AoyagiLemma5SuppliedAdmissibleFamily.fullBranches] using hb
  have hc_nonbase :
      some c ∈ TC.family.toAoyagiLemma5SuppliedNonbaseFamily.fullBranches := by
    simpa [AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches,
      AoyagiLemma5SuppliedAdmissibleFamily.fullBranches] using hc
  rcases
    (AoyagiLemma5SuppliedNonbaseFamily.some_mem_fullBranches_iff
      TC.family.toAoyagiLemma5SuppliedNonbaseFamily).mp hb_nonbase
    with ⟨j, hj, hbj⟩
  rcases
    (AoyagiLemma5SuppliedNonbaseFamily.some_mem_fullBranches_iff
      TC.family.toAoyagiLemma5SuppliedNonbaseFamily).mp hc_nonbase
    with ⟨k, hk, hck⟩
  have hsource_eq :
      (TC.branchLabel (some b)).1 = (TC.branchLabel (some c)).1 :=
    congrArg Sigma.fst hbc_label
  have hblock_b : cut.block j (TC.branchLabel (some b)).1 :=
    hblock j hj b hbj
  have hblock_c_same : cut.block k (TC.branchLabel (some b)).1 := by
    rw [hsource_eq]
    exact hblock k hk c hck
  have hjk : j = k := cut.block_index_unique hblock_b hblock_c_same
  have hck_j : c ∈ TC.family.branches j := by
    simpa [hjk] using hck
  exact
    (aoyagiLemma5Eq5_alphaIndexedBranchLabel_injOn
      (N + 1) a j M m (TC.family.branches j) alphaOf
      (fun b : β ↦ TC.branchLabel (some b))
      (halpha_inj j hj) (hlabel j hj)) hbj hck_j hbc_label

/-- A terminal-endpoint base label is distinct from every nonbase Eq5 branch
label whose source coordinate lies in its selected block.

This removes only the base/nonbase separation hypothesis from the finite
branch-label injection adapter.  It does not prove nonbase branch construction
or no-extra terminal-minimum coverage. -/
theorem branchLabel_none_ne_some_of_terminalEndpointLabel_and_nonbaseBlock
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (hbaseLabel :
      TC.branchLabel none =
        ((Sigma.mk (cut.point (N + 1) - 1) 1) : Σ _ : ℕ, ℕ))
    (hbranchBlock :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        cut.block j (TC.branchLabel (some b)).1) :
    ∀ {b : β}, some b ∈ TC.fullBranches →
      TC.branchLabel none ≠ TC.branchLabel (some b) := by
  intro b hb heq
  have hb_nonbase :
      some b ∈ TC.family.toAoyagiLemma5SuppliedNonbaseFamily.fullBranches := by
    simpa [AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches,
      AoyagiLemma5SuppliedAdmissibleFamily.fullBranches] using hb
  rcases
    (AoyagiLemma5SuppliedNonbaseFamily.some_mem_fullBranches_iff
      TC.family.toAoyagiLemma5SuppliedNonbaseFamily).mp hb_nonbase
    with ⟨j, hj, hbj⟩
  have hsource :
      (TC.branchLabel (some b)).1 = cut.point (N + 1) - 1 := by
    have h :=
      congrArg Sigma.fst (hbaseLabel.symm.trans heq)
    simpa using h.symm
  have hbad : cut.block j (cut.point (N + 1) - 1) := by
    rw [← hsource]
    exact hbranchBlock j hj b hbj
  exact (cut.not_block_terminalEndpoint (b := j)) hbad

/-- Branch-label injectivity from Eq5 alpha-indexed nonbase branch data and an
explicit terminal-endpoint base label. -/
theorem branchLabel_injOn_of_eq5AlphaIndexed_nonbase_terminalEndpointBase
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (alphaOf : β → ℕ)
    (halpha_inj :
      ∀ j ∈ Finset.Icc 1 N,
        Set.InjOn alphaOf ↑(TC.family.branches j))
    (hbranchBlock :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        cut.block j (TC.branchLabel (some b)).1)
    (hbranchLabelFormula :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        ((TC.branchLabel (some b)).2 : ℤ) =
          aoyagiHtildeUpperNat (N + 1) a M m j + 1 -
            (alphaOf b : ℤ))
    (hbaseLabel :
      TC.branchLabel none =
        ((Sigma.mk (cut.point (N + 1) - 1) 1) : Σ _ : ℕ, ℕ)) :
    Set.InjOn TC.branchLabel ↑TC.fullBranches :=
  TC.branchLabel_injOn_of_eq5AlphaIndexed_nonbase cut alphaOf
    halpha_inj hbranchBlock hbranchLabelFormula
    (TC.branchLabel_none_ne_some_of_terminalEndpointLabel_and_nonbaseBlock
      cut hbaseLabel hbranchBlock)

/-- Branch-label injectivity from supplied nonbase value-label data.

For two nonbase branches, equality of Sigma labels puts their source
coordinates in the same selected block.  The supplied value-label relation
then reduces equality of labels to equality of branch values, and the supplied
family's one-coordinate value injectivity identifies the branches.  This does
not construct the branch family or prove base/nonbase separation. -/
theorem branchLabel_injOn_of_nonbase_valueLabel
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (hbranchBlock :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        cut.block j (TC.branchLabel (some b)).1)
    (hvalueLabel :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.family.value b = ((TC.branchLabel (some b)).2 : ℤ) - 1)
    (hbase_ne :
      ∀ {b : β}, some b ∈ TC.fullBranches →
        TC.branchLabel none ≠ TC.branchLabel (some b)) :
    Set.InjOn TC.branchLabel ↑TC.fullBranches := by
  refine TC.branchLabel_injOn_fullBranches_of_some_injOn ?_ hbase_ne
  intro b hb c hc hbc_label
  have hb_nonbase :
      some b ∈ TC.family.toAoyagiLemma5SuppliedNonbaseFamily.fullBranches := by
    simpa [AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches,
      AoyagiLemma5SuppliedAdmissibleFamily.fullBranches] using hb
  have hc_nonbase :
      some c ∈ TC.family.toAoyagiLemma5SuppliedNonbaseFamily.fullBranches := by
    simpa [AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches,
      AoyagiLemma5SuppliedAdmissibleFamily.fullBranches] using hc
  rcases
    (AoyagiLemma5SuppliedNonbaseFamily.some_mem_fullBranches_iff
      TC.family.toAoyagiLemma5SuppliedNonbaseFamily).mp hb_nonbase
    with ⟨j, hj, hbj⟩
  rcases
    (AoyagiLemma5SuppliedNonbaseFamily.some_mem_fullBranches_iff
      TC.family.toAoyagiLemma5SuppliedNonbaseFamily).mp hc_nonbase
    with ⟨k, hk, hck⟩
  have hsource_eq :
      (TC.branchLabel (some b)).1 = (TC.branchLabel (some c)).1 :=
    congrArg Sigma.fst hbc_label
  have hblock_b : cut.block j (TC.branchLabel (some b)).1 :=
    hbranchBlock j hj b hbj
  have hblock_c_same : cut.block k (TC.branchLabel (some b)).1 := by
    rw [hsource_eq]
    exact hbranchBlock k hk c hck
  have hjk : j = k := cut.block_index_unique hblock_b hblock_c_same
  have hck_j : c ∈ TC.family.branches j := by
    simpa [hjk] using hck
  have hlabel_second :
      (TC.branchLabel (some b)).2 = (TC.branchLabel (some c)).2 :=
    congrArg Sigma.snd hbc_label
  have hvalue_eq : TC.family.value b = TC.family.value c := by
    rw [hvalueLabel j hj b hbj, hvalueLabel j hj c hck_j]
    exact congrArg (fun q : ℕ ↦ (q : ℤ) - 1) hlabel_second
  exact TC.family.value_injective hj hbj hck_j hvalue_eq

/-- Branch-label injectivity from supplied nonbase value-label data and an
explicit terminal-endpoint base label. -/
theorem branchLabel_injOn_of_nonbase_valueLabel_terminalEndpointBase
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (hbranchBlock :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        cut.block j (TC.branchLabel (some b)).1)
    (hvalueLabel :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.family.value b = ((TC.branchLabel (some b)).2 : ℤ) - 1)
    (hbaseLabel :
      TC.branchLabel none =
        ((Sigma.mk (cut.point (N + 1) - 1) 1) : Σ _ : ℕ, ℕ)) :
    Set.InjOn TC.branchLabel ↑TC.fullBranches :=
  TC.branchLabel_injOn_of_nonbase_valueLabel cut hbranchBlock hvalueLabel
    (TC.branchLabel_none_ne_some_of_terminalEndpointLabel_and_nonbaseBlock
      cut hbaseLabel hbranchBlock)

/-- Selected-block membership for branch labels whose source coordinate is a
supplied selected-block left endpoint.

This is a structured way to supply the `hbranchBlock` input used by the
branch-label injectivity adapters.  It does not construct the branch-coordinate
map or prove that the terminal candidate labels are source-produced. -/
theorem branchBlock_of_branchCoord_leftEndpoint
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (branchCoord : β → ℕ)
    (hbranchCoord :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        branchCoord b = j)
    (hbranchS :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.branchS (some b) = cut.point (branchCoord b) - 1) :
    ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
      cut.block j (TC.branchLabel (some b)).1 := by
  intro j hj b hb
  have hj_lt : j < N + 1 := by
    have hj_le : j ≤ N := (Finset.mem_Icc.mp hj).2
    omega
  have hleft : cut.block j (cut.point j - 1) :=
    cut.leftEndpoint_mem_block hj_lt
  have hcoord : branchCoord b = j := hbranchCoord j hj b hb
  have hsource : TC.branchS (some b) = cut.point j - 1 := by
    rw [hbranchS j hj b hb, hcoord]
  simpa [AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel, hsource]
    using hleft

/-- Transport nonbase branch-coordinate correctness from the strictest Eq5
endpoint supplied-family constructor into a terminal-candidate family.

The equality hypothesis is the boundary: it explicitly identifies the
terminal family's nonbase supplied family with the endpoint constructor.  This
does not construct the endpoint records or prove source-label legality. -/
theorem branchCoord_of_toNonbase_eq_eq5EndpointCoverage
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (strictBranches : ℕ → Finset β) (alphaOf : β → ℕ)
    (value : β → ℤ) (upper lower : ℕ → β) (baseValue : ℕ → ℤ)
    (ha : a ≤ N + 1)
    (baseValue_mem :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        baseValue j ∈ aoyagiHtildeIntervalValueSetNat (N + 1) a M m j)
    (halpha_image :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        (strictBranches j).image alphaOf =
          aoyagiLemma5Eq5AlphaDomain (N + 1) a j)
    (hvalue :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
        ∀ b ∈ strictBranches j,
          value b = aoyagiHtildeUpperNat (N + 1) a M m j - (alphaOf b : ℤ))
    (hupper :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        value (upper j) = aoyagiHtildeUpperNat (N + 1) a M m j)
    (hlower :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) → j ≤ a →
        j ≤ (N + 1) - a →
          value (lower j) = aoyagiHtildeLowerNat (N + 1) a M m j)
    (halpha_inj :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
        Set.InjOn alphaOf ↑(strictBranches j))
    (branchCoord : β → ℕ)
    (hstrictCoord :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
        ∀ b ∈ strictBranches j, branchCoord b = j)
    (hupperCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        branchCoord (upper j) = j)
    (hlowerCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) → j ≤ a →
        j ≤ (N + 1) - a → branchCoord (lower j) = j)
    (hfamily :
      TC.family.toAoyagiLemma5SuppliedNonbaseFamily =
        ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord
          (ell := N + 1) (a := a) (M := M) (m := m)
          strictBranches alphaOf value upper lower baseValue ha
          baseValue_mem halpha_image hvalue hupper hlower halpha_inj
          branchCoord hstrictCoord hupperCoord hlowerCoord) :
    ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
      branchCoord b = j := by
  intro j hj b hb
  have hj_endpoint : j ∈ Finset.Icc 1 ((N + 1) - 1) := by
    simpa using hj
  let Fendpoint : AoyagiLemma5SuppliedNonbaseFamily β (N + 1) a M m :=
    ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord
      (ell := N + 1) (a := a) (M := M) (m := m)
      strictBranches alphaOf value upper lower baseValue ha baseValue_mem
      halpha_image hvalue hupper hlower halpha_inj branchCoord
      hstrictCoord hupperCoord hlowerCoord
  have hb_endpoint : b ∈ Fendpoint.branches j := by
    change b ∈ TC.family.toAoyagiLemma5SuppliedNonbaseFamily.branches j at hb
    simpa [Fendpoint, hfamily] using hb
  exact
    ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord_branchCoord_eq
      (ell := N + 1) (a := a) (M := M) (m := m)
      strictBranches alphaOf value upper lower baseValue ha baseValue_mem
      halpha_image hvalue hupper hlower halpha_inj branchCoord
      hstrictCoord hupperCoord hlowerCoord hj_endpoint hb_endpoint

/-- Selected-block membership from an explicit identification of the terminal
nonbase family with the strictest Eq5 endpoint supplied-family constructor.

The branch source-label formula remains supplied separately through
`hbranchS`. -/
theorem branchBlock_of_toNonbase_eq_eq5EndpointCoverage_leftEndpoint
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (strictBranches : ℕ → Finset β) (alphaOf : β → ℕ)
    (value : β → ℤ) (upper lower : ℕ → β) (baseValue : ℕ → ℤ)
    (ha : a ≤ N + 1)
    (baseValue_mem :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        baseValue j ∈ aoyagiHtildeIntervalValueSetNat (N + 1) a M m j)
    (halpha_image :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        (strictBranches j).image alphaOf =
          aoyagiLemma5Eq5AlphaDomain (N + 1) a j)
    (hvalue :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
        ∀ b ∈ strictBranches j,
          value b = aoyagiHtildeUpperNat (N + 1) a M m j - (alphaOf b : ℤ))
    (hupper :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        value (upper j) = aoyagiHtildeUpperNat (N + 1) a M m j)
    (hlower :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) → j ≤ a →
        j ≤ (N + 1) - a →
          value (lower j) = aoyagiHtildeLowerNat (N + 1) a M m j)
    (halpha_inj :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
        Set.InjOn alphaOf ↑(strictBranches j))
    (branchCoord : β → ℕ)
    (hstrictCoord :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
        ∀ b ∈ strictBranches j, branchCoord b = j)
    (hupperCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        branchCoord (upper j) = j)
    (hlowerCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) → j ≤ a →
        j ≤ (N + 1) - a → branchCoord (lower j) = j)
    (hfamily :
      TC.family.toAoyagiLemma5SuppliedNonbaseFamily =
        ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord
          (ell := N + 1) (a := a) (M := M) (m := m)
          strictBranches alphaOf value upper lower baseValue ha
          baseValue_mem halpha_image hvalue hupper hlower halpha_inj
          branchCoord hstrictCoord hupperCoord hlowerCoord)
    (hbranchS :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.branchS (some b) = cut.point (branchCoord b) - 1) :
    ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
      cut.block j (TC.branchLabel (some b)).1 :=
  TC.branchBlock_of_branchCoord_leftEndpoint cut branchCoord
    (TC.branchCoord_of_toNonbase_eq_eq5EndpointCoverage
      strictBranches alphaOf value upper lower baseValue ha baseValue_mem
      halpha_image hvalue hupper hlower halpha_inj branchCoord hstrictCoord
      hupperCoord hlowerCoord hfamily)
    hbranchS

/-- Convert a supplied `branchK`/value relation into the Sigma-label
value-label relation used by `branchLabel_injOn_of_nonbase_valueLabel`. -/
theorem valueLabel_of_branchK_value
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (hbranchK :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.family.value b = (TC.branchK (some b) : ℤ) - 1) :
    ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
      TC.family.value b = ((TC.branchLabel (some b)).2 : ℤ) - 1 := by
  intro j hj b hb
  simpa [AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel]
    using hbranchK j hj b hb

/-- Branch-label injectivity from supplied branch-coordinate left-endpoint
labels, supplied branch-value labels, and an explicit terminal-endpoint base
label. -/
theorem branchLabel_injOn_of_branchCoord_leftEndpoint_branchK_value_terminalEndpointBase
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (branchCoord : β → ℕ)
    (hbranchCoord :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        branchCoord b = j)
    (hbranchS :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.branchS (some b) = cut.point (branchCoord b) - 1)
    (hbranchK :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.family.value b = (TC.branchK (some b) : ℤ) - 1)
    (hbaseLabel :
      TC.branchLabel none =
        ((Sigma.mk (cut.point (N + 1) - 1) 1) : Σ _ : ℕ, ℕ)) :
    Set.InjOn TC.branchLabel ↑TC.fullBranches :=
  TC.branchLabel_injOn_of_nonbase_valueLabel_terminalEndpointBase cut
    (TC.branchBlock_of_branchCoord_leftEndpoint
      cut branchCoord hbranchCoord hbranchS)
    (TC.valueLabel_of_branchK_value hbranchK)
    hbaseLabel

/-- Terminal-minimum exactness from Eq5 own-block common-domain payloads and
explicit alpha-indexed branch-label injection data. -/
theorem terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_alphaIndexedBranch_cardSqueeze
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (ha : a ≤ N + 1)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (pOf labelAlphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (branchAlphaOf : β → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (hselected :
      (∑ i : Fin (N + 2), m i) = ((N + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (N + 2),
      ((N + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (N + 2), m j)
    (hT : ∀ label ∈ TC.terminalMinimumLabels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        (N + 1) a (pOf label) (labelAlphaOf label) M m cut
        (layerWidth label) (T label))
    (hlabelBlock : ∀ label ∈ TC.terminalMinimumLabels,
      cut.block (pOf label) label.1)
    (hlast : cut.point (N + 1) ≤ L + 1)
    (hwidth_le : ∀ label ∈ TC.terminalMinimumLabels,
      aoyagiSelectedWidthNat (N + 1) m (pOf label) ≤
        (width (label.1 + 1) : ℤ))
    (hlabelFormula : ∀ label ∈ TC.terminalMinimumLabels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat (N + 1) a M m (pOf label) + 1 -
          (labelAlphaOf label : ℤ))
    (hlabel_ne_base : ∀ label ∈ TC.terminalMinimumLabels,
      T label label.1 ≠ TC.family.baseValue (pOf label))
    (hinjCountDatum :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (some (Sigma.mk (pOf label) (T label label.1)) :
            AoyagiLemma5CountDatum))
        ↑TC.terminalMinimumLabels)
    (hbranchAlpha_inj :
      ∀ j ∈ Finset.Icc 1 N,
        Set.InjOn branchAlphaOf ↑(TC.family.branches j))
    (hbranchBlock :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        cut.block j (TC.branchLabel (some b)).1)
    (hbranchLabelFormula :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        ((TC.branchLabel (some b)).2 : ℤ) =
          aoyagiHtildeUpperNat (N + 1) a M m j + 1 -
            (branchAlphaOf b : ℤ))
    (hbase_ne :
      ∀ {b : β}, some b ∈ TC.fullBranches →
        TC.branchLabel none ≠ TC.branchLabel (some b)) :
    TC.TerminalMinimumLabelExactness := by
  exact
    TC.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_cardSqueeze
      ha cut pOf labelAlphaOf layerWidth T hselected hsource hT
      hlabelBlock hlast hwidth_le hlabelFormula hlabel_ne_base
      hinjCountDatum
      (TC.branchLabel_injOn_of_eq5AlphaIndexed_nonbase cut branchAlphaOf
        hbranchAlpha_inj hbranchBlock hbranchLabelFormula hbase_ne)

/-- Exact terminal-minimum count from Eq5 own-block common-domain payloads and
explicit alpha-indexed branch-label injection data. -/
theorem terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_alphaIndexedBranch_cardSqueeze
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (ha : a ≤ N + 1)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (pOf labelAlphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (branchAlphaOf : β → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (hselected :
      (∑ i : Fin (N + 2), m i) = ((N + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (N + 2),
      ((N + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (N + 2), m j)
    (hT : ∀ label ∈ TC.terminalMinimumLabels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        (N + 1) a (pOf label) (labelAlphaOf label) M m cut
        (layerWidth label) (T label))
    (hlabelBlock : ∀ label ∈ TC.terminalMinimumLabels,
      cut.block (pOf label) label.1)
    (hlast : cut.point (N + 1) ≤ L + 1)
    (hwidth_le : ∀ label ∈ TC.terminalMinimumLabels,
      aoyagiSelectedWidthNat (N + 1) m (pOf label) ≤
        (width (label.1 + 1) : ℤ))
    (hlabelFormula : ∀ label ∈ TC.terminalMinimumLabels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat (N + 1) a M m (pOf label) + 1 -
          (labelAlphaOf label : ℤ))
    (hlabel_ne_base : ∀ label ∈ TC.terminalMinimumLabels,
      T label label.1 ≠ TC.family.baseValue (pOf label))
    (hinjCountDatum :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (some (Sigma.mk (pOf label) (T label label.1)) :
            AoyagiLemma5CountDatum))
        ↑TC.terminalMinimumLabels)
    (hbranchAlpha_inj :
      ∀ j ∈ Finset.Icc 1 N,
        Set.InjOn branchAlphaOf ↑(TC.family.branches j))
    (hbranchBlock :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        cut.block j (TC.branchLabel (some b)).1)
    (hbranchLabelFormula :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        ((TC.branchLabel (some b)).2 : ℤ) =
          aoyagiHtildeUpperNat (N + 1) a M m j + 1 -
            (branchAlphaOf b : ℤ))
    (hbase_ne :
      ∀ {b : β}, some b ∈ TC.fullBranches →
        TC.branchLabel none ≠ TC.branchLabel (some b)) :
    TC.terminalMinimumLabels.card = a * (N + 1 - a) + 1 := by
  exact
    TC.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_cardSqueeze
      ha cut pOf labelAlphaOf layerWidth T hselected hsource hT
      hlabelBlock hlast hwidth_le hlabelFormula hlabel_ne_base
      hinjCountDatum
      (TC.branchLabel_injOn_of_eq5AlphaIndexed_nonbase cut branchAlphaOf
        hbranchAlpha_inj hbranchBlock hbranchLabelFormula hbase_ne)

/-- Terminal-minimum exactness from Eq5 own-block common-domain payloads,
terminal `(p, alpha)` injectivity, and alpha-indexed branch data with an
explicit terminal-endpoint base label.

This removes only the opaque counted-datum injectivity and base/nonbase
branch-label separation hypotheses from the preceding alpha-indexed wrapper.
It does not construct Eq5 payloads, prove `(p, alpha)` injectivity from
source, or prove no-extra terminal-minimum coverage. -/
theorem
    terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_endpointBase_cardSqueeze
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (ha : a ≤ N + 1)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (pOf labelAlphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (branchAlphaOf : β → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (hselected :
      (∑ i : Fin (N + 2), m i) = ((N + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (N + 2),
      ((N + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (N + 2), m j)
    (hT : ∀ label ∈ TC.terminalMinimumLabels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        (N + 1) a (pOf label) (labelAlphaOf label) M m cut
        (layerWidth label) (T label))
    (hlabelBlock : ∀ label ∈ TC.terminalMinimumLabels,
      cut.block (pOf label) label.1)
    (hlast : cut.point (N + 1) ≤ L + 1)
    (hwidth_le : ∀ label ∈ TC.terminalMinimumLabels,
      aoyagiSelectedWidthNat (N + 1) m (pOf label) ≤
        (width (label.1 + 1) : ℤ))
    (hlabelFormula : ∀ label ∈ TC.terminalMinimumLabels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat (N + 1) a M m (pOf label) + 1 -
          (labelAlphaOf label : ℤ))
    (hlabel_ne_base : ∀ label ∈ TC.terminalMinimumLabels,
      T label label.1 ≠ TC.family.baseValue (pOf label))
    (hpAlpha_inj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (Sigma.mk (pOf label) (labelAlphaOf label) : Σ _ : ℕ, ℕ))
        ↑TC.terminalMinimumLabels)
    (hbranchAlpha_inj :
      ∀ j ∈ Finset.Icc 1 N,
        Set.InjOn branchAlphaOf ↑(TC.family.branches j))
    (hbranchBlock :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        cut.block j (TC.branchLabel (some b)).1)
    (hbranchLabelFormula :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        ((TC.branchLabel (some b)).2 : ℤ) =
          aoyagiHtildeUpperNat (N + 1) a M m j + 1 -
            (branchAlphaOf b : ℤ))
    (hbaseLabel :
      TC.branchLabel none =
        ((Sigma.mk (cut.point (N + 1) - 1) 1) : Σ _ : ℕ, ℕ)) :
    TC.TerminalMinimumLabelExactness := by
  exact
    TC.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_cardSqueeze
      ha cut pOf labelAlphaOf layerWidth T hselected hsource hT
      hlabelBlock hlast hwidth_le hlabelFormula hlabel_ne_base
      (TC.terminalMinimumCountDatum_injOn_of_eq5OwnBlock_pAlpha_injOn
        cut pOf labelAlphaOf layerWidth T hT hlabelBlock hpAlpha_inj)
      (TC.branchLabel_injOn_of_eq5AlphaIndexed_nonbase_terminalEndpointBase
        cut branchAlphaOf hbranchAlpha_inj hbranchBlock hbranchLabelFormula
        hbaseLabel)

/-- Exact terminal-minimum count from Eq5 own-block common-domain payloads,
terminal `(p, alpha)` injectivity, and alpha-indexed branch data with an
explicit terminal-endpoint base label.

This is the count version of
`terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_endpointBase_cardSqueeze`.
It is still a conditional finite cardinal-squeeze theorem, not a source
construction of the Lemma 5 terminal branch family. -/
theorem
    terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_endpointBase_cardSqueeze
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (ha : a ≤ N + 1)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (pOf labelAlphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (branchAlphaOf : β → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (hselected :
      (∑ i : Fin (N + 2), m i) = ((N + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (N + 2),
      ((N + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (N + 2), m j)
    (hT : ∀ label ∈ TC.terminalMinimumLabels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        (N + 1) a (pOf label) (labelAlphaOf label) M m cut
        (layerWidth label) (T label))
    (hlabelBlock : ∀ label ∈ TC.terminalMinimumLabels,
      cut.block (pOf label) label.1)
    (hlast : cut.point (N + 1) ≤ L + 1)
    (hwidth_le : ∀ label ∈ TC.terminalMinimumLabels,
      aoyagiSelectedWidthNat (N + 1) m (pOf label) ≤
        (width (label.1 + 1) : ℤ))
    (hlabelFormula : ∀ label ∈ TC.terminalMinimumLabels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat (N + 1) a M m (pOf label) + 1 -
          (labelAlphaOf label : ℤ))
    (hlabel_ne_base : ∀ label ∈ TC.terminalMinimumLabels,
      T label label.1 ≠ TC.family.baseValue (pOf label))
    (hpAlpha_inj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (Sigma.mk (pOf label) (labelAlphaOf label) : Σ _ : ℕ, ℕ))
        ↑TC.terminalMinimumLabels)
    (hbranchAlpha_inj :
      ∀ j ∈ Finset.Icc 1 N,
        Set.InjOn branchAlphaOf ↑(TC.family.branches j))
    (hbranchBlock :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        cut.block j (TC.branchLabel (some b)).1)
    (hbranchLabelFormula :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        ((TC.branchLabel (some b)).2 : ℤ) =
          aoyagiHtildeUpperNat (N + 1) a M m j + 1 -
            (branchAlphaOf b : ℤ))
    (hbaseLabel :
      TC.branchLabel none =
        ((Sigma.mk (cut.point (N + 1) - 1) 1) : Σ _ : ℕ, ℕ)) :
    TC.terminalMinimumLabels.card = a * (N + 1 - a) + 1 := by
  exact
    TC.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_cardSqueeze
      ha cut pOf labelAlphaOf layerWidth T hselected hsource hT
      hlabelBlock hlast hwidth_le hlabelFormula hlabel_ne_base
      (TC.terminalMinimumCountDatum_injOn_of_eq5OwnBlock_pAlpha_injOn
        cut pOf labelAlphaOf layerWidth T hT hlabelBlock hpAlpha_inj)
      (TC.branchLabel_injOn_of_eq5AlphaIndexed_nonbase_terminalEndpointBase
        cut branchAlphaOf hbranchAlpha_inj hbranchBlock hbranchLabelFormula
        hbaseLabel)

/-- Terminal-minimum exactness from Eq5 own-block common-domain payloads,
terminal `(p, alpha)` injectivity, and supplied nonbase value-label data.

This replaces the branch alpha-injectivity/formula inputs of the alpha-indexed
wrapper by the value-label relation
`TC.family.value b = (TC.branchLabel (some b)).2 - 1`.  It remains a
conditional finite cardinal-squeeze theorem. -/
theorem
    terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (ha : a ≤ N + 1)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (pOf labelAlphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (hselected :
      (∑ i : Fin (N + 2), m i) = ((N + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (N + 2),
      ((N + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (N + 2), m j)
    (hT : ∀ label ∈ TC.terminalMinimumLabels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        (N + 1) a (pOf label) (labelAlphaOf label) M m cut
        (layerWidth label) (T label))
    (hlabelBlock : ∀ label ∈ TC.terminalMinimumLabels,
      cut.block (pOf label) label.1)
    (hlast : cut.point (N + 1) ≤ L + 1)
    (hwidth_le : ∀ label ∈ TC.terminalMinimumLabels,
      aoyagiSelectedWidthNat (N + 1) m (pOf label) ≤
        (width (label.1 + 1) : ℤ))
    (hlabelFormula : ∀ label ∈ TC.terminalMinimumLabels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat (N + 1) a M m (pOf label) + 1 -
          (labelAlphaOf label : ℤ))
    (hlabel_ne_base : ∀ label ∈ TC.terminalMinimumLabels,
      T label label.1 ≠ TC.family.baseValue (pOf label))
    (hpAlpha_inj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (Sigma.mk (pOf label) (labelAlphaOf label) : Σ _ : ℕ, ℕ))
        ↑TC.terminalMinimumLabels)
    (hbranchBlock :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        cut.block j (TC.branchLabel (some b)).1)
    (hvalueLabel :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.family.value b = ((TC.branchLabel (some b)).2 : ℤ) - 1)
    (hbaseLabel :
      TC.branchLabel none =
        ((Sigma.mk (cut.point (N + 1) - 1) 1) : Σ _ : ℕ, ℕ)) :
    TC.TerminalMinimumLabelExactness := by
  exact
    TC.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_cardSqueeze
      ha cut pOf labelAlphaOf layerWidth T hselected hsource hT
      hlabelBlock hlast hwidth_le hlabelFormula hlabel_ne_base
      (TC.terminalMinimumCountDatum_injOn_of_eq5OwnBlock_pAlpha_injOn
        cut pOf labelAlphaOf layerWidth T hT hlabelBlock hpAlpha_inj)
      (TC.branchLabel_injOn_of_nonbase_valueLabel_terminalEndpointBase
        cut hbranchBlock hvalueLabel hbaseLabel)

/-- Exact terminal-minimum count from Eq5 own-block common-domain payloads,
terminal `(p, alpha)` injectivity, and supplied nonbase value-label data.

This is the count version of
`terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze`.
It is still conditional on supplied terminal Eq5 payloads and supplied
terminal `(p, alpha)` injectivity. -/
theorem
    terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (ha : a ≤ N + 1)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (pOf labelAlphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (hselected :
      (∑ i : Fin (N + 2), m i) = ((N + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (N + 2),
      ((N + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (N + 2), m j)
    (hT : ∀ label ∈ TC.terminalMinimumLabels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        (N + 1) a (pOf label) (labelAlphaOf label) M m cut
        (layerWidth label) (T label))
    (hlabelBlock : ∀ label ∈ TC.terminalMinimumLabels,
      cut.block (pOf label) label.1)
    (hlast : cut.point (N + 1) ≤ L + 1)
    (hwidth_le : ∀ label ∈ TC.terminalMinimumLabels,
      aoyagiSelectedWidthNat (N + 1) m (pOf label) ≤
        (width (label.1 + 1) : ℤ))
    (hlabelFormula : ∀ label ∈ TC.terminalMinimumLabels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat (N + 1) a M m (pOf label) + 1 -
          (labelAlphaOf label : ℤ))
    (hlabel_ne_base : ∀ label ∈ TC.terminalMinimumLabels,
      T label label.1 ≠ TC.family.baseValue (pOf label))
    (hpAlpha_inj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (Sigma.mk (pOf label) (labelAlphaOf label) : Σ _ : ℕ, ℕ))
        ↑TC.terminalMinimumLabels)
    (hbranchBlock :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        cut.block j (TC.branchLabel (some b)).1)
    (hvalueLabel :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.family.value b = ((TC.branchLabel (some b)).2 : ℤ) - 1)
    (hbaseLabel :
      TC.branchLabel none =
        ((Sigma.mk (cut.point (N + 1) - 1) 1) : Σ _ : ℕ, ℕ)) :
    TC.terminalMinimumLabels.card = a * (N + 1 - a) + 1 := by
  exact
    TC.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_cardSqueeze
      ha cut pOf labelAlphaOf layerWidth T hselected hsource hT
      hlabelBlock hlast hwidth_le hlabelFormula hlabel_ne_base
      (TC.terminalMinimumCountDatum_injOn_of_eq5OwnBlock_pAlpha_injOn
        cut pOf labelAlphaOf layerWidth T hT hlabelBlock hpAlpha_inj)
      (TC.branchLabel_injOn_of_nonbase_valueLabel_terminalEndpointBase
        cut hbranchBlock hvalueLabel hbaseLabel)

/-- Terminal-minimum exactness from Eq5 own-block common-domain payloads,
terminal `(p, alpha)` injectivity, and branch-coordinate left-endpoint/value
label data.

This is a convenience wrapper around
`terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze`.
It derives selected-block membership from a supplied coordinate map and
left-endpoint formula for `branchS`, and derives the value-label relation from
the supplied `branchK`/value relation. -/
theorem
    terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_branchCoordVal_cardSqueeze
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (ha : a ≤ N + 1)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (pOf labelAlphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (hselected :
      (∑ i : Fin (N + 2), m i) = ((N + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (N + 2),
      ((N + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (N + 2), m j)
    (hT : ∀ label ∈ TC.terminalMinimumLabels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        (N + 1) a (pOf label) (labelAlphaOf label) M m cut
        (layerWidth label) (T label))
    (hlabelBlock : ∀ label ∈ TC.terminalMinimumLabels,
      cut.block (pOf label) label.1)
    (hlast : cut.point (N + 1) ≤ L + 1)
    (hwidth_le : ∀ label ∈ TC.terminalMinimumLabels,
      aoyagiSelectedWidthNat (N + 1) m (pOf label) ≤
        (width (label.1 + 1) : ℤ))
    (hlabelFormula : ∀ label ∈ TC.terminalMinimumLabels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat (N + 1) a M m (pOf label) + 1 -
          (labelAlphaOf label : ℤ))
    (hlabel_ne_base : ∀ label ∈ TC.terminalMinimumLabels,
      T label label.1 ≠ TC.family.baseValue (pOf label))
    (hpAlpha_inj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (Sigma.mk (pOf label) (labelAlphaOf label) : Σ _ : ℕ, ℕ))
        ↑TC.terminalMinimumLabels)
    (branchCoord : β → ℕ)
    (hbranchCoord :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        branchCoord b = j)
    (hbranchS :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.branchS (some b) = cut.point (branchCoord b) - 1)
    (hbranchK :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.family.value b = (TC.branchK (some b) : ℤ) - 1)
    (hbaseLabel :
      TC.branchLabel none =
        ((Sigma.mk (cut.point (N + 1) - 1) 1) : Σ _ : ℕ, ℕ)) :
    TC.TerminalMinimumLabelExactness := by
  exact
    TC.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze
      ha cut pOf labelAlphaOf layerWidth T hselected hsource hT
      hlabelBlock hlast hwidth_le hlabelFormula hlabel_ne_base
      hpAlpha_inj
      (TC.branchBlock_of_branchCoord_leftEndpoint
        cut branchCoord hbranchCoord hbranchS)
      (TC.valueLabel_of_branchK_value hbranchK)
      hbaseLabel

/-- Exact terminal-minimum count from Eq5 own-block common-domain payloads,
terminal `(p, alpha)` injectivity, and branch-coordinate left-endpoint/value
label data.

This is the count version of
`terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_branchCoordVal_cardSqueeze`.
It remains conditional on the supplied terminal Eq5 payloads and supplied
branch-coordinate/value-label data. -/
theorem
    terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_branchCoordVal_cardSqueeze
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (ha : a ≤ N + 1)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (pOf labelAlphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (hselected :
      (∑ i : Fin (N + 2), m i) = ((N + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (N + 2),
      ((N + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (N + 2), m j)
    (hT : ∀ label ∈ TC.terminalMinimumLabels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        (N + 1) a (pOf label) (labelAlphaOf label) M m cut
        (layerWidth label) (T label))
    (hlabelBlock : ∀ label ∈ TC.terminalMinimumLabels,
      cut.block (pOf label) label.1)
    (hlast : cut.point (N + 1) ≤ L + 1)
    (hwidth_le : ∀ label ∈ TC.terminalMinimumLabels,
      aoyagiSelectedWidthNat (N + 1) m (pOf label) ≤
        (width (label.1 + 1) : ℤ))
    (hlabelFormula : ∀ label ∈ TC.terminalMinimumLabels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat (N + 1) a M m (pOf label) + 1 -
          (labelAlphaOf label : ℤ))
    (hlabel_ne_base : ∀ label ∈ TC.terminalMinimumLabels,
      T label label.1 ≠ TC.family.baseValue (pOf label))
    (hpAlpha_inj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (Sigma.mk (pOf label) (labelAlphaOf label) : Σ _ : ℕ, ℕ))
        ↑TC.terminalMinimumLabels)
    (branchCoord : β → ℕ)
    (hbranchCoord :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        branchCoord b = j)
    (hbranchS :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.branchS (some b) = cut.point (branchCoord b) - 1)
    (hbranchK :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.family.value b = (TC.branchK (some b) : ℤ) - 1)
    (hbaseLabel :
      TC.branchLabel none =
        ((Sigma.mk (cut.point (N + 1) - 1) 1) : Σ _ : ℕ, ℕ)) :
    TC.terminalMinimumLabels.card = a * (N + 1 - a) + 1 := by
  exact
    TC.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze
      ha cut pOf labelAlphaOf layerWidth T hselected hsource hT
      hlabelBlock hlast hwidth_le hlabelFormula hlabel_ne_base
      hpAlpha_inj
      (TC.branchBlock_of_branchCoord_leftEndpoint
        cut branchCoord hbranchCoord hbranchS)
      (TC.valueLabel_of_branchK_value hbranchK)
      hbaseLabel

/-- Terminal-minimum exactness from Eq5 own-block common-domain payloads,
terminal `(p, alpha)` injectivity, and an explicit identification of the
terminal nonbase family with the strictest Eq5 endpoint supplied family.

The family equality supplies only branch-coordinate correctness through the
endpoint constructor.  Terminal Eq5 payloads, the branch source/value labels,
and source-backed/direct no-extra data still remain separate boundaries. -/
theorem terminalMinimumLabelExactness_of_eq5EndpointFamily_branchCoordVal_cardSqueeze
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (ha : a ≤ N + 1)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (pOf labelAlphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (strictBranches : ℕ → Finset β) (alphaOf : β → ℕ)
    (value : β → ℤ) (upper lower : ℕ → β) (baseValue : ℕ → ℤ)
    (hselected :
      (∑ i : Fin (N + 2), m i) = ((N + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (N + 2),
      ((N + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (N + 2), m j)
    (hT : ∀ label ∈ TC.terminalMinimumLabels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        (N + 1) a (pOf label) (labelAlphaOf label) M m cut
        (layerWidth label) (T label))
    (hlabelBlock : ∀ label ∈ TC.terminalMinimumLabels,
      cut.block (pOf label) label.1)
    (hlast : cut.point (N + 1) ≤ L + 1)
    (hwidth_le : ∀ label ∈ TC.terminalMinimumLabels,
      aoyagiSelectedWidthNat (N + 1) m (pOf label) ≤
        (width (label.1 + 1) : ℤ))
    (hlabelFormula : ∀ label ∈ TC.terminalMinimumLabels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat (N + 1) a M m (pOf label) + 1 -
          (labelAlphaOf label : ℤ))
    (hlabel_ne_base : ∀ label ∈ TC.terminalMinimumLabels,
      T label label.1 ≠ TC.family.baseValue (pOf label))
    (hpAlpha_inj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (Sigma.mk (pOf label) (labelAlphaOf label) : Σ _ : ℕ, ℕ))
        ↑TC.terminalMinimumLabels)
    (baseValue_mem :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        baseValue j ∈ aoyagiHtildeIntervalValueSetNat (N + 1) a M m j)
    (halpha_image :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        (strictBranches j).image alphaOf =
          aoyagiLemma5Eq5AlphaDomain (N + 1) a j)
    (hvalue :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
        ∀ b ∈ strictBranches j,
          value b = aoyagiHtildeUpperNat (N + 1) a M m j - (alphaOf b : ℤ))
    (hupper :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        value (upper j) = aoyagiHtildeUpperNat (N + 1) a M m j)
    (hlower :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) → j ≤ a →
        j ≤ (N + 1) - a →
          value (lower j) = aoyagiHtildeLowerNat (N + 1) a M m j)
    (halpha_inj :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
        Set.InjOn alphaOf ↑(strictBranches j))
    (branchCoord : β → ℕ)
    (hstrictCoord :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
        ∀ b ∈ strictBranches j, branchCoord b = j)
    (hupperCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        branchCoord (upper j) = j)
    (hlowerCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) → j ≤ a →
        j ≤ (N + 1) - a → branchCoord (lower j) = j)
    (hfamily :
      TC.family.toAoyagiLemma5SuppliedNonbaseFamily =
        ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord
          (ell := N + 1) (a := a) (M := M) (m := m)
          strictBranches alphaOf value upper lower baseValue ha
          baseValue_mem halpha_image hvalue hupper hlower halpha_inj
          branchCoord hstrictCoord hupperCoord hlowerCoord)
    (hbranchS :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.branchS (some b) = cut.point (branchCoord b) - 1)
    (hbranchK :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.family.value b = (TC.branchK (some b) : ℤ) - 1)
    (hbaseLabel :
      TC.branchLabel none =
        ((Sigma.mk (cut.point (N + 1) - 1) 1) : Σ _ : ℕ, ℕ)) :
    TC.TerminalMinimumLabelExactness := by
  exact
    TC.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze
      ha cut pOf labelAlphaOf layerWidth T hselected hsource hT
      hlabelBlock hlast hwidth_le hlabelFormula hlabel_ne_base
      hpAlpha_inj
      (TC.branchBlock_of_toNonbase_eq_eq5EndpointCoverage_leftEndpoint
        cut strictBranches alphaOf value upper lower baseValue ha
        baseValue_mem halpha_image hvalue hupper hlower halpha_inj
        branchCoord hstrictCoord hupperCoord hlowerCoord hfamily hbranchS)
      (TC.valueLabel_of_branchK_value hbranchK)
      hbaseLabel

/-- Exact terminal-minimum count from the endpoint-family version of the Eq5
branch-coordinate/value cardinal squeeze. -/
theorem terminalMinimumLabels_card_of_eq5EndpointFamily_branchCoordVal_cardSqueeze
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (ha : a ≤ N + 1)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (pOf labelAlphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (strictBranches : ℕ → Finset β) (alphaOf : β → ℕ)
    (value : β → ℤ) (upper lower : ℕ → β) (baseValue : ℕ → ℤ)
    (hselected :
      (∑ i : Fin (N + 2), m i) = ((N + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (N + 2),
      ((N + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (N + 2), m j)
    (hT : ∀ label ∈ TC.terminalMinimumLabels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        (N + 1) a (pOf label) (labelAlphaOf label) M m cut
        (layerWidth label) (T label))
    (hlabelBlock : ∀ label ∈ TC.terminalMinimumLabels,
      cut.block (pOf label) label.1)
    (hlast : cut.point (N + 1) ≤ L + 1)
    (hwidth_le : ∀ label ∈ TC.terminalMinimumLabels,
      aoyagiSelectedWidthNat (N + 1) m (pOf label) ≤
        (width (label.1 + 1) : ℤ))
    (hlabelFormula : ∀ label ∈ TC.terminalMinimumLabels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat (N + 1) a M m (pOf label) + 1 -
          (labelAlphaOf label : ℤ))
    (hlabel_ne_base : ∀ label ∈ TC.terminalMinimumLabels,
      T label label.1 ≠ TC.family.baseValue (pOf label))
    (hpAlpha_inj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (Sigma.mk (pOf label) (labelAlphaOf label) : Σ _ : ℕ, ℕ))
        ↑TC.terminalMinimumLabels)
    (baseValue_mem :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        baseValue j ∈ aoyagiHtildeIntervalValueSetNat (N + 1) a M m j)
    (halpha_image :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        (strictBranches j).image alphaOf =
          aoyagiLemma5Eq5AlphaDomain (N + 1) a j)
    (hvalue :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
        ∀ b ∈ strictBranches j,
          value b = aoyagiHtildeUpperNat (N + 1) a M m j - (alphaOf b : ℤ))
    (hupper :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        value (upper j) = aoyagiHtildeUpperNat (N + 1) a M m j)
    (hlower :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) → j ≤ a →
        j ≤ (N + 1) - a →
          value (lower j) = aoyagiHtildeLowerNat (N + 1) a M m j)
    (halpha_inj :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
        Set.InjOn alphaOf ↑(strictBranches j))
    (branchCoord : β → ℕ)
    (hstrictCoord :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
        ∀ b ∈ strictBranches j, branchCoord b = j)
    (hupperCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        branchCoord (upper j) = j)
    (hlowerCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) → j ≤ a →
        j ≤ (N + 1) - a → branchCoord (lower j) = j)
    (hfamily :
      TC.family.toAoyagiLemma5SuppliedNonbaseFamily =
        ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord
          (ell := N + 1) (a := a) (M := M) (m := m)
          strictBranches alphaOf value upper lower baseValue ha
          baseValue_mem halpha_image hvalue hupper hlower halpha_inj
          branchCoord hstrictCoord hupperCoord hlowerCoord)
    (hbranchS :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.branchS (some b) = cut.point (branchCoord b) - 1)
    (hbranchK :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.family.value b = (TC.branchK (some b) : ℤ) - 1)
    (hbaseLabel :
      TC.branchLabel none =
        ((Sigma.mk (cut.point (N + 1) - 1) 1) : Σ _ : ℕ, ℕ)) :
    TC.terminalMinimumLabels.card = a * (N + 1 - a) + 1 := by
  exact
    TC.terminalMinimumLabels_card_of_exactness N a M m ha hselected
      (TC.terminalMinimumLabelExactness_of_eq5EndpointFamily_branchCoordVal_cardSqueeze
        ha cut pOf labelAlphaOf layerWidth T strictBranches alphaOf value
        upper lower baseValue hselected hsource hT hlabelBlock hlast hwidth_le
        hlabelFormula hlabel_ne_base hpAlpha_inj baseValue_mem halpha_image
        hvalue hupper hlower halpha_inj branchCoord hstrictCoord hupperCoord
        hlowerCoord hfamily hbranchS hbranchK hbaseLabel)

/-- Block-width version of
`terminalMinimumLabelExactness_of_eq5EndpointFamily_branchCoordVal_cardSqueeze`.

The blockwise actual-width hypothesis is converted to the per-terminal-label
width bound by the supplied terminal label block data. -/
theorem
    terminalMinimumLabelExactness_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (ha : a ≤ N + 1)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (pOf labelAlphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (strictBranches : ℕ → Finset β) (alphaOf : β → ℕ)
    (value : β → ℤ) (upper lower : ℕ → β) (baseValue : ℕ → ℤ)
    (hselected :
      (∑ i : Fin (N + 2), m i) = ((N + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (N + 2),
      ((N + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (N + 2), m j)
    (hT : ∀ label ∈ TC.terminalMinimumLabels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        (N + 1) a (pOf label) (labelAlphaOf label) M m cut
        (layerWidth label) (T label))
    (hlabelBlock : ∀ label ∈ TC.terminalMinimumLabels,
      cut.block (pOf label) label.1)
    (hlast : cut.point (N + 1) ≤ L + 1)
    (hactual :
      ∀ i : Fin (N + 1), ∀ r : ℕ,
        cut.point i.val ≤ r → r < cut.point (i.val + 1) →
          aoyagiSelectedWidthNat (N + 1) m i.val ≤ (width r : ℤ))
    (hlabelFormula : ∀ label ∈ TC.terminalMinimumLabels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat (N + 1) a M m (pOf label) + 1 -
          (labelAlphaOf label : ℤ))
    (hlabel_ne_base : ∀ label ∈ TC.terminalMinimumLabels,
      T label label.1 ≠ TC.family.baseValue (pOf label))
    (hpAlpha_inj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (Sigma.mk (pOf label) (labelAlphaOf label) : Σ _ : ℕ, ℕ))
        ↑TC.terminalMinimumLabels)
    (baseValue_mem :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        baseValue j ∈ aoyagiHtildeIntervalValueSetNat (N + 1) a M m j)
    (halpha_image :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        (strictBranches j).image alphaOf =
          aoyagiLemma5Eq5AlphaDomain (N + 1) a j)
    (hvalue :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
        ∀ b ∈ strictBranches j,
          value b = aoyagiHtildeUpperNat (N + 1) a M m j - (alphaOf b : ℤ))
    (hupper :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        value (upper j) = aoyagiHtildeUpperNat (N + 1) a M m j)
    (hlower :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) → j ≤ a →
        j ≤ (N + 1) - a →
          value (lower j) = aoyagiHtildeLowerNat (N + 1) a M m j)
    (halpha_inj :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
        Set.InjOn alphaOf ↑(strictBranches j))
    (branchCoord : β → ℕ)
    (hstrictCoord :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
        ∀ b ∈ strictBranches j, branchCoord b = j)
    (hupperCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        branchCoord (upper j) = j)
    (hlowerCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) → j ≤ a →
        j ≤ (N + 1) - a → branchCoord (lower j) = j)
    (hfamily :
      TC.family.toAoyagiLemma5SuppliedNonbaseFamily =
        ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord
          (ell := N + 1) (a := a) (M := M) (m := m)
          strictBranches alphaOf value upper lower baseValue ha
          baseValue_mem halpha_image hvalue hupper hlower halpha_inj
          branchCoord hstrictCoord hupperCoord hlowerCoord)
    (hbranchS :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.branchS (some b) = cut.point (branchCoord b) - 1)
    (hbranchK :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.family.value b = (TC.branchK (some b) : ℤ) - 1)
    (hbaseLabel :
      TC.branchLabel none =
        ((Sigma.mk (cut.point (N + 1) - 1) 1) : Σ _ : ℕ, ℕ)) :
    TC.TerminalMinimumLabelExactness := by
  exact
    TC.terminalMinimumLabelExactness_of_eq5EndpointFamily_branchCoordVal_cardSqueeze
      ha cut pOf labelAlphaOf layerWidth T strictBranches alphaOf value
      upper lower baseValue hselected hsource hT hlabelBlock hlast
      (fun label hlabel ↦
        cut.selectedWidthNat_le_actualWidth_of_block width m hactual
          (hlabelBlock label hlabel))
      hlabelFormula hlabel_ne_base hpAlpha_inj baseValue_mem halpha_image
      hvalue hupper hlower halpha_inj branchCoord hstrictCoord hupperCoord
      hlowerCoord hfamily hbranchS hbranchK hbaseLabel

/-- Exact terminal-minimum count from the block-width endpoint-family
cardinal squeeze. -/
theorem terminalMinimumLabels_card_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N a : ℕ} {M : ℤ} {m : Fin (N + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N a M m t numerator leastValue)
    (ha : a ≤ N + 1)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (pOf labelAlphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (strictBranches : ℕ → Finset β) (alphaOf : β → ℕ)
    (value : β → ℤ) (upper lower : ℕ → β) (baseValue : ℕ → ℤ)
    (hselected :
      (∑ i : Fin (N + 2), m i) = ((N + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (N + 2),
      ((N + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (N + 2), m j)
    (hT : ∀ label ∈ TC.terminalMinimumLabels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        (N + 1) a (pOf label) (labelAlphaOf label) M m cut
        (layerWidth label) (T label))
    (hlabelBlock : ∀ label ∈ TC.terminalMinimumLabels,
      cut.block (pOf label) label.1)
    (hlast : cut.point (N + 1) ≤ L + 1)
    (hactual :
      ∀ i : Fin (N + 1), ∀ r : ℕ,
        cut.point i.val ≤ r → r < cut.point (i.val + 1) →
          aoyagiSelectedWidthNat (N + 1) m i.val ≤ (width r : ℤ))
    (hlabelFormula : ∀ label ∈ TC.terminalMinimumLabels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat (N + 1) a M m (pOf label) + 1 -
          (labelAlphaOf label : ℤ))
    (hlabel_ne_base : ∀ label ∈ TC.terminalMinimumLabels,
      T label label.1 ≠ TC.family.baseValue (pOf label))
    (hpAlpha_inj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (Sigma.mk (pOf label) (labelAlphaOf label) : Σ _ : ℕ, ℕ))
        ↑TC.terminalMinimumLabels)
    (baseValue_mem :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        baseValue j ∈ aoyagiHtildeIntervalValueSetNat (N + 1) a M m j)
    (halpha_image :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        (strictBranches j).image alphaOf =
          aoyagiLemma5Eq5AlphaDomain (N + 1) a j)
    (hvalue :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
        ∀ b ∈ strictBranches j,
          value b = aoyagiHtildeUpperNat (N + 1) a M m j - (alphaOf b : ℤ))
    (hupper :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        value (upper j) = aoyagiHtildeUpperNat (N + 1) a M m j)
    (hlower :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) → j ≤ a →
        j ≤ (N + 1) - a →
          value (lower j) = aoyagiHtildeLowerNat (N + 1) a M m j)
    (halpha_inj :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
        Set.InjOn alphaOf ↑(strictBranches j))
    (branchCoord : β → ℕ)
    (hstrictCoord :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
        ∀ b ∈ strictBranches j, branchCoord b = j)
    (hupperCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        branchCoord (upper j) = j)
    (hlowerCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) → j ≤ a →
        j ≤ (N + 1) - a → branchCoord (lower j) = j)
    (hfamily :
      TC.family.toAoyagiLemma5SuppliedNonbaseFamily =
        ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord
          (ell := N + 1) (a := a) (M := M) (m := m)
          strictBranches alphaOf value upper lower baseValue ha
          baseValue_mem halpha_image hvalue hupper hlower halpha_inj
          branchCoord hstrictCoord hupperCoord hlowerCoord)
    (hbranchS :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.branchS (some b) = cut.point (branchCoord b) - 1)
    (hbranchK :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.family.value b = (TC.branchK (some b) : ℤ) - 1)
    (hbaseLabel :
      TC.branchLabel none =
        ((Sigma.mk (cut.point (N + 1) - 1) 1) : Σ _ : ℕ, ℕ)) :
    TC.terminalMinimumLabels.card = a * (N + 1 - a) + 1 := by
  exact
    TC.terminalMinimumLabels_card_of_exactness N a M m ha hselected
      (TC.terminalMinimumLabelExactness_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze
        ha cut pOf labelAlphaOf layerWidth T strictBranches alphaOf value
        upper lower baseValue hselected hsource hT hlabelBlock hlast hactual
        hlabelFormula hlabel_ne_base hpAlpha_inj baseValue_mem halpha_image
        hvalue hupper hlower halpha_inj branchCoord hstrictCoord hupperCoord
        hlowerCoord hfamily hbranchS hbranchK hbaseLabel)

end AoyagiLemma5SuppliedTerminalCandidateFamily

end Aoyagi
end DLN
end DLNFibre
