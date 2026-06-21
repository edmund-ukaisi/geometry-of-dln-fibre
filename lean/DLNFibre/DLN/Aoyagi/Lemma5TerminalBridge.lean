import DLNFibre.DLN.Aoyagi.BlowupArithmetic
import DLNFibre.DLN.Aoyagi.Lemma5SuppliedFamily

/-!
# Supplied terminal-candidate bridge for Aoyagi's Lemma 5

This file connects the supplied Lemma 5 branch family to the existing
terminal-exponent certificate API.  The bridge is deliberately conditional:
the identification of a source terminal-exponent numerator with the Lemma 3
free-count expression is supplied as a hypothesis.  No displayed branch
construction, chart coverage, pole-order count, normal-crossing theorem, or
RLCT extraction is proved here.
-/

open scoped BigOperators

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- The free high-count parameter used in Aoyagi Lemma 3.

For total increment length `n+1`, this counts only the first `n` Lemma 4
increments and excludes the final increment `Fin.last n`. -/
def aoyagiLemma4FreeHighCount (n : ℕ) (M : ℤ)
    (m H : Fin (n + 2) → ℤ) : ℕ :=
  (Finset.univ.filter fun j : Fin n ↦
    aoyagiLemma4F (n + 1) m H j.castSucc = M).card

/-- The isolated Lemma 5 terminal-exponent numerator supplied by the Lemma 3
minimum calculation for total increment length `n+1`. -/
def aoyagiLemma5MinNumerator (n a : ℕ) : ℤ :=
  (a : ℤ) * ((n + 1 : ℕ) : ℤ) *
    (((n + 1 : ℕ) : ℤ) - (a : ℤ))

/-- Every tagged branch in a supplied full Lemma 5 family attains the isolated
Lemma 3 numerator minimum, stated with the named free high-count parameter. -/
theorem AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_freeHighCountMin
    {β : Type*} [DecidableEq β] {n a : ℕ} {M : ℤ}
    {m : Fin (n + 2) → ℤ}
    (F : AoyagiLemma5SuppliedAdmissibleFamily β (n + 1) a M m)
    (ha : a ≤ n + 1)
    (hselected :
      (∑ j : Fin (n + 2), m j) = ((n + 1 : ℕ) : ℤ) * (M - 1) + a)
    {x : Option β} (hx : x ∈ F.fullBranches) :
    aoyagiLemma3A ((n + 1 : ℕ) : ℤ) (a : ℤ)
        (aoyagiLemma4FreeHighCount n M m (F.fullH x) : ℤ) =
      (a : ℤ) * ((n + 1 : ℕ) : ℤ) *
        (((n + 1 : ℕ) : ℤ) - (a : ℤ)) := by
  simpa [aoyagiLemma4FreeHighCount] using
    F.fullBranch_freeHighCount_lemma3A_eq_min ha hselected hx

/-- Supplied terminal-exponent numerator bridge for a tagged Lemma 5 branch.

If an introduced-label exponent certificate has a numerator supplied to be the
Lemma 3 free-count expression of a tagged supplied Lemma 5 branch, then its
terminal exponent is the isolated Lemma 3 minimum numerator.

The hypothesis `hnumer` is the missing terminal-exponent normalisation.  This
theorem does not construct the source label, prove terminal `\tilde t=0`,
identify the numerator with `lambda`, prove pole order, or perform RLCT
extraction. -/
theorem IntroducedLabelExponentCertificates.terminalExponent_eq_suppliedLemma5MinNumerator
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J s k : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    (certs : IntroducedLabelExponentCertificates L width S J t numerator leastValue)
    (F : AoyagiLemma5SuppliedAdmissibleFamily β (n + 1) a M m)
    (ha : a ≤ n + 1)
    (hselected :
      (∑ j : Fin (n + 2), m j) = ((n + 1 : ℕ) : ℤ) * (M - 1) + a)
    {x : Option β} (hx : x ∈ F.fullBranches)
    (hintro : introducedLabel L width S J s k)
    (hnumer :
      numerator s k =
        aoyagiLemma3A ((n + 1 : ℕ) : ℤ) (a : ℤ)
          (aoyagiLemma4FreeHighCount n M m (F.fullH x) : ℤ)) :
    terminalExponent L (widthZ width) (t s k) =
      (a : ℤ) * ((n + 1 : ℕ) : ℤ) *
        (((n + 1 : ℕ) : ℤ) - (a : ℤ)) := by
  have hc := certs.certificate hintro
  calc
    terminalExponent L (widthZ width) (t s k) = numerator s k :=
      hc.terminalExponent_eq
    _ =
        aoyagiLemma3A ((n + 1 : ℕ) : ℤ) (a : ℤ)
          (aoyagiLemma4FreeHighCount n M m (F.fullH x) : ℤ) := hnumer
    _ = (a : ℤ) * ((n + 1 : ℕ) : ℤ) *
        (((n + 1 : ℕ) : ℤ) - (a : ℤ)) :=
      F.fullBranch_freeHighCountMin ha hselected hx

/-- Supplied terminal-candidate data over a full Lemma 5 branch family.

The fields attach each tagged supplied branch to a source label in the generic
introduced-label exponent-certificate API, supply terminality as least value
zero, and supply the missing numerator normalisation to the Lemma 3 free-count
expression.  This is still a supplied boundary: it does not construct these
labels from Aoyagi's printed equations and does not assert there are no other
terminal minimizers. -/
structure AoyagiLemma5SuppliedTerminalCandidateFamily (β : Type*) [DecidableEq β]
    (L : ℕ) (width : ℕ → ℕ) (S J : ℕ)
    (n a : ℕ) (M : ℤ) (m : Fin (n + 2) → ℤ)
    (t : ℕ → ℕ → ℕ → ℤ)
    (numerator leastValue : ℕ → ℕ → ℤ) where
  family : AoyagiLemma5SuppliedAdmissibleFamily β (n + 1) a M m
  certs : IntroducedLabelExponentCertificates L width S J t numerator leastValue
  branchS : Option β → ℕ
  branchK : Option β → ℕ
  introduced :
    ∀ {x : Option β}, x ∈ family.fullBranches →
      introducedLabel L width S J (branchS x) (branchK x)
  terminal_leastValue_zero :
    ∀ {x : Option β}, x ∈ family.fullBranches →
      leastValue (branchS x) (branchK x) = 0
  numerator_eq_lemma3A :
    ∀ {x : Option β}, x ∈ family.fullBranches →
      numerator (branchS x) (branchK x) =
        aoyagiLemma3A ((n + 1 : ℕ) : ℤ) (a : ℤ)
          (aoyagiLemma4FreeHighCount n M m (family.fullH x) : ℤ)

namespace AoyagiLemma5SuppliedTerminalCandidateFamily

/-- The tagged branch set of a supplied terminal-candidate family. -/
def fullBranches {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue) :
    Finset (Option β) :=
  C.family.fullBranches

/-- The supplied source-label pair attached to a tagged branch. -/
def branchLabel {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (x : Option β) :
    Σ _ : ℕ, ℕ :=
  Sigma.mk (C.branchS x) (C.branchK x)

/-- The finite image of supplied branch labels.

This is a candidate-label image only.  It is not the full terminal-minimizer
set unless separate no-extra-minimizer/coverage data are supplied. -/
def branchLabelImage {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue) :
    Finset (Σ _ : ℕ, ℕ) :=
  C.fullBranches.image C.branchLabel

/-- Introduced labels with terminal least value zero and the supplied Lemma 5
minimum numerator.

This is a finite exact-minimum label set inside the current introduced-label
domain.  It is not a pole-order statement and it is not known to equal the
branch-label image without a separate no-extra/coverage hypothesis. -/
def terminalMinimumLabels {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (_C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue) :
    Finset (Σ _ : ℕ, ℕ) :=
  (introducedLabelFinset L width S J).filter fun label ↦
    leastValue label.1 label.2 = 0 ∧
      terminalExponent L (widthZ width) (t label.1 label.2) =
        aoyagiLemma5MinNumerator n a

/-- A supplied counted-datum classifier for the finite terminal-minimum labels.

This is the source-facing upper-bound boundary separated from branch-label
exactness: it classifies terminal minimum labels into the counted interval
codomain, but does not say that they are supplied branch labels. -/
abbrev TerminalMinimumCountDatumClassifier {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue) : Type :=
  AoyagiLemma5CountDatumClassifier (Σ _ : ℕ, ℕ)
    (n + 1) a M m C.family.baseValue C.terminalMinimumLabels

/-- A supplied counted-datum classifier gives the terminal-minimum upper
count.

This is an upper-bound wrapper only.  The classifier, source-to-counted-datum
map, and injectivity are supplied data; branch-label exactness is not used. -/
theorem terminalMinimumLabels_card_le_of_countDatumClassifier {β : Type*}
    [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (ha : a ≤ n + 1)
    (classifier : C.TerminalMinimumCountDatumClassifier) :
    C.terminalMinimumLabels.card ≤ a * (n + 1 - a) + 1 := by
  exact AoyagiLemma5CountDatumClassifier.candidates_card_le
    (n + 1) a M m C.family.baseValue C.terminalMinimumLabels classifier
    (Nat.succ_pos n) ha C.family.baseValue_mem

/-- The counted datum attached to a supplied branch, once a coordinate is
supplied for each nonbase branch.

This is bookkeeping for the back-to-label boundary.  It does not construct the
coordinate map or prove it agrees with Aoyagi's displayed branch families. -/
def branchCountDatumOfCoord {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (branchCoord : β → ℕ) :
    Option β → AoyagiLemma5CountDatum :=
  C.family.toAoyagiLemma5SuppliedNonbaseFamily.countDatumOfBranchCoord
    branchCoord

/-- Supplied bridge from terminal-minimum counted data back to supplied branch
labels.

For each terminal-minimum label, the bridge supplies a branch with the same
branch label and with counted datum equal to the datum assigned by the supplied
terminal-minimum counted-datum classifier.  This is a supplied boundary; it is
not proved from Aoyagi's equations `(3)`, `(4)`, and `(5)`. -/
structure TerminalMinimumCountDatumBackToBranchLabel {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (branchCoord : β → ℕ)
    (classifier : C.TerminalMinimumCountDatumClassifier) : Prop where
  lift :
    ∀ {label : Σ _ : ℕ, ℕ}, label ∈ C.terminalMinimumLabels →
      ∃ x ∈ C.fullBranches,
        C.branchLabel x = label ∧
          C.branchCountDatumOfCoord branchCoord x = classifier.classify label

/-- The supplied terminal-candidate branch set has Aoyagi's Lemma 5 supplied
finite count. -/
theorem fullBranches_card {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    (n a : ℕ) (M : ℤ) (m : Fin (n + 2) → ℤ)
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (hell : 1 ≤ n + 1) (ha : a ≤ n + 1) :
    C.fullBranches.card = a * (n + 1 - a) + 1 := by
  exact AoyagiLemma5SuppliedAdmissibleFamily.fullBranches_card
    (n + 1) a M m C.family hell ha

/-- The supplied label attached to a tagged branch belongs to the finite
introduced-label set. -/
theorem branchLabel_mem_introducedLabelFinset {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    {x : Option β} (hx : x ∈ C.fullBranches) :
    C.branchLabel x ∈ introducedLabelFinset L width S J := by
  exact mem_introducedLabelFinset.mpr (C.introduced hx)

/-- The supplied branch-label image is contained in the finite introduced-label
set. -/
theorem branchLabelImage_subset_introducedLabelFinset {β : Type*}
    [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue) :
    C.branchLabelImage ⊆ introducedLabelFinset L width S J := by
  intro label hlabel
  rcases Finset.mem_image.mp hlabel with ⟨x, hx, rfl⟩
  exact C.branchLabel_mem_introducedLabelFinset hx

/-- The branch-label image has the same cardinality as the tagged branch set
when the supplied branch-to-label map is injective on the supplied branch set.

This is only a distinct supplied-candidate count.  It does not assert that all
terminal minimizers occur in this image. -/
theorem branchLabelImage_card_eq_fullBranches_card_of_injOn {β : Type*}
    [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (hinj : Set.InjOn C.branchLabel ↑C.fullBranches) :
    C.branchLabelImage.card = C.fullBranches.card := by
  exact Finset.card_image_of_injOn (s := C.fullBranches) (f := C.branchLabel) hinj

/-- Under supplied branch-label injectivity, the distinct supplied
terminal-candidate label image has Aoyagi's Lemma 5 supplied finite count.

This is not a pole-order theorem: it counts only the injected image of the
supplied candidate labels, and assumes no coverage of possible extra terminal
minimizers. -/
theorem branchLabelImage_card {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    (n a : ℕ) (M : ℤ) (m : Fin (n + 2) → ℤ)
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (ha : a ≤ n + 1)
    (hinj : Set.InjOn C.branchLabel ↑C.fullBranches) :
    C.branchLabelImage.card = a * (n + 1 - a) + 1 := by
  rw [C.branchLabelImage_card_eq_fullBranches_card_of_injOn hinj]
  exact C.fullBranches_card n a M m (Nat.succ_pos n) ha

/-- Supplied upper-bound classifier for the terminal-minimum labels.

The classifier is the no-extra direction phrased constructively: every finite
terminal-minimum label is assigned to a tagged supplied branch whose supplied
label is the original label.  This is still a supplied boundary; it is not
proved from Aoyagi's Lemma 5 upper-bound paragraph. -/
structure UpperBoundClassifier {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue) : Prop where
  classify :
    ∀ {label : Σ _ : ℕ, ℕ}, label ∈ C.terminalMinimumLabels →
      ∃ x ∈ C.fullBranches, C.branchLabel x = label

/-- A supplied upper-bound classifier gives the no-extra containment from
terminal minimum labels to the supplied branch-label image. -/
theorem terminalMinimumLabels_subset_branchLabelImage_of_upperBoundClassifier
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (classifier : C.UpperBoundClassifier) :
    C.terminalMinimumLabels ⊆ C.branchLabelImage := by
  intro label hlabel
  rcases classifier.classify hlabel with ⟨x, hx, hxl⟩
  rw [← hxl]
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- The no-extra containment from terminal minimum labels to the supplied
branch-label image gives the supplied upper-bound classifier.

This is the reverse finite-set direction to
`terminalMinimumLabels_subset_branchLabelImage_of_upperBoundClassifier`; it
does not prove the containment from Aoyagi's source. -/
theorem upperBoundClassifier_of_terminalMinimumLabels_subset_branchLabelImage
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (hsubset : C.terminalMinimumLabels ⊆ C.branchLabelImage) :
    C.UpperBoundClassifier where
  classify := by
    intro label hlabel
    rcases Finset.mem_image.mp (hsubset hlabel) with ⟨x, hx, hxl⟩
    exact ⟨x, hx, hxl⟩

/-- The supplied upper-bound classifier is exactly the no-extra containment
from terminal minimum labels to the supplied branch-label image.

This is a definitional finite-set equivalence for the supplied boundary, not a
source-backed classifier theorem. -/
theorem upperBoundClassifier_iff_terminalMinimumLabels_subset_branchLabelImage
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue) :
    C.UpperBoundClassifier ↔ C.terminalMinimumLabels ⊆ C.branchLabelImage := by
  constructor
  · intro classifier
    exact C.terminalMinimumLabels_subset_branchLabelImage_of_upperBoundClassifier
      classifier
  · intro hsubset
    exact C.upperBoundClassifier_of_terminalMinimumLabels_subset_branchLabelImage
      hsubset

/-- A supplied counted-datum back-to-label bridge gives the supplied
upper-bound classifier.

The counted-datum equality records the intended route through the interval
classifier, but the resulting upper-bound classifier uses only the supplied
branch-label witness. -/
theorem upperBoundClassifier_of_countDatumBackToBranchLabel {β : Type*}
    [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (branchCoord : β → ℕ)
    (classifier : C.TerminalMinimumCountDatumClassifier)
    (backToLabel :
      C.TerminalMinimumCountDatumBackToBranchLabel branchCoord classifier) :
    C.UpperBoundClassifier where
  classify := by
    intro label hlabel
    rcases backToLabel.lift hlabel with ⟨x, hx, hbranch, _hdatum⟩
    exact ⟨x, hx, hbranch⟩

/-- A supplied upper-bound classifier gives a cardinal upper bound by the
branch-label image. -/
theorem terminalMinimumLabels_card_le_branchLabelImage_card_of_upperBoundClassifier
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (classifier : C.UpperBoundClassifier) :
    C.terminalMinimumLabels.card ≤ C.branchLabelImage.card :=
  Finset.card_le_card
    (C.terminalMinimumLabels_subset_branchLabelImage_of_upperBoundClassifier
      classifier)

/-- Numeric upper count from a supplied upper-bound classifier.

This is an upper-bound wrapper only.  It does not prove the classifier,
branch-label injectivity, pole order, normal crossings, or RLCT extraction. -/
theorem terminalMinimumLabels_card_le_of_upperBoundClassifier {β : Type*}
    [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    (n a : ℕ) (M : ℤ) (m : Fin (n + 2) → ℤ)
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (ha : a ≤ n + 1)
    (classifier : C.UpperBoundClassifier) :
    C.terminalMinimumLabels.card ≤ a * (n + 1 - a) + 1 := by
  calc
    C.terminalMinimumLabels.card ≤ C.branchLabelImage.card :=
      C.terminalMinimumLabels_card_le_branchLabelImage_card_of_upperBoundClassifier
        classifier
    _ ≤ C.fullBranches.card := Finset.card_image_le
    _ = a * (n + 1 - a) + 1 :=
      C.fullBranches_card n a M m (Nat.succ_pos n) ha

/-- Membership in the finite exact-minimum label set. -/
theorem mem_terminalMinimumLabels {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    {label : Σ _ : ℕ, ℕ} :
    label ∈ C.terminalMinimumLabels ↔
      introducedLabel L width S J label.1 label.2 ∧
        leastValue label.1 label.2 = 0 ∧
          terminalExponent L (widthZ width) (t label.1 label.2) =
            aoyagiLemma5MinNumerator n a := by
  simp [terminalMinimumLabels, mem_introducedLabelFinset]

/-- Every tagged supplied terminal candidate has terminal least value zero. -/
theorem branch_terminalLeastValue_zero {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    {x : Option β} (hx : x ∈ C.fullBranches) :
    leastValue (C.branchS x) (C.branchK x) = 0 :=
  C.terminal_leastValue_zero hx

/-- Every tagged supplied terminal candidate has terminal exponent equal to
the isolated Lemma 3 minimum numerator.

The source-label realisation, terminal least-value zero, and numerator
normalisation are supplied fields of the structure. -/
theorem branch_terminalExponent_eq_minNumerator {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (ha : a ≤ n + 1)
    (hselected :
      (∑ j : Fin (n + 2), m j) = ((n + 1 : ℕ) : ℤ) * (M - 1) + a)
    {x : Option β} (hx : x ∈ C.fullBranches) :
    terminalExponent L (widthZ width) (t (C.branchS x) (C.branchK x)) =
      (a : ℤ) * ((n + 1 : ℕ) : ℤ) *
        (((n + 1 : ℕ) : ℤ) - (a : ℤ)) := by
  exact C.certs.terminalExponent_eq_suppliedLemma5MinNumerator
    C.family ha hselected hx (C.introduced hx) (C.numerator_eq_lemma3A hx)

/-- Branchwise supplied terminal-candidate package: introduced label,
terminal least value zero, and terminal-exponent minimum numerator. -/
theorem branch_terminalCandidateData {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (ha : a ≤ n + 1)
    (hselected :
      (∑ j : Fin (n + 2), m j) = ((n + 1 : ℕ) : ℤ) * (M - 1) + a)
    {x : Option β} (hx : x ∈ C.fullBranches) :
    introducedLabel L width S J (C.branchS x) (C.branchK x) ∧
      leastValue (C.branchS x) (C.branchK x) = 0 ∧
        terminalExponent L (widthZ width) (t (C.branchS x) (C.branchK x)) =
          (a : ℤ) * ((n + 1 : ℕ) : ℤ) *
            (((n + 1 : ℕ) : ℤ) - (a : ℤ)) := by
  exact ⟨C.introduced hx, C.branch_terminalLeastValue_zero hx,
    C.branch_terminalExponent_eq_minNumerator ha hselected hx⟩

/-- Every label in the supplied branch-label image inherits the branchwise
terminal-candidate data.

This does not say that the image contains every terminal minimizer; it only
transfers data from the supplied tagged branches to their supplied labels. -/
theorem branchLabelImage_terminalCandidateData {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (ha : a ≤ n + 1)
    (hselected :
      (∑ j : Fin (n + 2), m j) = ((n + 1 : ℕ) : ℤ) * (M - 1) + a)
    {label : Σ _ : ℕ, ℕ} (hlabel : label ∈ C.branchLabelImage) :
    introducedLabel L width S J label.1 label.2 ∧
      leastValue label.1 label.2 = 0 ∧
        terminalExponent L (widthZ width) (t label.1 label.2) =
          (a : ℤ) * ((n + 1 : ℕ) : ℤ) *
            (((n + 1 : ℕ) : ℤ) - (a : ℤ)) := by
  rcases Finset.mem_image.mp hlabel with ⟨x, hx, rfl⟩
  exact C.branch_terminalCandidateData ha hselected hx

/-- The supplied branch-label image is contained in the exact-minimum label
set.

This is only the easy direction: supplied candidates attain the minimum.  It
does not say that every minimum label comes from the supplied branch family. -/
theorem branchLabelImage_subset_terminalMinimumLabels {β : Type*}
    [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (ha : a ≤ n + 1)
    (hselected :
      (∑ j : Fin (n + 2), m j) = ((n + 1 : ℕ) : ℤ) * (M - 1) + a) :
    C.branchLabelImage ⊆ C.terminalMinimumLabels := by
  intro label hlabel
  rcases C.branchLabelImage_terminalCandidateData ha hselected hlabel with
    ⟨hintro, hleast, hterminal⟩
  rw [C.mem_terminalMinimumLabels]
  exact ⟨hintro, hleast, by
    simpa [aoyagiLemma5MinNumerator] using hterminal⟩

/-- Exact finite count of terminal minimum labels under supplied no-extra
coverage and supplied branch-label injectivity.

The hypothesis `hnoExtra` is the no-extra-minimizer boundary: every introduced
label with terminal least value zero and the supplied minimum numerator is in
the supplied branch-label image.  This theorem is still not a pole-order or
RLCT extraction theorem. -/
theorem terminalMinimumLabels_card_of_noExtra {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    (n a : ℕ) (M : ℤ) (m : Fin (n + 2) → ℤ)
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (ha : a ≤ n + 1)
    (hselected :
      (∑ j : Fin (n + 2), m j) = ((n + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hinj : Set.InjOn C.branchLabel ↑C.fullBranches)
    (hnoExtra : C.terminalMinimumLabels ⊆ C.branchLabelImage) :
    C.terminalMinimumLabels.card = a * (n + 1 - a) + 1 := by
  have himage : C.branchLabelImage ⊆ C.terminalMinimumLabels :=
    C.branchLabelImage_subset_terminalMinimumLabels ha hselected
  have heq : C.terminalMinimumLabels = C.branchLabelImage := by
    ext label
    constructor
    · intro hlabel
      exact hnoExtra hlabel
    · intro hlabel
      exact himage hlabel
  rw [heq]
  exact C.branchLabelImage_card n a M m ha hinj

/-- Supplied exactness data for the finite terminal-minimum label set.

The injectivity field separates distinct supplied branches as distinct source
labels.  The no-extra field says every introduced label with terminal least
value zero and the supplied minimum numerator is in the supplied branch-label
image.  This is still finite label data, not a normal-crossing or RLCT
extraction theorem. -/
structure TerminalMinimumLabelExactness {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue) : Prop where
  branchLabel_injOn : Set.InjOn C.branchLabel ↑C.fullBranches
  terminalMinimumLabels_subset_branchLabelImage :
    C.terminalMinimumLabels ⊆ C.branchLabelImage

/-- A supplied upper-bound classifier and supplied branch-label injectivity
package exactly the existing terminal-minimum exactness boundary. -/
theorem terminalMinimumLabelExactness_of_upperBoundClassifier {β : Type*}
    [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (hinj : Set.InjOn C.branchLabel ↑C.fullBranches)
    (classifier : C.UpperBoundClassifier) :
    C.TerminalMinimumLabelExactness where
  branchLabel_injOn := hinj
  terminalMinimumLabels_subset_branchLabelImage :=
    C.terminalMinimumLabels_subset_branchLabelImage_of_upperBoundClassifier
      classifier

/-- Packaged exactness identifies the finite terminal-minimum label set with
the supplied branch-label image.

The forward inclusion from the branch-label image to the minimum-label set
still uses `ha` and the selected-width sum through the supplied terminal
minimum bridge; the reverse inclusion is the supplied no-extra field. -/
theorem terminalMinimumLabels_eq_branchLabelImage_of_exactness {β : Type*}
    [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (ha : a ≤ n + 1)
    (hselected :
      (∑ j : Fin (n + 2), m j) = ((n + 1 : ℕ) : ℤ) * (M - 1) + a)
    (exactness : C.TerminalMinimumLabelExactness) :
    C.terminalMinimumLabels = C.branchLabelImage := by
  have himage : C.branchLabelImage ⊆ C.terminalMinimumLabels :=
    C.branchLabelImage_subset_terminalMinimumLabels ha hselected
  ext label
  constructor
  · intro hlabel
    exact exactness.terminalMinimumLabels_subset_branchLabelImage hlabel
  · intro hlabel
    exact himage hlabel

/-- Exact finite count of terminal minimum labels from packaged supplied
exactness data.

This is a convenience wrapper around `terminalMinimumLabels_card_of_noExtra`.
It does not prove the exactness fields from the source. -/
theorem terminalMinimumLabels_card_of_exactness {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    (n a : ℕ) (M : ℤ) (m : Fin (n + 2) → ℤ)
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (ha : a ≤ n + 1)
    (hselected :
      (∑ j : Fin (n + 2), m j) = ((n + 1 : ℕ) : ℤ) * (M - 1) + a)
    (exactness : C.TerminalMinimumLabelExactness) :
    C.terminalMinimumLabels.card = a * (n + 1 - a) + 1 := by
  rw [C.terminalMinimumLabels_eq_branchLabelImage_of_exactness ha hselected exactness]
  exact C.branchLabelImage_card n a M m ha exactness.branchLabel_injOn

/-- Packaged exactness gives a bijection from supplied branches to terminal
minimum labels.

This is finite bookkeeping only: the exactness fields themselves remain
supplied. -/
theorem branchLabel_bijOn_terminalMinimumLabels_of_exactness {β : Type*}
    [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (ha : a ≤ n + 1)
    (hselected :
      (∑ j : Fin (n + 2), m j) = ((n + 1 : ℕ) : ℤ) * (M - 1) + a)
    (exactness : C.TerminalMinimumLabelExactness) :
    Set.BijOn C.branchLabel ↑C.fullBranches ↑C.terminalMinimumLabels := by
  refine ⟨?_, exactness.branchLabel_injOn, ?_⟩
  · intro x hx
    exact C.branchLabelImage_subset_terminalMinimumLabels ha hselected
      (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  · intro label hlabel
    have heq : C.terminalMinimumLabels = C.branchLabelImage :=
      C.terminalMinimumLabels_eq_branchLabelImage_of_exactness ha hselected exactness
    have himage : label ∈ C.branchLabelImage := by
      rwa [heq] at hlabel
    rcases Finset.mem_image.mp himage with ⟨x, hx, hxl⟩
    exact ⟨x, hx, hxl⟩

/-- A bijection from supplied branches to terminal minimum labels is one
standard way to supply terminal-minimum exactness. -/
theorem terminalMinimumLabelExactness_of_branchLabel_bijOn {β : Type*}
    [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (hbij : Set.BijOn C.branchLabel ↑C.fullBranches ↑C.terminalMinimumLabels) :
    C.TerminalMinimumLabelExactness where
  branchLabel_injOn := hbij.injOn
  terminalMinimumLabels_subset_branchLabelImage := by
    intro label hlabel
    rcases hbij.surjOn hlabel with ⟨x, hx, hxl⟩
    rw [← hxl]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- Count terminal minimum labels from a supplied branch-label bijection.

This wrapper does not prove the bijection from Aoyagi's source equations. -/
theorem terminalMinimumLabels_card_of_branchLabel_bijOn {β : Type*}
    [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    (n a : ℕ) (M : ℤ) (m : Fin (n + 2) → ℤ)
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (ha : a ≤ n + 1)
    (hbij : Set.BijOn C.branchLabel ↑C.fullBranches ↑C.terminalMinimumLabels) :
    C.terminalMinimumLabels.card = a * (n + 1 - a) + 1 := by
  have hsubset : C.branchLabelImage ⊆ C.terminalMinimumLabels := by
    intro label hlabel
    rcases Finset.mem_image.mp hlabel with ⟨x, hx, rfl⟩
    exact hbij.mapsTo hx
  have hnoExtra : C.terminalMinimumLabels ⊆ C.branchLabelImage :=
    (C.terminalMinimumLabelExactness_of_branchLabel_bijOn hbij).2
  have heq : C.terminalMinimumLabels = C.branchLabelImage := by
    ext label
    constructor
    · intro hlabel
      exact hnoExtra hlabel
    · intro hlabel
      exact hsubset hlabel
  rw [heq]
  exact C.branchLabelImage_card n a M m ha hbij.injOn

end AoyagiLemma5SuppliedTerminalCandidateFamily

end Aoyagi
end DLN
end DLNFibre
