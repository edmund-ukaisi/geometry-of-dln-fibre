import DLNFibre.DLN.Aoyagi.Lemma5TerminalBridge
import DLNFibre.DLN.Aoyagi.FinalFormula

/-!
# Lemma 5 terminal order bridge

This file rewrites the remaining supplied Lemma 5 terminal-exactness
obstruction in Aoyagi Theorem 2's final order notation.  It is a handoff
layer only: branch-label injectivity and the terminal-minimum upper bound
remain supplied, and no source-backed no-extra coverage, pole order, normal
crossings, or RLCT extraction is proved here.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

namespace AoyagiLemma5SuppliedTerminalCandidateFamily

/-- Terminal-minimum exactness, stated using Aoyagi Theorem 2's order formula,
is equivalent to the remaining supplied finite obstruction.

The two right-hand hypotheses are still supplied: branch-label injectivity and
the terminal-minimum cardinal upper bound. -/
theorem terminalMinimumLabelExactness_iff_branchLabel_injOn_and_theorem2OrderFormula_bound
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J n : ℕ}
    {m : Fin (n + 2) → ℤ}
    (data : AoyagiDefinition3CeilData (n + 1) m)
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC :
      AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J
        n data.aParam data.ceilWidth m t numerator leastValue) :
    TC.TerminalMinimumLabelExactness ↔
      Set.InjOn TC.branchLabel ↑TC.fullBranches ∧
        TC.terminalMinimumLabels.card ≤ data.theorem2OrderFormula := by
  simpa [AoyagiDefinition3CeilData.theorem2OrderFormula] using
    (TC.terminalMinimumLabelExactness_iff_branchLabel_injOn_and_card_bound
      n data.aParam data.ceilWidth m data.aParam_le data.selectedSum_eq)

/-- Supplied branch-label injectivity plus a supplied terminal-minimum upper
bound give Aoyagi Theorem 2's displayed order formula.

This is finite bookkeeping from the Lemma 5 supplied terminal-candidate
interface to final-formula notation.  It does not construct the upper bound,
branch-label injectivity, no-extra coverage, pole order, normal crossings, or
RLCT extraction. -/
theorem terminalMinimumLabels_card_eq_theorem2OrderFormula_of_card_bound_and_branchLabel_injOn
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J n : ℕ}
    {m : Fin (n + 2) → ℤ}
    (data : AoyagiDefinition3CeilData (n + 1) m)
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC :
      AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J
        n data.aParam data.ceilWidth m t numerator leastValue)
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (hupper : TC.terminalMinimumLabels.card ≤ data.theorem2OrderFormula) :
    TC.terminalMinimumLabels.card = data.theorem2OrderFormula := by
  have hexact : TC.TerminalMinimumLabelExactness :=
    (TC.terminalMinimumLabelExactness_iff_branchLabel_injOn_and_theorem2OrderFormula_bound
      data).mpr ⟨hinj, hupper⟩
  simpa [AoyagiDefinition3CeilData.theorem2OrderFormula] using
    (TC.terminalMinimumLabels_card_of_exactness
      n data.aParam data.ceilWidth m data.aParam_le data.selectedSum_eq hexact)

/-- A supplied counted-datum classifier gives Aoyagi Theorem 2's displayed
terminal-minimum upper bound.

This is finite bookkeeping from the counted-datum classifier boundary to final
order notation.  It does not construct the classifier, a back-to-label map,
branch-label injectivity, no-extra coverage, pole order, normal crossings, or
RLCT extraction. -/
theorem terminalMinimumLabels_card_le_theorem2OrderFormula_of_countDatumClassifier
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J n : ℕ}
    {m : Fin (n + 2) → ℤ}
    (data : AoyagiDefinition3CeilData (n + 1) m)
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC :
      AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J
        n data.aParam data.ceilWidth m t numerator leastValue)
    (classifier : TC.TerminalMinimumCountDatumClassifier) :
    TC.terminalMinimumLabels.card ≤ data.theorem2OrderFormula := by
  simpa [AoyagiDefinition3CeilData.theorem2OrderFormula] using
    (TC.terminalMinimumLabels_card_le_of_countDatumClassifier
      data.aParam_le classifier)

/-- Supplied branch-label injectivity plus a supplied counted-datum classifier
give Aoyagi Theorem 2's displayed order formula.

The classifier supplies only the terminal-minimum cardinal upper bound; the
branch-label injectivity remains an explicit hypothesis.  This does not
construct source classifiers, branch labels, no-extra coverage, pole order,
normal crossings, or RLCT extraction. -/
theorem
  terminalMinimumLabels_card_eq_theorem2OrderFormula_of_countDatumClassifier_and_branchLabel_injOn
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J n : ℕ}
    {m : Fin (n + 2) → ℤ}
    (data : AoyagiDefinition3CeilData (n + 1) m)
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC :
      AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J
        n data.aParam data.ceilWidth m t numerator leastValue)
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (classifier : TC.TerminalMinimumCountDatumClassifier) :
    TC.terminalMinimumLabels.card = data.theorem2OrderFormula :=
  terminalMinimumLabels_card_eq_theorem2OrderFormula_of_card_bound_and_branchLabel_injOn
    data TC hinj
    (terminalMinimumLabels_card_le_theorem2OrderFormula_of_countDatumClassifier
      data TC classifier)

/-- A supplied upper-bound classifier gives Aoyagi Theorem 2's displayed
terminal-minimum upper bound.

This is finite bookkeeping from the upper-bound classifier boundary to final
order notation.  It does not construct the classifier, branch-label
injectivity, no-extra coverage, pole order, normal crossings, or RLCT
extraction. -/
theorem terminalMinimumLabels_card_le_theorem2OrderFormula_of_upperBoundClassifier
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J n : ℕ}
    {m : Fin (n + 2) → ℤ}
    (data : AoyagiDefinition3CeilData (n + 1) m)
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC :
      AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J
        n data.aParam data.ceilWidth m t numerator leastValue)
    (classifier : TC.UpperBoundClassifier) :
    TC.terminalMinimumLabels.card ≤ data.theorem2OrderFormula := by
  simpa [AoyagiDefinition3CeilData.theorem2OrderFormula] using
    (TC.terminalMinimumLabels_card_le_of_upperBoundClassifier
      n data.aParam data.ceilWidth m data.aParam_le classifier)

/-- Supplied branch-label injectivity plus a supplied upper-bound classifier
give Aoyagi Theorem 2's displayed order formula.

This is finite bookkeeping only.  The classifier and injectivity remain
explicit supplied hypotheses. -/
theorem
  terminalMinimumLabels_card_eq_theorem2OrderFormula_of_upperBoundClassifier_and_branchLabel_injOn
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J n : ℕ}
    {m : Fin (n + 2) → ℤ}
    (data : AoyagiDefinition3CeilData (n + 1) m)
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC :
      AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J
        n data.aParam data.ceilWidth m t numerator leastValue)
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (classifier : TC.UpperBoundClassifier) :
    TC.terminalMinimumLabels.card = data.theorem2OrderFormula := by
  simpa [AoyagiDefinition3CeilData.theorem2OrderFormula] using
    (TC.terminalMinimumLabels_card_of_upperBoundClassifier_and_branchLabel_injOn
      n data.aParam data.ceilWidth m data.aParam_le data.selectedSum_eq
      hinj classifier)

/-- A supplied counted-datum back-to-label bridge gives Aoyagi Theorem 2's
displayed terminal-minimum upper bound.

This is finite bookkeeping from the counted-datum back-to-label boundary to
final order notation.  It does not construct the counted-datum classifier,
back-to-label bridge, branch-label injectivity, no-extra coverage, pole order,
normal crossings, or RLCT extraction. -/
theorem terminalMinimumLabels_card_le_theorem2OrderFormula_of_countDatumBackToBranchLabel
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J n : ℕ}
    {m : Fin (n + 2) → ℤ}
    (data : AoyagiDefinition3CeilData (n + 1) m)
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC :
      AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J
        n data.aParam data.ceilWidth m t numerator leastValue)
    (branchCoord : β → ℕ)
    (classifier : TC.TerminalMinimumCountDatumClassifier)
    (backToLabel :
      TC.TerminalMinimumCountDatumBackToBranchLabel branchCoord classifier) :
    TC.terminalMinimumLabels.card ≤ data.theorem2OrderFormula := by
  simpa [AoyagiDefinition3CeilData.theorem2OrderFormula] using
    (TC.terminalMinimumLabels_card_le_of_countDatumBackToBranchLabel
      n data.aParam data.ceilWidth m data.aParam_le branchCoord classifier
      backToLabel)

/-- Supplied branch-label injectivity plus a supplied counted-datum
back-to-label bridge give Aoyagi Theorem 2's displayed order formula.

This is finite bookkeeping only.  The counted-datum classifier,
back-to-label bridge, and branch-label injectivity remain explicit supplied
hypotheses. -/
theorem
  terminalMinimumLabels_card_eq_theorem2OrderFormula_of_countDatumBackToBranchLabel_and_injOn
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J n : ℕ}
    {m : Fin (n + 2) → ℤ}
    (data : AoyagiDefinition3CeilData (n + 1) m)
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC :
      AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J
        n data.aParam data.ceilWidth m t numerator leastValue)
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (branchCoord : β → ℕ)
    (classifier : TC.TerminalMinimumCountDatumClassifier)
    (backToLabel :
      TC.TerminalMinimumCountDatumBackToBranchLabel branchCoord classifier) :
    TC.terminalMinimumLabels.card = data.theorem2OrderFormula := by
  simpa [AoyagiDefinition3CeilData.theorem2OrderFormula] using
    (TC.terminalMinimumLabels_card_of_countDatumBackToBranchLabel
      n data.aParam data.ceilWidth m data.aParam_le data.selectedSum_eq
      hinj branchCoord classifier backToLabel)

end AoyagiLemma5SuppliedTerminalCandidateFamily

end Aoyagi
end DLN
end DLNFibre
