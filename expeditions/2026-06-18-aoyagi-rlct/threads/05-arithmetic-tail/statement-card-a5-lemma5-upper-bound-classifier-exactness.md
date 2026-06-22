# Statement card - A5 Lemma 5 upper-bound classifier exactness wrappers

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_eq_branchLabelImage_of_upperBoundClassifier`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_iff_branchLabel_injOn_and_upperBoundClassifier`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_upperBoundClassifier_and_branchLabel_injOn`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_bijOn_terminalMinimumLabels_of_upperBoundClassifier`

## Claim

For a supplied terminal-candidate family, a supplied upper-bound classifier
identifies `terminalMinimumLabels` with the supplied `branchLabelImage`, once
the supplied branch labels are known to attain the terminal minimum.  If
branch-label injectivity is also supplied, the same data packages as
terminal-minimum exactness, a branch-label bijection, and the exact finite
label count.

## Proved

- `UpperBoundClassifier C` gives
  `C.terminalMinimumLabels subset C.branchLabelImage`.
- The existing supplied-candidate theorem gives
  `C.branchLabelImage subset C.terminalMinimumLabels` under `a <= n+1` and
  the selected-width sum.
- The two containments identify the finite sets.
- Adding supplied `Set.InjOn C.branchLabel C.fullBranches` gives the exactness
  package, the bijection, and the count
  `C.terminalMinimumLabels.card = a * (n + 1 - a) + 1`.

## Assumed

The terminal-candidate family, `a <= n+1`, the selected-width sum, the
upper-bound classifier, and branch-label injectivity where the theorem claims
a bijection or exact count.

## Deferred

Source construction of the classifier, branch-label injectivity,
counted-datum back-to-label coverage, source labels, displayed branch
coverage, pole order, normal crossings, and RLCT extraction.

## Verification

- Focused Lean check:
  `lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`
- Independent xhigh pen-and-paper scout confirmed the finite-set implication
  and the supplied hypotheses that must remain explicit.
