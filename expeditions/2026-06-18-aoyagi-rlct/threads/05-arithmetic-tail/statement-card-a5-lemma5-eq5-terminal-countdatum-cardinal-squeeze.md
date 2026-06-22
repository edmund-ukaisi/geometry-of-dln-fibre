# Statement card - A5 Lemma 5 Eq5 terminal counted-datum cardinal squeeze

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_widthBound`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_blockWidth`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_leftEndpointMin`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_offSelected`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_offSelected_lt`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_eq_branchLabelImage_of_eq5OwnBlockCommon_widthBound_cardSqueeze`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_cardSqueeze`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_cardSqueeze`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_bijOn_terminalMinimumLabels_of_eq5OwnBlockCommon_widthBound_cardSqueeze`

## Claim

For a supplied terminal-candidate family, supplied Eq5 own-block common-domain
payloads for `TC.terminalMinimumLabels` give the terminal-minimum upper bound
after supplying counted-datum injectivity.  Adding supplied branch-label
injectivity and the selected-width sum gives equality with the supplied
branch-label image, terminal-minimum exactness, the exact finite count, and a
branch-label bijection.

## Proved

Lean composes:

- the Eq5 terminal counted-datum classifier constructor;
- `TC.terminalMinimumLabels_card_le_of_countDatumClassifier`;
- the existing cardinal-squeeze wrappers from a counted-datum classifier plus
  supplied branch-label injectivity.

The upper-bound statement is available for the raw selected-width bound and
for the block-width, left-endpoint/minimum, off-selected, and strict
off-selected variants.  The exactness/cardinality/bijection statements are
added for the raw selected-width bound interface.

## Assumed

The terminal-candidate family, `a <= N+1`, selected-width sum, Eq5 piecewise
source vector data for every terminal-minimum label, own-block membership,
last-point source range, selected-width source hypotheses, Eq5 label formula,
nonbase inequality, counted-datum injectivity, and, for exactness, branch-label
injectivity.

## Deferred

Eq5 branch construction, source production of terminal-minimum Eq5 payloads,
counted-datum injectivity, branch-label injectivity, counted-datum-preserving
back-to-label coverage, Lemma 5 order count from displayed branches, pole
order, normal crossings, and RLCT extraction.

## Verification

Focused Lean check:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean
```
