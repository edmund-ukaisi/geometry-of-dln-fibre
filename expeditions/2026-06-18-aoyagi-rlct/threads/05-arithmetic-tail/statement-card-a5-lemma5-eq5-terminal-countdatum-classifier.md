# Statement card - A5 Lemma 5 Eq5 terminal counted-datum classifier

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_widthBound`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_blockWidth`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_leftEndpointMin`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_offSelected`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_offSelected_lt`

## Claim

For a supplied terminal-candidate family, if every label in
`TC.terminalMinimumLabels` has supplied Eq5 own-block common-domain payload
data and the induced counted-datum map is injective, then
`TC.TerminalMinimumCountDatumClassifier` exists.

## Proved

Lean defines the classifier by

```text
label |-> some (pOf label, T label label.1)
```

and proves `mapsTo` using the existing Eq5 own-block common-domain payload.
The source-shaped variants derive the selected-width bound from block-width,
left-endpoint/minimum, off-selected, or strict off-selected dominance
hypotheses.

## Assumed

Terminal-candidate family `TC`, Eq5 piecewise source vector data for every
terminal-minimum label, own-block membership, last-point source range,
selected-width source hypotheses, Eq5 label formula, nonbase inequality, and
`Set.InjOn classify TC.terminalMinimumLabels`.

## Deferred

Eq5 branch construction, proof that every terminal-minimum label has such an
Eq5 witness, nonbase status, classifier injectivity, back-to-label coverage,
`UpperBoundClassifier`, exactness, Lemma 5 order count, pole order, normal
crossings, and RLCT extraction.

## Verification

Focused Lean check:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean
```
