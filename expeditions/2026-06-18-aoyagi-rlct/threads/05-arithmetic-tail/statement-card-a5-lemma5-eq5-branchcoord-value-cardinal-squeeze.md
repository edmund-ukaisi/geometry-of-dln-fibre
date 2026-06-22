# Statement card - A5 Lemma 5 Eq5 branch-coordinate/value cardinal squeeze

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchBlock_of_branchCoord_leftEndpoint`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.valueLabel_of_branchK_value`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_branchCoord_leftEndpoint_branchK_value_terminalEndpointBase`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_branchCoordVal_cardSqueeze`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_branchCoordVal_cardSqueeze`

## Claim

For a supplied terminal-candidate family, supplied nonbase branch-coordinate
correctness plus supplied left-endpoint `branchS` labels imply the selected
block membership needed by the value-label branch-injection theorem.  Supplied
`branchK`/value synchronisation implies the Sigma-label value relation.  With
the terminal-endpoint base label, these adapters give branch-label injectivity
and compose with the existing terminal pAlpha counted-datum injection in the
finite cardinal squeeze.

## Proved

Lean proves the two structured adapters, the derived branch-label injectivity
on `TC.fullBranches`, then conditional `TC.TerminalMinimumLabelExactness` and

```text
TC.terminalMinimumLabels.card = a * (N + 1 - a) + 1.
```

## Assumed

The supplied terminal-candidate family, selected cutpoints, nonbase branch
coordinate correctness, supplied left-endpoint `branchS` formula, supplied
`branchK`/value formula, terminal-endpoint base label, `a <= N+1`,
selected-width sum, source width inequalities, Eq5 piecewise source-vector
data for every terminal-minimum label, own-block membership for terminal
labels, last-point source range, selected-width source hypotheses, the
terminal-label Eq5 label formula, terminal-label nonbase inequality, and
terminal `(p, alpha)` injectivity.

## Deferred

Eq5 branch construction, source proof of branch-coordinate correctness, source
proof of branch source-label and value-label formulas, source production of
terminal Eq5 payloads, source proof of terminal `(p, alpha)` injectivity,
direct counted-datum back-to-label coverage, source-backed no-extra
terminal-minimum coverage, Lemma 5 order count, pole order, normal crossings,
and RLCT extraction.

## Cited

None; this is finite Lean bookkeeping over supplied hypotheses and previously
formalized definitions.

## Verification

Focused Lean check:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean
```

## Review

Independent xhigh review passed.  Review artifact:
`review-lemma5-eq5-branchcoord-value-cardinal-squeeze-a5.md`.
