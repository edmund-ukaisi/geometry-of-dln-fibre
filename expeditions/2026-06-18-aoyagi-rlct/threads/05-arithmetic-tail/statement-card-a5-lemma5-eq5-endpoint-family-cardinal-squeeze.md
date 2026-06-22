# Statement card - A5 Lemma 5 Eq5 endpoint-family cardinal squeeze

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5EndpointFamily_branchCoordVal_cardSqueeze`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5EndpointFamily_branchCoordVal_cardSqueeze`

## Claim

For a supplied terminal-candidate family, if its nonbase supplied family is
explicitly equal to the strictest supplied Eq5 endpoint constructor, then the
existing branch-coordinate/value terminal cardinal squeeze can use the
endpoint constructor to supply the terminal nonbase branch-coordinate input.

## Proved

Lean proves conditional terminal-minimum exactness and

```text
TC.terminalMinimumLabels.card = a * (N + 1 - a) + 1.
```

The proof composes:

```text
branchCoord_of_toNonbase_eq_eq5EndpointCoverage
branchBlock_of_toNonbase_eq_eq5EndpointCoverage_leftEndpoint
valueLabel_of_branchK_value
terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze
terminalMinimumLabels_card_of_exactness
```

## Assumed

The supplied terminal-candidate family, selected cutpoints, terminal Eq5
payloads for all labels in `TC.terminalMinimumLabels`, terminal `(p, alpha)`
injectivity, terminal-label block/width/source hypotheses, terminal-label
nonbase inequalities, the supplied strict Eq5 endpoint constructor data,
explicit equality between `TC.family.toAoyagiLemma5SuppliedNonbaseFamily` and
that endpoint constructor, supplied `branchS` left-endpoint labels, supplied
`branchK`/value synchronization, and the terminal-endpoint base label.

## Deferred

Eq5 branch construction, source production of endpoint records, source-label
legality, proof of the terminal-family equality from Aoyagi's source,
base-filter survival for source records, source production of terminal Eq5
payloads, source proof of terminal `(p, alpha)` injectivity, direct
counted-datum back-to-label construction, source-backed no-extra
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

xhigh review passed after wording repair.  Review artifact:
`review-lemma5-eq5-endpoint-family-cardinal-squeeze-a5.md`.
