# Statement card - A5 Lemma 5 Eq5 endpoint-family block-width cardinal squeeze

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze`

## Claim

For a supplied terminal-candidate family whose nonbase family is explicitly
equal to the strictest supplied Eq5 endpoint constructor, the endpoint-family
cardinal squeeze can use a blockwise actual-width hypothesis instead of a
per-terminal-label width bound.

## Proved

Lean proves conditional terminal-minimum exactness and

```text
TC.terminalMinimumLabels.card = a * (N + 1 - a) + 1.
```

The only new step is the derivation of the per-label width bound from
`cut.selectedWidthNat_le_actualWidth_of_block` and the supplied label-block
hypothesis.  The proof then reuses the width-bound endpoint-family cardinal
squeeze.

## Assumed

The supplied terminal-candidate family, selected cutpoints, terminal Eq5
payloads for all labels in `TC.terminalMinimumLabels`, terminal `(p, alpha)`
injectivity, terminal-label block/source hypotheses, terminal-label nonbase
inequalities, blockwise actual-width bounds, the supplied strict Eq5 endpoint
constructor data, explicit equality between
`TC.family.toAoyagiLemma5SuppliedNonbaseFamily` and that endpoint constructor,
supplied `branchS` left-endpoint labels, supplied `branchK`/value
synchronization, and the terminal-endpoint base label.

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

Focused Lean checks and full library checks pass:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.Lemma5Eq5TerminalClassifier
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build reports only pre-existing Core warnings.

## Review

xhigh review passed.  Review artifact:
`review-lemma5-eq5-endpoint-family-blockwidth-cardinal-squeeze-a5.md`.
