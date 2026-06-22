# Review - Lemma 5 Eq5 own-block block-width payload

Reviewer: xhigh Lean/API reviewer `Euclid`.

Verdict: pass.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5CountDatumBridge.lean`
- `reproduction-lemma5-eq5-ownblock-block-width-payload-a5.md`
- `statement-card-a5-lemma5-eq5-ownblock-block-width-payload.md`

## Findings

No findings.

## Lean/API Notes

The proof stays narrow.  It derives `1 <= p` from the Eq5 alpha hypotheses,
derives the selected-width bound via
`C.selectedWidthNat_le_actualWidth_of_block`, and delegates to the existing
width-bound payload.  The nonbase inequality `T S != baseValue p` remains a
hypothesis.

The theorem does not construct Eq5 vectors, classifier/back-to-label coverage,
Lemma 5 count or order, pole order, normal crossings, or RLCT extraction.

## Verification

Focused Lean check:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5CountDatumBridge.lean
```
