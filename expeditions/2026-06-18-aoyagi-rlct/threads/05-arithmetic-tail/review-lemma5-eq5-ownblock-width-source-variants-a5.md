# Review - Lemma 5 Eq5 own-block width-source variants

Reviewer: xhigh Lean/API reviewer `Helmholtz`.

Verdict: pass.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5CountDatumBridge.lean`
- `reproduction-lemma5-eq5-ownblock-width-source-variants-a5.md`
- `statement-card-a5-lemma5-eq5-ownblock-width-source-variants.md`

## Findings

No findings.

## Lean/API Notes

The `leftEndpointMin`, `offSelected`, and `offSelected_lt` variants derive
only the selected-width bound needed by the existing own-block
counted/introduced payload, then delegate to the raw-width theorem.  The
source-shaped width hypotheses remain explicit, and the conclusions remain
limited to counted-datum membership, `T S = k - 1`, and introduced-label
membership.

The review assumes the existing selected-width dominance APIs and upstream
Eq5 source-label/count-datum bridges are trusted.  It checked only this
adapter diff.

## Verification

Focused Lean check:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5CountDatumBridge.lean
```
