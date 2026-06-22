# Review - Lemma 5 Eq5 own-block counted-datum classifier

Reviewer: xhigh Lean/API reviewer `Rawls`.

Verdict: pass.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5CountDatumBridge.lean`
- `reproduction-lemma5-eq5-ownblock-countdatum-classifier-a5.md`
- `statement-card-a5-lemma5-eq5-ownblock-countdatum-classifier.md`

## Findings

No findings.

## Lean/API Notes

The adapters are conservative.  The `mapsTo` field is proved from the
existing one-branch Eq5 own-block counted/introduced payload, and classifier
injectivity remains an explicit supplied hypothesis.  The `label.1` and
`S+1` indexing matches the existing own-block and width-bound APIs.

The comments and statement card avoid claiming Eq5 construction, nonbase
proof, terminal-domain lifting, coverage, order count, or RLCT consequences.

Residual risk: the adapters intentionally carry stronger source-label payload
hypotheses than the bare counted-datum classifier needs, and they still
depend on supplied injectivity and nonbase hypotheses.

## Verification

Focused Lean check from the nested Lake project root:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5CountDatumBridge.lean
```
