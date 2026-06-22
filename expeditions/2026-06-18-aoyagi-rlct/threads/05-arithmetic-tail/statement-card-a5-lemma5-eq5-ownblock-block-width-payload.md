# Statement card - A5 Lemma 5 Eq5 own-block block-width payload

## Lean Name

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_blockWidth`

## Claim

For one supplied Eq5 own-block branch, counted-datum membership and
introduced-label membership follow from block-local actual-width lower bounds,
without a separate raw selected-width hypothesis.

## Proved

Lean derives

```text
aoyagiSelectedWidthNat ell m p <= n(S+1)
```

from `C.block p S` and
`AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block`, then
reuses the existing raw-width payload.

## Assumed

The Eq5 piecewise source vector, selected-width/source inequalities,
block-local actual-width lower bounds, last-point source range, label formula,
and nonbase inequality `T S != baseValue p`.

## Deferred

Eq5 vector construction, nonbase status, terminal-exponent and least-value
certificates, classifier construction, back-to-label coverage, Lemma 5 order
count, pole order, normal crossings, and RLCT extraction.

## Verification

Focused Lean check:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5CountDatumBridge.lean
```
