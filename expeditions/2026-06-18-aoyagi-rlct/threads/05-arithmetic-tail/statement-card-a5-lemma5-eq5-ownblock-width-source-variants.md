# Statement card - A5 Lemma 5 Eq5 own-block width-source variants

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_leftEndpointMin`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_offSelected`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_offSelected_lt`

## Claim

For one supplied Eq5 own-block branch, the counted-datum and introduced-label
payload follows from the existing left-endpoint/minimum or off-selected width
dominance hypotheses.

## Proved

Lean derives the needed selected-width bound using:

- `AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block_of_leftEndpoint_min`;
- `AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block_of_offSelected`;
- `AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block_of_offSelected_lt`.

It then reuses the existing raw-width own-block payload.

## Assumed

The Eq5 piecewise source vector, selected-width/source inequalities, the
corresponding source-shaped width dominance hypotheses, last-point source
range, label formula, and nonbase inequality `T S != baseValue p`.

## Deferred

Eq5 vector construction, nonbase status, terminal-exponent and least-value
certificates, classifier construction, back-to-label coverage, Lemma 5 order
count, pole order, normal crossings, and RLCT extraction.

## Verification

Focused Lean check:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5CountDatumBridge.lean
```
