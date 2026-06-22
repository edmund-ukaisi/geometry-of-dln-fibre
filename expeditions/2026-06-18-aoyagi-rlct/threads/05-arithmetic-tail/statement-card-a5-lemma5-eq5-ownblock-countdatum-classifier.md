# Statement card - A5 Lemma 5 Eq5 own-block counted-datum classifier

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_widthBound`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_blockWidth`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_leftEndpointMin`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_offSelected`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_offSelected_lt`

## Claim

A finite supplied family of Eq5 own-block source labels gives an
`AoyagiLemma5CountDatumClassifier` once every label has the existing one-branch
payload hypotheses and the counted-datum map is supplied injective on the
label set.

## Proved

Lean defines

```text
classify(label) = some (pOf label, T label label.1)
```

and proves the `mapsTo` field using the existing Eq5 own-block payload.  The
source-shaped variants derive the selected-width bound from block-width,
left-endpoint/minimum, off-selected, or strict off-selected dominance
hypotheses.

## Assumed

The finite label set, Eq5 piecewise source vector for every label, own-block
membership, last-point source range, selected-width source hypotheses, Eq5
label formula, nonbase inequality, and `Set.InjOn classify labels`.

## Deferred

Eq5 branch construction, nonbase status, classifier injectivity from the
source, terminal introduced-domain lifting, back-to-label coverage,
terminal-minimum exactness, Lemma 5 order count, pole order, normal crossings,
and RLCT extraction.

## Verification

Focused Lean check:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5CountDatumBridge.lean
```
