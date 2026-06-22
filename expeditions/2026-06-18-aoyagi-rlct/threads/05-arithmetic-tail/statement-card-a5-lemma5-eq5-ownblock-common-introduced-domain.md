# Statement card - A5 Lemma 5 Eq5 own-block common introduced domain

## Lean Names

- `DLNFibre.DLN.Aoyagi.introducedLabel_mono_state`
- `DLNFibre.DLN.Aoyagi.introducedLabelFinset_subset_of_state_le`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_widthBound`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_blockWidth`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_leftEndpointMin`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_offSelected`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_offSelected_lt`

## Claim

Introduced-label membership is monotone under explicit forward movement of
the blow-up state, and the Eq5 own-block counted/introduced payload can be
lifted from the local state `(S,k)` to any supplied later/common state.

## Proved

Lean proves:

```text
introducedLabel L n S J s k ->
introducedLabel L n S' J' s k
```

under `S < S' or (S = S' and J <= J')`, plus the corresponding finite-set
subset.  The Eq5 wrappers combine this subset with the existing own-block
payloads.

## Assumed

For Eq5 wrappers: the Eq5 piecewise source vector, selected-width/source
inequalities, last-point source range, selected-width bound or source-shaped
width dominance hypotheses, label formula, nonbase inequality, and target
state comparison.

## Deferred

Terminal state construction, terminal introduced-domain coverage, Eq5 branch
construction, nonbase status, classifier injectivity, back-to-label coverage,
Lemma 5 order count, pole order, normal crossings, and RLCT extraction.

## Verification

Focused checks:

```text
lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic
lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5CountDatumBridge.lean
```
