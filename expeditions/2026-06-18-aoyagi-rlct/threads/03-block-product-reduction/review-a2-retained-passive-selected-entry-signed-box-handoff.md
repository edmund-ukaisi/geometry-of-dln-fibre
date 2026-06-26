# Review - A2 retained-passive selected-entry signed-box handoff

Reviewer: Dewey the 3rd, xhigh read-only review.

## Findings

No blockers.

The theorem keeps `sourceChart`, `hsourceChart`, `hmap`, `hresidual_eq`, and
local loss/density bounds as hypotheses.  It therefore does not construct a
retained-passive chart, prove a weighted pushforward, identify a
Jacobian/source density, prove normal crossings, compute pole order, or extract
an RLCT.

The proof only specializes the selected-entry monomial-unit package and the
selected-entry critical inequality split, mirroring the precedent in
`SelectedEntrySignedBoxLocalMeasure.lean` and then calling the retained-passive
monomial-unit consumer.

## Residual risk

The theorem remains only as strong as the supplied retained-passive `hmap` and
`hresidual_eq`.  These are intentionally still unproved sockets.
