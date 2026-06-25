# Review - A2 local-source adapted-loss finite-integral socket

Date: 2026-06-25.

## Verdict

Accepted at the stated scope.

The theorem is the local-source version of an already-landed source-rank
socket.  Its only mathematical move is multiplication of the adapted lower
bound by a positive comparison constant before applying the local-source p.13
finite-integral theorem.

## Boundary Check

The statement keeps every substantive analytic or chart-side input explicit:
the adapted lower bound, adapted-to-loss comparison, residual source
hypotheses, and density bounds.  It does not construct a chart or infer
pushforward/Jacobian data.

## Next Consumer

This theorem is the right intermediate for a future local-source original-loss
wrapper, once a downstream chart package supplies local source-filter product
family bounds rather than full source-rank-stratum bounds.
