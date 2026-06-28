# Review: A2 retained-passive canonical chart selected-entry square-sum bridge

Reviewer: xhigh `Dirac the 3rd`

Verdict: PASS after statement-card status correction.

## Findings

No Lean soundness issue was found.  The proof follows from the banked canonical
residual-factor readout, the explicit supplied residual-factor matrix identity,
`AoyagiResidualBlockCoordinateIndex.value_matrix`, finite reindexing by the
residual-coordinate equivalence, and the selected-entry residual square-sum
lemma.

The reviewer found one documentation lag: the statement card still said the
Lean proof was pending after the theorem had been implemented.  The card was
updated to record the proved theorem and verification gates.

## Nonclaim check

The theorem does not prove or assume away the missing full suffix
selected-entry product construction.  It also does not claim residual
zero-locus nullity, chart-side a.e. positivity, negative-power integrability,
density transport, normal crossings, pole order, or RLCT extraction.

