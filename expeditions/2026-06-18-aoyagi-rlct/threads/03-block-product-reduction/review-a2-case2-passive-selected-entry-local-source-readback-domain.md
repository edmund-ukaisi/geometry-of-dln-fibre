# Review - A2 Case 2 Passive Selected-Entry Local Source-Readback Domain

Date: 2026-06-29.

## Verdict

PASS.

Two independent xhigh read-only reviews found no issues.

## Lean/API Review

Reviewer: McClintock the 3rd.

Findings:

- The theorem assumes continuity of passive fields and only basepoint
  determinant-unit hypotheses.
- The open set is the preimage of the retained determinant-chart set.
- The conclusion is limited to local-source membership and full source-readback
  equality.
- Supporting APIs match the scope: the Case 2 determinant bridge uses only
  `Ctop.det` and passive `A1` determinant units, determinant-chart openness is
  the retained-passive topology-tuple openness theorem, and readback uses the
  fixed-base edge-matrix equality plus `sourceReadback_edgeMatrix_eq`.

Residual risk noted by reviewer: the review was read-only and did not rerun
Lean; the controller already ran focused and aggregator builds.

## Source-Scope Review

Reviewer: Galileo the 3rd.

Findings:

- The reproduction note matches Aoyagi pp. 10-13 on the block substitutions
  and keeps the p.13 lower-right order as `prod C - F3 F2`.
- The passive fields remain independent: `A1passive`, `F2`, `A3passive`,
  `Ctop`, and `F3` are supplied separately, while selected-entry coordinates
  build only the residual `C` family.
- The determinant domain is scoped correctly as `Ctop.det` plus passive `A1`
  determinant units.
- No source-prior, Haar, Jacobian, normal-crossing, RLCT, source-image, or
  coverage overclaim was found.

Residual risk noted by reviewer: upstream selected-entry and retained-passive
lemmas were not fully re-audited beyond this boundary check.

## Controller Response

No code changes were needed after review.  The statement card and ledgers were
updated from review pending to review PASS.
