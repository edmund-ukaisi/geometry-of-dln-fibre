# Review - A4 source-current stack without chart family

Reviewers: xhigh subagents `Lagrange` and `Descartes`.

Verdict: pass.

## Findings

No blocking findings.

## Source/Fidelity Audit

Lagrange confirmed that this slice is below the hard source-production
boundary if it is documented as a chart-family-free finite row-stack wrapper.
Aoyagi's Case 2 display on PDF pp. 19-21 supports the displayed pivot chart,
`Q`, `C'_J = Q^-1 C_J`, `P`, `D'''_J`, and the continuing product identity.
This theorem only repackages that identity into source-current row
coordinates using existing row-reindex lemmas.

Required caveats are recorded next to the claim: the formula-level successor
block is not a chart-produced successor following object; the suffix remains
the supplied raw `sourceSuffixProduct`; no chart coverage, transition
regularity, coordinate-produced corrected post-data, Jacobian arithmetic,
normal crossings, pole order, termination, or RLCT content is implied; and
the theorem is only for the displayed pivot and continuing branch with
explicit `hnext`.

## Lean/API Audit

Descartes identified the smallest safe patch: rename the existing proof body
to

```text
sourceChartMap_continuingOldTopSourceSuffixSuccFollowingBlock_withoutChartFamily
```

remove only the `ChartRegular`, `TransitionRegular`, and `chartFamily`
binders, replace the base call by

```text
sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withoutChartFamily
```

and re-add the old theorem name as a compatibility wrapper.  Descartes also
checked that the only downstream Lean call site uses the old theorem name, so
preserving the old signature keeps downstream code source-compatible.

The implemented proof keeps the stabilizing local `hcurrent` and `hsuccessor`
type annotations and the explicit `(J := J)` old-top blocks.  The focused
Lean build passed.

## Caveat

This review is a finite row-bookkeeping/API review.  It does not review or
prove chart production, analytic regularity, normal crossings, pole order, or
RLCT extraction.
