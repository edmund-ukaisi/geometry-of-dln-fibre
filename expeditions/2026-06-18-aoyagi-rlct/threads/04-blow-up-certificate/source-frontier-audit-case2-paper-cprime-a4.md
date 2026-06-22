# Source-frontier audit - A4 Case 2 paper Cprime

Auditor: xhigh source/frontier scout `Gauss`.

Status: audit passed; no new broad reproduction of the local `C'=Q^-1*C`
algebra is needed.

## Question

After the A5 alpha-injection cardinal-squeeze checkpoint, a source-frontier
scout recommended returning to A4 Case 2 and reproducing the source-produced
following factor `C'=Q^-1*C` as a total source-coordinate object.  This audit
checks whether that reproduction is genuinely missing or already covered by
existing A4 terminal-frontier artifacts.

## Audit Result

The broad local `Q^-1*C` calculation is already substantially present.
Existing Lean and artifacts cover:

- `case2DisplayedPaperCprime`: Aoyagi's paper transported factor
  `C'=Q^-1*C`, formed from source-coordinate `C`;
- `case2DisplayedPaperCprimeTop` and
  `case2DisplayedPaperCprimeTop_apply`: the surviving pivot-row correction;
- `case2DisplayedPaperCprimeTail` and
  `case2DisplayedPaperCprimeTail_apply`: unchanged lower tail;
- `case2DisplayedPostPivotFreeFollowingFactor_paperCprime_eq_sourceFollowingFactor_succ`:
  the post-pivot tail of paper `C'` is the next same-stage source following
  factor;
- `sourceChartMap_paperCprimeWeightedLowerRows_withCorrectedPostData`: the
  weighted lower-row handoff specialized to paper `C'`;
- `SuppliedTerminalCprimeBridge`: the terminal bridge recording supplied
  old-row and pivot-row equations.

There is not a single named total source-coordinate object for paper `C'`.
The closest existing total-source constructor is the reverse-direction
zero-extension `case2DisplayedConstructedSourceFollowingFactor`, which
represents any supplied pivot-first matrix as a total source-coordinate
function.  If a single paper-`C'` total-source adapter becomes useful, it
should be a thin adapter over the existing definitions, not a new source
reproduction.

## Missing Frontier

The genuinely missing A4 slice is not more local `Q^-1*C` algebra.  It is
chart/source production of the full successor object or successor
following-product data from the displayed Case 2 chart across the continuing
and terminal branches.  In particular, a future reproduction/theorem must
produce, rather than supply, the relevant old top rows, transported pivot row,
post-pivot tail, and suffix handling for the next `C'^(S+1)` or successor
following-product package.

Current terminal bridges deliberately stop at supplied row equations.  They
are correct boundary APIs, not chart-production theorems.

## Kill Conditions

- Do not call lower-tail identities a full `C'^(S+1)` construction.
- Do not treat `SuppliedTerminalCprimeBridge` as chart production.
- Do not replace actual-width exhaustion with prefix exhaustion or failed
  continuation.
- Do not relabel row-exhausted wide-next terminal rows as original rows.
- Do not infer recurrence/exponent post-data, chart coverage, Jacobian
  arithmetic, normal crossings, pole order, or RLCT from these local bridges.
