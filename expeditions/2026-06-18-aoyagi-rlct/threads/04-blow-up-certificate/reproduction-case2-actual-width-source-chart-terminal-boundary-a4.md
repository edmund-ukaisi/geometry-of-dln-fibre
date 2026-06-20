# A4 Case 2 Actual-Width Source-Chart Terminal Boundary

Status: reproduced the actual-width source-chart terminal boundary package.
This is a composition of already proved source-chart terminal source-suffix
and relabelled post-data projections.

## Source Anchor

On Aoyagi PDF pp. 21-22, the stopped Case 2 terminal display rewrites the
local product as a terminal prefix product

```text
diag(b_1,...,b_J,b'_(J+1),...,b'_(M(S+1))) *
C'^(S+1) * prod_{s=S+2}^L C^(s).
```

In the actual next-width exhausted branch

```text
n(S+1)=J+1,
```

the terminal prefix rows are `1..J+1`, the post-pivot column correction in
the top row of `Q^-1 C` is empty, and the terminal `C'` rows are original
source rows `1..J+1`.

## Pen-And-Paper Reproduction

The previous source-chart terminal source-suffix theorem gives the entry-ideal
equality

```text
old-top/source-suffix product
  =
terminal weight * original source rows(1..J+1) * source suffix.
```

The displayed source chart fixes the selected pivot value

```text
v = case2DisplayedSourceChartMap(...)(J+1,J+1),
```

so the concrete post recurrence state is

```text
pre.case2Succ v.
```

Under actual-width exhaustion, old state `(S,J+1)` and relabelled state
`(S+1,0)` have the same introduced-label domain.  Therefore the already proved
relabel projections transport:

- level/least-value invariants to `(S+1,0)`;
- all-label exponent certificates to `(S+1,0)`;
- the surviving pivot weight to the relabelled post-state weight.

Combining these facts gives a boundary package:

```text
entry-ideal terminal equality
and relabelled level invariants
and relabelled exponent-domain certificates.
```

## Lean Shape

The proved theorem is:

```text
sourceChart_actualWidth_terminalOriginalRowsBoundary
```

It returns a conjunction of:

- the source-chart terminal source-suffix entry-ideal equality with original
  terminal rows;
- `IntroducedLabelLevelInvariants` for `(S+1,0)`;
- `IntroducedLabelExponentCertificates` for `(S+1,0)`.

## Boundaries

- Actual-width exhaustion `n(S+1)=J+1` is essential.
- This is not a row-exhausted wide-next theorem.
- `chartFamily`, source following rows `C`, and suffix matrices `Ctail` remain
  supplied.
- The theorem does not prove source-produced `C'^(S+1)`, chart coverage,
  chart-produced post-data, Jacobian arithmetic, normal crossings, RLCT
  extraction, termination, transition invariance, automatic Case 2 gap/tail
  transport, or printed-vector repair.
