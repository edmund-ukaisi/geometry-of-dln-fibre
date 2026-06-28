# Review - A2 retained-passive canonical product-density finite-integral handoff

Reviewer: xhigh `Linnaeus the 2nd`

Verdict: PASS.

## Findings

The base point is correct for the identity edge-family source map.  The
`sourceData` package is centered at the reverse-edge family, and the local
finite-integral socket receives `Cedge = id`; the required base equality is
discharged by `rfl`.

The measure orientation is correct.  The source measure is

```text
mu = Measure.map sourceChart (m.restrict T),
```

while the chart-side residual hypotheses are under

```text
(m.restrict S).withDensity
  (fun z => ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt z)).
```

The proof first invokes
`residualSourceHypotheses_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet`
to obtain `mu.restrict localSource`-a.e. residual positivity and
`residualNegPowerIntegrableOn localSource mu t`, then calls the existing
retained-passive p.13 local finite-integral theorem.

The chart-side residual positive-set measurability, chart-side residual
positivity, and chart-side finite residual integral remain explicit
hypotheses.  The local loss lower bound and density bounds also remain
explicit.  The theorem introduces no original source prior, selected-entry
signed-box density, monomial lower bound, normal-crossing production,
pole-order theorem, or RLCT theorem.

The explicit `[SFinite m]` hypothesis is a Lean typeclass bridge to infer
`SFinite` for `Measure.map sourceChart (m.restrict T)`, matching the existing
local finite-integral socket's `[SFinite μ]` requirement.  The reviewer noted
that an API taking `[SFinite μ]` directly could be weaker, but this is not a
mathematical boundary problem for the canonical chart-produced measure.

## Verification

The focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure
```

`git diff --check` passed, and the touched files contain no forbidden Lean
markers.
