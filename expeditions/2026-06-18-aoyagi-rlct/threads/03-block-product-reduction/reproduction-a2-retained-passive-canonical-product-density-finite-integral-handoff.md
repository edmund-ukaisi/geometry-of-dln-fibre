# A2 retained-passive canonical product-density finite-integral handoff

Status: controller reproduced; Lean proved and xhigh reviewed.

## Claim

The canonical retained-passive solved-`A1` raw-coordinate source measure can be
fed into the retained-passive p.13 finite-integral socket without an external
local-source residual hypothesis.  The residual positivity and residual
negative-power integrability on the retained-passive local source are supplied
by the canonical product-density residual handoff from chart-side hypotheses.

This is a composition result.  It does not prove the chart-side residual
positive-set measurability, chart-side residual positivity, or chart-side
finite residual integral.

## Setup

Let

```text
rho = Fin (finrank R U0)
kappa' = throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U0
S = topologyTupleDetChartSet
T = topologyTupleRawOrderSourceRecursiveDetChartSet
EFam = forall p : Fin (M+1),
  reverseVertex W p.castSucc ->L[R] reverseVertex W p.succ
base = fun p => LinearMap.toContinuousLinearMap (reverseEdge W B p)
sourceChart(y)
  = paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
      (ofTopologyTuple (topologyTupleEdgeRawOrderInverse y))
localSource = paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U0 hU0 id
mu = Measure.map sourceChart (m.restrict T)
nuChart = (m.restrict S).withDensity
  (fun z => ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt z)).
```

The source-data package is assumed for the identity edge-family source map and
the base reverse-edge family:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData W B U0 hU0 base id H r rEdge.
```

Then the base condition required by the retained-passive local finite-integral
socket is definitional:

```text
id base = base.
```

The continuity condition for the edge-family source map is also definitional,
because `id : EFam -> EFam` is continuous.

## Residual hypotheses

The previous checkpoint proved

```text
residualSourceHypotheses_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet.
```

Applied to the chart-side facts

```text
MeasurableSet {x | 0 < residualSquareSum(x)}
nuChart-a.e. z, 0 < residualSquareSum(sourceChart(rawOrder z))
int^- z, ofReal(residualSquareSum(sourceChart(rawOrder z))^(-t)) dnuChart < infinity,
```

it gives exactly the two local-source hypotheses expected by the retained-
passive p.13 local finite-integral theorem:

```text
mu.restrict localSource-a.e. x, 0 < residualSquareSum(x)
residualNegPowerIntegrableOn localSource mu t.
```

No residual lower bound by a monomial is introduced.  The negative-power
integral is still the chart-side input under the canonical product-density
weighted measure.

## Finite-integral socket

The retained-passive local finite-integral theorem

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource
```

takes:

```text
hCedge : Continuous id
hbase  : id base = base
hpos_local
hbase_local
hloss
hdensity_nonneg
hdensity_le
```

and returns an open neighborhood `U` of `base` such that the p.13 regular-
coordinate product integral over

```text
(mu.restrict (U inter sourceStratum)).prod nuReg
```

is finite.  Substituting the two residual hypotheses from the canonical
product-density residual handoff gives the desired canonical product-density
finite-integral handoff.

If Mathlib does not infer sigma-finiteness or s-finiteness from the chart Haar
measure hypothesis, the wrapper should keep `[SFinite m]` explicit.  This is
only the typeclass needed to infer `SFinite (Measure.map sourceChart
(m.restrict T))` for the local finite-integral socket.

## Boundary

This checkpoint is a local chart-measure composition.  It removes the retained-
passive local residual hypotheses for the canonical product-density source
measure, replacing them by chart-side residual hypotheses under `nuChart`.

It does not construct an original source prior, identify a selected-entry
signed-box source density, prove a monomial residual lower bound, produce
normal crossings, compute pole order, or extract an RLCT.

## Kill conditions

- The source-data package is not centered at the reverse-edge base family for
  the identity source map.
- The canonical source measure in the finite-integral conclusion is not
  definitionally `Measure.map sourceChart (m.restrict T)`.
- The residual handoff is accidentally stated for the abstract actual
  determinant density rather than the named solved-`A1` product density.
- The theorem hides chart-side residual positivity or finite residual
  integrability instead of keeping them explicit.
