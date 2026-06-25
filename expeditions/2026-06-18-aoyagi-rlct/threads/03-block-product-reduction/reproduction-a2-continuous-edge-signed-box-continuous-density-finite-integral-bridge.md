# Reproduction - A2 continuous-edge signed-box continuous-density finite-integral bridge

Date: 2026-06-25.

Status: pen-and-paper reproduction for a source-measurability and edge-matrix
measurability handoff.

## Source Anchor

The signed-box continuous-density finite-integral bridge still asks separately
for:

```text
MeasurableSet S,
Measurable fixedBaseEdgeMatrixFamily,
```

where

```text
S = paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge.
```

The source-rank measurability theorem already proves `MeasurableSet S` from a
globally continuous edge family `Cedge`.  The residual-coordinate
measurability theorem asks for the endpoint fixed-basis matrix family because
that is the finite matrix family consumed by the deterministic p.13 suffix
recursion.  If `Cedge` is globally continuous, this matrix family is globally
continuous, hence measurable.

This slice composes those two elementary continuity-to-measurability facts
with the already-landed signed-box continuous-density finite-integral bridge.

## Calculation

Assume

```text
hCedge : Continuous Cedge.
```

For each edge `p`, continuity of the projection

```text
fun x => Cedge x p
```

follows by composing `hCedge` with `continuous_apply p`.  The endpoint
fixed-basis coordinate map

```text
fun f =>
  LinearMap.toMatrix
    (paperEndpointFixedBaseBasis W B U0 hU0 p.castSucc)
    (paperEndpointFixedBaseBasis W B U0 hU0 p.succ)
    (f : reverseVertex W p.castSucc ->ₗ reverseVertex W p.succ)
```

is continuous by `continuous_linearMap_toMatrix`.  Therefore the composed
family

```text
fun x =>
  paperEndpointFixedBaseEdgeMatrixOfReverseEdges
    W B U0 hU0 (fun p => Cedge x p)
```

is continuous as a finite Pi-valued matrix family, hence measurable.

Separately,

```text
measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous
```

turns the same global continuity of `Cedge` into measurability of the
source-rank stratum.  It uses fixed finite-basis matrix rank loci for the raw
edge ranks; it does not use or assert exact-rank openness.

The signed-box continuous-density bridge can now be called with those two
derived hypotheses.  All other analytic/source inputs remain unchanged:
`0 < t`, signed-box chart a.e.-measurability, weighted pushforward,
source-density a.e.-measurability/nonnegativity/upper bound, residual monomial
lower bound, positive continuous product density at `(x0,0)`, and the local
regular-fiber loss lower bound.

## Boundaries

This is only a continuity-to-measurability wrapper.  It assumes global
`Continuous Cedge`; it does not derive anything from merely
`ContinuousAt Cedge x0`.  It does not claim exact-rank/source-rank openness.
It does not introduce raw `Measurable Cedge` over continuous-linear-map spaces.

It does not construct Aoyagi's analytic chart, prove the weighted pushforward
identity, transport Jacobian or prior density, compare with the original
DLN/statistical loss, produce normal crossings, compute pole order, or extract
an RLCT.

## Kill Conditions

- If only `ContinuousAt Cedge x0` is available, this theorem does not apply.
- Do not use this theorem as a source-rank openness theorem.
- Do not treat the derived fixed-basis matrix measurability as a theorem about
  arbitrary raw `Measurable Cedge` hypotheses.
