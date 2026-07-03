# A2 source-density continuity density-bounds package

Date: 2026-07-03.

## Calculation

The eventual-density coordinate-source handoff needs finite constants
`CJ` and `CS` and eventual pointwise upper bounds

```text
forall eventually z in nhds z0, jacobianDensity z <= CJ,
forall eventually z in nhds z0, sourceDensity z <= CS.
```

The Jacobian side is no longer a socket.  For

```text
Y z =
  case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
    n hS hcont hnext z eNext e
```

and

```text
jacobianDensity z =
  ENNReal.ofReal
    (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
      (M := 1) (Y z)),
```

the determinant-sector hypothesis at `z0` and the retained-passive
local-unit Jacobian theorem give a finite eventual upper bound

```text
exists CJ < top, forall eventually z in nhds z0, jacobianDensity z <= CJ.
```

The source side is deliberately handled as a local boundedness socket, not
as a source-density construction.  Write

```text
sourceChart =
  case2PassiveThetaWithFollowingFactorEndpointSourceChart
    W2 B2 n hS hcont hnext hU0 eNext e
```

and

```text
sourceDensity z = sourceImageDensity (sourceChart z).
```

Since `sourceImageDensity` is an arbitrary function in the current endpoint
handoff, there is no mathematical reason it must be locally bounded.  The
honest elementary assumption is:

```text
ContinuousAt sourceDensity z0,
sourceDensity z0 < top.
```

The generic ENNReal continuity lemma then chooses a finite `CS` and gives

```text
forall eventually z in nhds z0, sourceDensity z <= CS.
```

Combining the two witnesses packages exactly the two eventual upper-density
inputs for the downstream coordinate-source finite-integral theorem.

## Lean Target

The package theorem is:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_finite_eventually_jacobianDensity_sourceDensity_bounds_case2PassiveThetaWithFollowingFactorEndpointSourceChart_of_sourceDensity_continuousAt_lt_top
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

It uses:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_finite_eventually_le_jacobianDensity_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
exists_lt_top_eventually_le_of_continuousAt_lt_top
```

## Boundary

This proves only a density-bounds package.  It does not prove the finite
integral endpoint itself, does not construct `sourceImageDensity`, and does
not prove continuity or finiteness of the composed source density.  Those
remain separate source-density construction or prior-transport obligations.

It also proves no determinant-Haar/raw-Haar transport, original-prior
transport, normal crossings, pole order, or RLCT extraction.
