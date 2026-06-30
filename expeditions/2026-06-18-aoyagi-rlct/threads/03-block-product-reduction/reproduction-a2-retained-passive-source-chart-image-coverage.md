# Reproduction - A2 Retained-Passive Source-Chart Image Coverage

Date: 2026-06-30.

Status: pen-and-paper check before Lean. This is retained-passive
determinant-chart image coverage only.

## Question

The existing self-base coverage theorem gives an open neighborhood
`Ulocal` contained in

```text
paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U0 hU0 Cedge.
```

Can we expose the actual retained-passive determinant-chart coordinate datum
whose source chart realizes `Cedge x` for points `x in Ulocal`?

## Calculation

By definition,

```text
paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U0 hU0 Cedge
```

is the preimage of the ambient source edge-family set

```text
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W B U0 hU0
```

under `Cedge`. Thus `x in Ulocal` implies

```text
Cedge x in paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet.
```

The retained-passive source chart is already a homeomorphism

```text
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamily_homeomorph
```

from determinant-chart coordinate data to that source edge-family set. Apply
the inverse of this homeomorphism to the subtype point `Cedge x`. Its
right-inverse law gives

```text
paperEndpointFixedBaseRetainedPassiveP13SourceChart data = Cedge x.
```

The source-rank stratum in the theorem is only a consumer-shaped restriction:
the same witness exists for every `x in Ulocal`, hence also for
`x in Ulocal inter sourceStratum`.

## Lean Target

Add to
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean`:

```text
exists_open_paperEndpointFixedBaseRetainedPassiveP13SourceChart_image_coverage_of_selfBase
```

## Nonclaims

This is retained-passive determinant-chart image coverage. It does not prove
Case 2 passive-theta or selected-entry coverage, source-image equality with a
source-rank stratum, original/source-prior transport, Haar/Jacobian transport,
normal crossings, pole order, or RLCT extraction.
