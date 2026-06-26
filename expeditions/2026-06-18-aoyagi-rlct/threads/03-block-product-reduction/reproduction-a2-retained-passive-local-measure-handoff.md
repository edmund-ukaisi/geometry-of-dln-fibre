# Reproduction - A2 Retained-Passive Local-Measure Handoff

Date: 2026-06-26.

Status: reproduced and formalised in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean`.

## Target

The existing local-measure consumer

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_subset_localSource
```

takes a supplied local source and requires:

- local coverage of the source-rank stratum by that local source inside an
  open neighborhood;
- measurability of the local source;
- residual positivity and negative-power integrability on the local source;
- local loss and density bounds in `nhdsWithin x0 localSource`.

The retained-passive work now supplies the first two inputs for

```text
paperEndpointFixedBaseRetainedPassiveP13LocalSource.
```

The narrow target is therefore to specialize the consumer to this local source
while leaving the residual and loss/density hypotheses explicit.

## Reproduction

Let

```text
localSource =
  paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U0 hU0 Cedge.
```

Assume `Cedge` is globally continuous and is the self-base edge family at
`x0`:

```text
Cedge x0 = fun p => LinearMap.toContinuousLinearMap (reverseEdge W B p).
```

The retained-passive coverage theorem gives an open set `Ulocal` with
`x0 in Ulocal` and

```text
Ulocal ∩ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge
  ⊆ Ulocal ∩ localSource.
```

The retained-passive measurability theorem gives

```text
MeasurableSet localSource.
```

Substituting these two facts into the existing source-stratum/local-source
consumer proves the finite p.13 regular-coordinate integral over

```text
U ∩ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge
```

for some open `U` containing `x0`, provided the residual positivity,
residual negative-power integrability, loss lower bound, and density bounds
are supplied on `localSource`.

## Boundary

This is a consumer specialization.  It removes only the coverage and
measurability fields for the retained-passive determinant-chart local source.
It does not construct the source-measure pushforward, prove residual
integrability, prove the loss/density bounds, compute a Jacobian density,
prove normal crossings, determine a pole order, or extract an RLCT.
