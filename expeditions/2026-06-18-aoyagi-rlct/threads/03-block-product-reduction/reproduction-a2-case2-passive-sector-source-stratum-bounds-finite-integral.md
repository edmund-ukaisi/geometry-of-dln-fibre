# Reproduction - A2 Case 2 passive-sector source-stratum-bounds finite integral

Date: 2026-06-29.

Status: reproduced, formalised, and reviewed.

## Question

The passive-sector finite-integral handoff uses local loss and density bounds
on the retained-passive local source.  Downstream p.13 estimates are often
stated on the source-rank stratum.  Can we prove the same chart-produced
passive-sector finite-integral conclusion with loss and density hypotheses on
`sourceStratum` instead?

Answer: yes.  The existing retained-passive local-source neighborhood theorem
does not prove source-rank coverage.  It supplies only a local inclusion:

```text
Ulocal ∩ sourceStratum ⊆ Ulocal ∩ localSource.
```

That inclusion is exactly what the source-stratum-bounds local-measure consumer
needs.

## Calculation

The passive selected-entry punctured-sector residual-source handoff gives an
open coordinate-domain sector `V` around `z0`.  For

```text
mu = Measure.map sourceChart (sourceMeasure.restrict V),
localSource = retainedPassiveP13LocalSource W2 B2 U0 hU0 id,
```

it supplies:

```text
mu.restrict localSource = mu,
mu.restrict localSource-a.e. residual square-sum positivity,
residualNegPowerIntegrableOn localSource mu t.
```

The source-rank stratum

```text
sourceStratum = paperEndpointFixedBaseSourceRankStratum W2 B2 id r rEdge
```

is measurable because `id : EdgeFamily -> EdgeFamily` is continuous.  The
self-base retained-passive local-source theorem gives an open `Ulocal`
containing the fixed-base edge family `base` and the local inclusion

```text
Ulocal ∩ sourceStratum ⊆ Ulocal ∩ localSource.
```

Thus the generic source-stratum-bounds consumer applies with:

```text
hpos_local  : residual positivity on mu.restrict localSource,
hbase_local : residualNegPowerIntegrableOn localSource mu t,
hloss       : loss lower bound on nhdsWithin base sourceStratum,
hdensity_*  : density bounds on nhdsWithin base sourceStratum.
```

It returns an open edge-family neighborhood `U` around `base` and proves the
finite integral over

```text
(mu.restrict (U ∩ sourceStratum)).prod nu.
```

## Lean target

The theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_withPassive_puncturedSector_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean
```

It should call:

```text
exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_passiveProductMeasure_finiteMass
exists_open_paperEndpointFixedBaseRetainedPassiveP13LocalSource_coverage_of_selfBase
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_bounds_locally_subset_localSource
```

## Verification

Lean now proves the target theorem in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean`.
The controller checked it with local Lake:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff
env LEAN_NUM_THREADS=3 lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
```

`lean/scripts/sorries`, `git diff --check`, and a direct axiom probe also passed.
The theorem reports only `[propext, Classical.choice, Quot.sound]`.

Xhigh source/scope reviewer `Mencius the 4th` and xhigh Lean/API reviewer
`Dalton the 4th` returned PASS; see
`review-a2-case2-passive-sector-source-stratum-bounds-finite-integral.md`.

## Kill conditions

- Do not claim source-rank coverage; only use the local inclusion into
  `localSource`.
- Do not claim determinant-chart Haar transport or source-prior transport.
- Do not claim passive/source Jacobian transport.
- Do not claim source-image equality or exact localized residual marginal
  equality.
- Do not construct normal crossings, compute pole order, or extract RLCT.
