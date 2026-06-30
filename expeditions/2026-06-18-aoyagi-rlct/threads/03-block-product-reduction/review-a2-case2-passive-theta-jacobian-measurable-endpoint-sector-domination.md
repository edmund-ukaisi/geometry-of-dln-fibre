# Review - A2 Case 2 passive theta Jacobian measurable endpoint-sector domination

Date: 2026-06-30.

## Source and Scope Review

Reviewer: `Poincare`, xhigh effort.  Result: PASS.

The slice is Aoyagi-only and independent of the quiver paper.  It is internal
to the existing Aoyagi local-coordinate and local-measure development: local
endpoint image measurability plus finite-scalar measure domination
bookkeeping.

The reviewer flagged one important boundary, which was applied: do not infer
measurability of the image of an intersection merely from measurability of a
larger local image.  The implementation therefore adds a shrink-stable
Lusin-Souslin lemma and proves measurability on the final returned open set.

## Lean and API Review

Reviewer: `Feynman`, xhigh effort.  Result: PASS.

The recommended theorem shape was used:

```text
exists_pos_open_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_withDensity_jacobian_restrict_endpointSectorSet_le_smul_passiveProductMeasure
```

The reviewer recommended removing the explicit endpoint map measurability
argument, adding the Lusin-Souslin hypotheses and `hpivot₀`, and avoiding an
explicit full-domain `MeasurableSpace (Case2PassiveTheta ...)` binder in the
Jacobian wrapper because it conflicts with the product measurable-space
instance used by `passiveMeasure.prod weightedBox`.  The implementation follows
that advice and adds the needed target `BorelSpace` hypothesis so continuity
discharges measurability of the endpoint map.

## Controller Check

The final proof uses:

```text
exists_open_subset_measurableSet_case2PassiveThetaEndpointSectorSet
exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2PassiveThetaEndpointTopologyTuple_passiveProductMeasure
measure_map_case2PassiveThetaEndpointTopologyTuple_restrict_endpointSectorSet_le_smul
```

It first obtains a Jacobian-unit open `U`, then shrinks to `V ⊆ U` with
measurable endpoint image.  The upper Jacobian domination is restricted from
`U` to `V`, rewritten by `restrict_withDensity` and
`Measure.restrict_restrict_of_subset`, then pushed forward and restricted to
the named endpoint sector.

## Nonclaims

This review accepts only local measurable endpoint-sector domination.  It does
not assert global endpoint-sector measurability, exact passive-sector Haar
transport, determinant-chart Haar transport, raw-order Haar transport,
source-prior comparison, source-image equality, source-rank coverage, normal
crossings, pole order, or RLCT extraction.
