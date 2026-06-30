# Statement card - A2 Case 2 passive theta Jacobian measurable endpoint-sector domination

Date: 2026-06-30.

## Statement

Under the same local endpoint image-measurability hypotheses used in the
previous Lusin-Souslin slice, there is a positive `K` and an open neighborhood
`V` of the determinant-sector, nonzero-pivot base theta point such that

```text
MeasurableSet (case2PassiveThetaEndpointSectorSet ... V)
```

and, for

```text
passiveSource = passiveMeasure.prod weightedBox
Y z = case2PassiveThetaEndpointTopologyTuple ... z eNext e
jacobianDensity z =
  ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z)),
S_V = case2PassiveThetaEndpointSectorSet ... V,
```

one has

```text
(Measure.map Y ((passiveSource.withDensity jacobianDensity).restrict V)).restrict S_V
  <= ofReal K •
     (Measure.map Y (passiveSource.restrict V)).restrict S_V.
```

## Lean Targets

```text
exists_open_subset_measurableSet_case2PassiveThetaEndpointSectorSet

exists_pos_open_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_withDensity_jacobian_restrict_endpointSectorSet_le_smul_passiveProductMeasure
```

## Proof Idea

First prove the relative endpoint image-measurability statement: if `G` is any
open neighborhood of the base point, intersect `G` with the local
endpoint-injectivity neighborhood and apply Lusin-Souslin to the continuous
injective endpoint map on the intersection.

Then obtain the Jacobian upper sandwich on an open `U`; apply the relative
measurability theorem with `G = U` to get `V ⊆ U`.  Restrict the upper
Jacobian domination from `U` to `V`, rewrite the global `withDensity`
restriction, and apply the existing endpoint-sector domination transfer.

## Nonclaims

No global endpoint-sector measurability, exact passive-sector Haar pushforward,
determinant-chart Haar transport, raw-order Haar transport, source-prior
comparison, source-image equality, source-rank coverage, normal crossings,
pole order, or RLCT extraction is claimed.

## Reproduction

```text
threads/03-block-product-reduction/reproduction-a2-case2-passive-theta-jacobian-measurable-endpoint-sector-domination.md
```

## Verification

Passed before commit:

```text
lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure
lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaJacobianMeasure
lake env lean -E warning DLNFibre.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
```

Touched-file scans found no `sorry`, `admit`, `axiom`, `#exit`,
`native_decide`, `#check`, `#eval`, `set_option trace`, or `dbg_trace`.
The two new public declarations have axiom footprint:

```text
[propext, Classical.choice, Quot.sound]
```
