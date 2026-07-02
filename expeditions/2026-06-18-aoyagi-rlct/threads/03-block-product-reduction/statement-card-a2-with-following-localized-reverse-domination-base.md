# Statement card - A2 with-following localized reverse domination base

Date: 2026-07-02.

## Lean target

```text
exists_open_subset_rawHaar_restrict_patch_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_baseJ_restrict_of_endpointPatch_restrict_le_smul_endpointTopologyTuple
```

## Inputs

On the same local Case 2 with-following shrink `V` supplied by the endpoint
topology-tuple chart theorem, define:

```text
Y = with-following endpoint topology tuple
Phi = topologyTupleEdgeRawOrder
rawMap z = Phi (Y z)
baseJ = sourceMeasure.withDensity
  (fun z => ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z))).
```

For an additive Haar measure `rawHaar`, a raw-order patch `P`, and scalar `c`,
the theorem assumes:

```text
P subset rawSourceSet
NullMeasurableSet (rawDetChart ∩ rawOrderOnEndpoint preimage P) rawHaar
rawHaar.restrict (rawDetChart ∩ rawOrderOnEndpoint preimage P)
  <= c • Measure.map Y (sourceMeasure.restrict V).
```

## Output

The theorem returns the same open shrink `V` with `z0 in V`, `V subset G`, and
a.e. measurability of `rawMap` for `baseJ.restrict V`.  It also proves the
localized reverse domination:

```text
rawHaar.restrict P
  <= c • Measure.map rawMap (baseJ.restrict V).
```

## Proof dependencies

- the with-following endpoint topology-tuple local chart theorem;
- patch-parametric retained-passive raw-order COV;
- generic weighted reverse-domination handoff through a composed map;
- continuity of the endpoint tuple map and raw-order map on the determinant
  chart.

## Verification

Focused and full local Lean builds passed:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaRawImageHandoff
env LEAN_NUM_THREADS=3 lake build DLNFibre
```

`scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
Touched Lean-file forbidden-marker scan and `git diff --check` passed.  The
direct axiom probe for the new theorem reported:

```text
[propext, Classical.choice, Quot.sound]
```

Independent xhigh review is recorded in
`review-a2-with-following-localized-reverse-domination-base.md`.

## Nonclaims

The endpoint-patch domination is an explicit input.  This does not prove
endpoint-Haar transport, concrete source-density lower bounds,
coordinate-source domination, raw-Haar normalization, source-image coverage,
source-rank coverage, original source-prior transport, normal crossings, pole
order, or RLCT extraction.
