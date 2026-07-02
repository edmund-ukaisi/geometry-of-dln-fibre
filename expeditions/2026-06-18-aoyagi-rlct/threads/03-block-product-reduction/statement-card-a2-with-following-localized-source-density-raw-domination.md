# Statement card - A2 with-following localized source-density raw domination

Date: 2026-07-02.

## Lean targets

```text
exists_open_subset_rawHaar_restrict_patch_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_endpointPatch_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
exists_open_subset_rawHaar_restrict_patch_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_endpointPatch_restrict_le_smul_endpointTopologyTuple_eventually_sourceDensity_lower
```

## Inputs

On a local Case 2 with-following shrink `V`, let

```text
Y = with-following endpoint topology tuple
rawMap = topologyTupleEdgeRawOrder o Y
baseJ = referenceSource.withDensity jacobianDensity
coordinateSourceMeasure = baseJ.withDensity sourceDensity
```

For a raw-order patch `P`, additive Haar measure `rawHaar`, and scalar `Cdet`,
the localized source-density theorem assumes:

```text
P subset rawSourceSet
NullMeasurableSet (rawDetChart ∩ rawOrderOnEndpoint preimage P) rawHaar
rawHaar.restrict (rawDetChart ∩ rawOrderOnEndpoint preimage P)
  <= Cdet • Measure.map Y (referenceSource.restrict V)
Cdet < infinity
epsilon <= sourceDensity z for baseJ.restrict V-a.e. z
epsilon != 0
epsilon != infinity
```

The eventual wrapper replaces the a.e. lower bound by

```text
forall eventually z near z0, epsilon <= sourceDensity z.
```

## Output

Both localized wrappers conclude finite-scalar domination on the same patch:

```text
(Cdet * epsilon^{-1}) < infinity
rawHaar.restrict P
  <= (Cdet * epsilon^{-1}) •
     Measure.map rawMap (coordinateSourceMeasure.restrict V).
```

## Proof Dependencies

- localized with-following reverse domination base;
- lower-density measure handoff
  `measure_le_smul_map_restrict_withDensity_of_le_smul_map_restrict_of_ae_le`;
- the same open-neighborhood extraction used by the global eventual wrapper.

## Verification

Focused and full local Lean builds passed:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaRawImageHandoff
env LEAN_NUM_THREADS=3 lake build DLNFibre
```

`scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
Touched Lean-file forbidden-marker scan and `git diff --check` passed.
Direct axiom probes for both declarations reported:

```text
[propext, Classical.choice, Quot.sound]
```

Independent xhigh review is recorded in
`review-a2-with-following-localized-source-density-raw-domination.md`.

## Nonclaims

The endpoint-patch domination and source-density lower bound remain explicit.
This does not prove endpoint-Haar transport, exact raw-Haar pushforward,
raw-Haar normalization, source-image coverage, source-rank coverage, original
source-prior transport, normal crossings, pole order, or RLCT extraction.
