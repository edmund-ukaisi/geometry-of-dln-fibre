# Statement card - A2 with-following original-volume source-image inverse-Haar density

Date: 2026-07-02.

## Lean targets

P13 chart-piece exact-density bridge:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_sourceReference_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
```

Same-shrink source-image exact-density bridge:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_sourceImageReference_same_shrink_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
```

## Input

On the returned local with-following shrink `V`:

```text
map rawMap (thetaReference | V) = rawHaar | rawSourceSet.
```

The source-image theorem also takes a measurable `chartPiece` with:

```text
chartPiece subset sourceChart '' V.
```

## Output

With

```text
c =
  (map rawOrderMatrixTupleEquiv rawHaar).addHaarScalarFactor
    (originalTupleVolume d),
sourceRef = map sourceChart (thetaReference | V),
invHaarDensity = fun _ => c^-1,
```

the theorem proves:

```text
originalVolume | chartPiece
  = (sourceRef.withDensity invHaarDensity) | chartPiece
```

and the bounded-density side condition:

```text
forall-ae E with respect to sourceRef | chartPiece,
  invHaarDensity E <= c^-1.
```

The same-shrink source-image theorem also returns local readback,
source-chart injectivity, source-chart continuity, measurability of
`sourceChart '' V`, and the p.13 support of that image.

## Dependencies

- with-following raw-order/source-chart two-stage handoff;
- with-following p.13 source-image support theorem;
- p.13 raw-order Haar-to-original-volume scalar equality;
- positive additive-Haar scalar helper;
- `measure_eq_inv_smul_of_eq_nnreal_smul`;
- constant-density simplification via `withDensity_const`.

## Verification

Focused local build and full local build passed:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeBridge
env LEAN_NUM_THREADS=3 lake build DLNFibre
```

`scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
`git diff --check` passed, and the touched Lean-file forbidden-marker scan was
clean.  Direct axiom probes for both declarations reported:

```text
[propext, Classical.choice, Quot.sound]
```

Xhigh review `review-a2-with-following-original-volume-source-image-invhaar-density.md`
found no issues.

## Nonclaims

No determinant-Haar transport, no proof of the raw pushforward identity, no
original source-prior transport, no global source-image coverage, no
source-rank coverage, no scalar normalization, no normal crossings, no pole
order, and no RLCT extraction.
