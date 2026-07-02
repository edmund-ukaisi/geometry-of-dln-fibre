# Statement card - A2 with-following inverse-Haar original-volume readback density socket

Date: 2026-07-02.

## Lean target

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_and_readback_le_smul_sourceReference_same_shrink_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
```

## Input

On the returned local with-following shrink `V`:

```text
map rawMap (thetaReference | V) = rawHaar | rawSourceSet.
```

The chart piece is measurable and lies in the actual local source image:

```text
chartPiece subset sourceChart '' V.
```

## Output

With:

```text
c =
  (map rawOrderMatrixTupleEquiv rawHaar).addHaarScalarFactor
    (originalTupleVolume d),
sourceRef = map sourceChart (thetaReference | V),
invHaarDensity = fun _ => c^-1,
```

the theorem packages both:

```text
originalVolume | chartPiece =
  (sourceRef.withDensity invHaarDensity) | chartPiece,
forall-ae E with respect to sourceRef | chartPiece,
  invHaarDensity E <= c^-1,
```

and the readback consequence:

```text
AEMeasurable readback (originalVolume | chartPiece),
map readback (originalVolume | chartPiece)
  <= c^-1 * (thetaReference | G).
```

It also returns the same local source-chart structure as the source-image
bridge: left inverse, injectivity, continuity, measurable image, and p.13
support of the image.

## Dependencies

- with-following source-image inverse-Haar exact-density bridge;
- generic original-volume readback socket from a source-image `withDensity`
  identity;
- local source-chart left inverse, injectivity, continuity, and image
  measurability.

## Verification

Focused local module build and full local build passed:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeReadback
env LEAN_NUM_THREADS=3 lake build DLNFibre
```

`lean/scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
`git diff --check` passed, and the touched Lean-file forbidden-marker scan was
clean.  Direct axiom probe reported:

```text
[propext, Classical.choice, Quot.sound]
```

Xhigh review `review-a2-with-following-original-volume-invhaar-readback-density-socket.md`
found no issues.

## Nonclaims

No proof of the raw pushforward identity, no determinant-Haar transport, no
raw-Haar transport, no source-prior/original-prior transport, no source-image
coverage beyond the local chart, no source-rank coverage, no normal crossings,
no pole order, and no RLCT extraction.
