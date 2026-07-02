# A2 with-following original-volume source-image inverse-Haar density

Date: 2026-07-02.

## Source calculation

This is the exact-density analogue of the existing with-following
original-volume domination bridge.  It is still conditional on the same raw
pushforward identity:

```text
map rawMap (thetaReference | V) = rawHaar | rawSourceSet.
```

The local with-following endpoint package gives, after shrinking inside the
caller neighborhood,

```text
rawChart (rawMap z) = sourceChart z
```

on `V`.  Therefore the two-stage source chart image of the raw pushforward is
the direct source reference:

```text
map rawChart (map rawMap (thetaReference | V))
  = map sourceChart (thetaReference | V).
```

Using the raw pushforward identity, this becomes:

```text
map rawChart (rawHaar | rawSourceSet)
  = sourceRef.
```

The p.13 retained-passive source-measure bridge gives the Haar scalar
normalization:

```text
map rawChart (rawHaar | rawSourceSet)
  = c * (originalVolume | p13SourceSet),
```

where

```text
c =
  (map rawOrderMatrixTupleEquiv rawHaar).addHaarScalarFactor
    (originalTupleVolume d).
```

The scalar `c` is positive because both sides are additive Haar measures after
transport to the tuple coordinates.  Hence `c != 0`.

## Chart-piece restriction

If `chartPiece` is measurable and lies in the p.13 source set, then restriction
of the preceding identity gives:

```text
sourceRef | chartPiece = c * (originalVolume | chartPiece).
```

Inverting the nonzero `NNReal` scalar gives:

```text
originalVolume | chartPiece = c^-1 * (sourceRef | chartPiece).
```

Since the density is constant, this is the same as:

```text
originalVolume | chartPiece
  = (sourceRef.withDensity (fun _ => c^-1)) | chartPiece.
```

The required a.e. bounded-density side condition is tautological:

```text
forall-ae E with respect to sourceRef | chartPiece,
  c^-1 <= c^-1.
```

## Source-image wrapper

The source-image theorem additionally shrinks so that:

```text
readback (sourceChart z) = z,
sourceChart is injective and continuous on V,
sourceChart '' V is measurable,
sourceChart '' V subset p13SourceSet.
```

For any measurable `chartPiece subset sourceChart '' V`, the p.13 containment
needed by the p.13 exact-density theorem follows immediately.  Thus the same
constant inverse-Haar density identity holds on actual local source-image
pieces.

## Boundary

The raw pushforward identity remains an explicit hypothesis.  This does not
prove determinant-Haar transport, raw-Haar transport, original source-prior
transport, global source-image coverage, source-rank coverage, normal
crossings, pole order, or RLCT extraction.  It only identifies the local
source-image density with the constant inverse Haar scalar in the branch where
the caller has supplied exact raw-source pushforward.
