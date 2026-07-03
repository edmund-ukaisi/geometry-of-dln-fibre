# A2 with-following original-volume readback from C-one support

Date: 2026-07-03.

## Claim

The source-cylinder original-volume readback wrapper can be exposed in the
more usable C-one support form.  Instead of requiring

```text
chartPiece subset sourceChart '' (V inter sourceCylinder),
```

we require

```text
chartPiece subset sourceChart '' V,
forall E in chartPiece, cOneReadout E in signedBox.
```

The conclusion is unchanged: under the same a.e. lower bound
`epsilon <= sourceDensity` on `baseJ.restrict V`, the original-volume readback
of `chartPiece` is dominated by the coordinate-source measure restricted to
the ambient neighborhood `G`.

## Pen-and-paper calculation

The local source-chart package gives

```text
readback(sourceChart z) = z,    z in V.
```

The enlarged with-following readback records the C-one readout as the
theta-side `yNext` coordinate.  Projecting the displayed equality to `yNext`
therefore gives

```text
cOneReadout(sourceChart z) = z.1.yNext,    z in V.
```

Take `E in chartPiece`.  The ordinary image support gives a witness

```text
E = sourceChart z,    z in V.
```

The C-one support hypothesis gives

```text
cOneReadout E in signedBox.
```

Substituting `E = sourceChart z` and using the projected readback identity
gives

```text
z.1.yNext in signedBox.
```

Thus `z in sourceCylinder`, so the same witness proves

```text
E in sourceChart '' (V inter sourceCylinder).
```

The source-cylinder original-volume wrapper then applies directly.

## Boundary

This theorem does not prove C-one signed-box support for arbitrary chart
pieces.  It only converts that support into the exact source-cylinder support
needed for active endpoint containment.  It also does not prove
source-density positivity, determinant-chart Haar transport, exact raw-Haar
pushforward, Haar normalization, source coverage, source-rank coverage,
original source-prior transport, normal crossings, pole order, or RLCT
extraction.
