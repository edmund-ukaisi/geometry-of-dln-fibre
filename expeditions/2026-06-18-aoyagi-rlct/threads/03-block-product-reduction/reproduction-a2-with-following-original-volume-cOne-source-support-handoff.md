# A2 With-Following Original-Volume C-One Source-Support Handoff

Date: 2026-07-07.

## Target

Turn ordinary local chart-piece support plus C-one signed-box support into the
source-cylinder support required by the direct original-volume source-cylinder
domination theorem.

The intended theorem keeps the direct non-readback conclusion:

```text
originalVolume.restrict chartPiece
  <= Dvol * Measure.map sourceChart (coordinateSourceMeasure.restrict V).
```

It replaces the public support hypothesis

```text
chartPiece subset sourceChart '' (V inter sourceCylinder)
```

by the two hypotheses

```text
chartPiece subset sourceChart '' V
forall E in chartPiece, cOneReadout E in signedBox.
```

## Pen-And-Paper Reproduction

Choose an outer local shrink `W` where the source-chart readback is a left
inverse:

```text
readback (sourceChart z) = z        for z in W.
```

Then run the direct original-volume source-cylinder theorem with ambient
neighborhood `W`.  It returns an inner shrink `V subset W`.

For `E in chartPiece`, ordinary support gives a point `z in V` with

```text
E = sourceChart z.
```

The C-one support hypothesis gives

```text
cOneReadout E in signedBox.
```

Because `V subset W`, the left-inverse identity applies at `z`.  The existing
C-one support bridge identifies the C-one readout of `sourceChart z` with the
theta-side `yNext` coordinate, so

```text
z.1.yNext in signedBox.
```

Thus `z in sourceCylinder`, and

```text
E in sourceChart '' (V inter sourceCylinder).
```

The direct source-cylinder original-volume theorem now applies unchanged.  Its
scalar is

```text
Ddet = Cdet * eps^-1
Dvol = ((cHaar^-1 : NNReal) : ENNReal) * Ddet.
```

## Boundary

This is only a support-conversion wrapper over the already proved direct
original-volume source-cylinder handoff.  It does not prove the C-one
signed-box condition for arbitrary chart pieces, source-density positivity,
determinant-chart Haar transport, exact raw-Haar pushforward, Haar-scalar
normalization, source coverage, source-rank coverage, original-prior
transport, readback domination, finite-integral transfer, normal crossings,
pole order, or RLCT extraction.
