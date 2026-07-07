# A2 With-Following Original-Prior C-One Source-Support Handoff

Date: 2026-07-07.

## Target

Turn ordinary local chart-piece support plus C-one signed-box support into the
source-cylinder support required by the direct original-prior source-cylinder
domination theorem.

The intended theorem keeps the direct non-readback conclusion:

```text
originalPrior.restrict chartPiece
  <= Cprior * Measure.map sourceChart (coordinateSourceMeasure.restrict V).
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

First choose an outer local shrink `W` with the source-chart readback
left-inverse:

```text
readback (sourceChart z) = z        for z in W.
```

Then run the direct original-prior source-cylinder theorem inside `W`.  It
returns an inner shrink `V subset W`.

Now let `E in chartPiece`.  The ordinary support hypothesis gives a point
`z in V` with

```text
E = sourceChart z.
```

The C-one support hypothesis gives

```text
cOneReadout E in signedBox.
```

Since `V subset W`, the left-inverse identity applies to `z`.  The existing
C-one support bridge says that this identity identifies the C-one readout of
`sourceChart z` with the theta-side `yNext` coordinate.  Therefore

```text
z.1.yNext in signedBox,
```

so `z in sourceCylinder`.  Hence

```text
E in sourceChart '' (V inter sourceCylinder).
```

This converts the public C-one support hypotheses into the source-cylinder
support consumed by the direct prior domination theorem.  All scalar and
density bookkeeping is unchanged:

```text
Ddet = Cdet * eps^-1
Dvol = ((cHaar^-1 : NNReal) : ENNReal) * Ddet
Cprior = ofReal Kprior * Dvol.
```

## Boundary

This is only a support-conversion wrapper over the already proved direct
original-prior source-cylinder handoff.  It does not prove the C-one signed-box
condition for arbitrary chart pieces, source-density positivity,
prior-density boundedness, source-prior identification, original-prior
transport, readback domination, finite-integral transfer, determinant-chart
Haar transport, exact raw-Haar pushforward, Haar-scalar normalization, source
coverage, source-rank coverage, normal crossings, pole order, or RLCT
extraction.
