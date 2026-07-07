# A2 With-Following Original-Prior C-One Eventual Pullback Bounds

Date: 2026-07-07.

## Target

Turn supplied eventual pullback bounds near the theta basepoint into the a.e.
source-density and prior-density hypotheses required by the direct
original-prior C-one source-support handoff.

The fixed data are:

```text
eps : ENNReal
density : EdgeFamily -> Real
Kprior : Real
```

and the supplied local hypotheses are:

```text
forall eventually z near z0,
  eps <= sourceImageDensity (sourceChart z)

forall eventually z near z0,
  density (sourceChart z) <= Kprior.
```

The intended conclusion is the same direct non-readback original-prior
domination package as the C-one handoff, but the caller no longer supplies the
a.e. bounds separately.

## Pen-And-Paper Reproduction

Let `G` be the requested open neighborhood of `z0`.  Intersect it with the
common eventual event for the two pullback bounds.  Since the event is
eventual in `nhds z0`, there is an open set `Gbounds` containing `z0` on which
both inequalities hold pointwise.  Set

```text
Gshrink = G inter Gbounds.
```

Apply the direct original-prior C-one source-support theorem inside
`Gshrink`.  It returns an open set `V` with `z0 in V` and
`V subset Gshrink`, hence:

```text
V subset G
V subset Gbounds.
```

Now let `E in sourceChart '' V`.  Choose `z in V` with
`E = sourceChart z`.  Since `z in Gbounds`, the source-density part of the
event gives

```text
eps <= sourceImageDensity E.
```

Therefore the existing image-to-restrict helper gives

```text
forall almost every z with respect to baseJ.restrict V,
  eps <= sourceDensity z,
```

where `sourceDensity z = sourceImageDensity (sourceChart z)`.

Similarly, for a measurable chart piece with

```text
chartPiece subset sourceChart '' V,
```

each `E in chartPiece` has a witness `z in V` with `E = sourceChart z`.
The prior-density part of the event gives

```text
density E <= Kprior.
```

The existing restrict helper converts this pointwise chart-piece bound into

```text
forall almost every E with respect to originalVolume.restrict chartPiece,
  density E <= Kprior.
```

These are exactly the two a.e. hypotheses consumed by the direct
original-prior C-one source-support handoff.  All scalar bookkeeping is
unchanged:

```text
Ddet = Cdet * eps^-1
Dvol = ((cHaar^-1 : NNReal) : ENNReal) * Ddet
Cprior = ofReal Kprior * Dvol.
```

## Boundary

This wrapper proves only the neighborhood-shrinking and a.e.-bound handoff
from supplied eventual pullback bounds.  It does not prove C-one signed-box
support, source-density positivity, prior-density boundedness from
continuity, source/source-rank coverage, determinant or raw Haar transport,
Haar scalar normalization, source-prior/original-prior equality, readback
domination, finite-integral transfer, normal crossings, pole order, or RLCT
extraction.
