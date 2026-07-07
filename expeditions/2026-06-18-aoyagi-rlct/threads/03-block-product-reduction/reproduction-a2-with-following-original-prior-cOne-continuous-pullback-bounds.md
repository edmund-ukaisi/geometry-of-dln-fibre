# A2 With-Following Original-Prior C-One Continuous Pullback Bounds

Date: 2026-07-07.

## Target

Replace the supplied eventual pullback density bounds in the direct
original-prior C-one handoff by continuity at the basepoint and strict
basepoint inequalities.

The fixed constants are:

```text
eps : ENNReal
density : EdgeFamily -> Real
Kprior : Real
```

The local hypotheses are:

```text
ContinuousAt (fun z => sourceImageDensity (sourceChart z)) z0
eps < sourceImageDensity (sourceChart z0)

ContinuousAt (fun z => density (sourceChart z)) z0
density (sourceChart z0) < Kprior.
```

## Pen-And-Paper Reproduction

The source-density side is a direct neighborhood argument.  Since
`sourceImageDensity ∘ sourceChart` is continuous at `z0` and

```text
eps < sourceImageDensity (sourceChart z0),
```

the open upper ray `(eps, infinity]` is a neighborhood of
`sourceImageDensity (sourceChart z0)`.  Pulling it back by continuity gives an
eventual neighborhood of `z0` on which

```text
eps <= sourceImageDensity (sourceChart z).
```

The prior-density side is the real-valued analogue.  Since
`density ∘ sourceChart` is continuous at `z0` and

```text
density (sourceChart z0) < Kprior,
```

the open lower ray `(-infinity, Kprior)` pulls back to an eventual
neighborhood of `z0` on which

```text
density (sourceChart z) <= Kprior.
```

These are exactly the two eventual hypotheses consumed by the existing
eventual-pullback C-one wrapper.  Applying that wrapper returns the same open
`V` and direct original-prior domination package.

## Boundary

This is only the continuity-to-eventual handoff.  It does not prove
continuity of either pullback, positivity or finiteness of the source-image
density, prior-density nonnegativity, positivity, or boundedness without the
strict basepoint hypothesis, C-one signed-box support for arbitrary chart
pieces, determinant/raw Haar transport, Haar normalization, source/source-rank
coverage, source-prior or original-prior transport, readback domination,
finite-integral transfer, normal crossings, pole order, or RLCT extraction.
