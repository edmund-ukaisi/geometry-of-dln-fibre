# A2 density pullback continuity to eventual bounds

Status: pen-and-paper reproduction checked; Lean helpers implemented.

## Question

The full source-image prior wrapper now accepts two eventual pullback bounds:

```text
forall-eventually z in nhds z0,
  epsilon <= sourceImageDensity (sourceChart z),

forall-eventually z in nhds z0,
  density (sourceChart z) <= Kprior.
```

Can these be produced from local continuity of the two pullbacks and strict
basepoint inequalities?

## Calculation

Let

```text
f(z) = sourceImageDensity (sourceChart z)
g(z) = density (sourceChart z).
```

For the lower source-image bound, assume:

```text
ContinuousAt f z0,
epsilon < f(z0).
```

The open interval `Ioi epsilon` is a neighborhood of `f(z0)`.  By continuity,
eventually near `z0` we have `f(z) in Ioi epsilon`, hence

```text
epsilon <= f(z).
```

For the upper prior-density bound, assume:

```text
ContinuousAt g z0,
g(z0) < Kprior.
```

The open interval `Iio Kprior` is a neighborhood of `g(z0)`.  By continuity,
eventually near `z0` we have `g(z) in Iio Kprior`, hence

```text
g(z) <= Kprior.
```

Combining the two results gives exactly the two eventual hypotheses consumed
by the eventual-pullback full prior-domination wrapper.

## Boundary

This is only a topological handoff.  It does not construct or identify
`sourceImageDensity`; it does not prove the prior density is the intended
smooth prior; it does not prove either continuity assumption or either strict
basepoint inequality.  It does not prove determinant-chart Haar transport,
exact raw-Haar pushforward, raw-Haar normalization, source-image coverage,
source-rank coverage, normal crossings, pole order, or RLCT extraction.
