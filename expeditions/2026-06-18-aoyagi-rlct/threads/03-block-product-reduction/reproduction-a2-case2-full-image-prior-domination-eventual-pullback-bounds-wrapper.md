# A2 Case 2: full source-image prior domination from eventual pullback bounds

Status: pen-and-paper reproduction checked; Lean wrapper implemented.

## Question

The input-image-bound wrapper asks for pointwise bounds on

```text
sourceChart '' G.
```

A more local way to feed such bounds is to assume that the pullbacks along the
source chart are eventually bounded near the base passive-theta point `z0`:

```text
forall-frequently-near z0,
  epsilon <= sourceImageDensity (sourceChart z),

forall-frequently-near z0,
  density (sourceChart z) <= Kprior.
```

In Lean this should be stated as two `nhds z0` eventual hypotheses:

```text
forall-eventually z in nhds z0,
  epsilon <= sourceImageDensity (sourceChart z),

forall-eventually z in nhds z0,
  density (sourceChart z) <= Kprior.
```

The output shrink `V` must be chosen after `epsilon`, `density`, and `Kprior`
are fixed.  It should not be claimed uniform in all future density bounds.

## Calculation

Combine the two eventual hypotheses:

```text
forall-eventually z in nhds z0,
  epsilon <= sourceImageDensity (sourceChart z)
  and density (sourceChart z) <= Kprior.
```

The neighborhood characterization gives an open set `G` with

```text
z0 in G,
forall z in G,
  epsilon <= sourceImageDensity (sourceChart z)
  and density (sourceChart z) <= Kprior.
```

For any `E in sourceChart '' G`, choose a witness `z in G` with
`E = sourceChart z`.  The bounds on `G` give:

```text
epsilon <= sourceImageDensity E,
density E <= Kprior.
```

Thus the eventual pullback bounds imply the two input-image bounds required by
the input-image wrapper:

```text
forall E in sourceChart '' G, epsilon <= sourceImageDensity E,
forall E in sourceChart '' G, density E <= Kprior.
```

Applying that wrapper returns a smaller open `V` with `z0 in V`, the
source-chart readback/injectivity/continuity/measurable-image/p.13-support
facts, and the same prior domination conclusion on `sourceChart '' V`.

The determinant-side reverse domination remains a hypothesis on this returned
`V`:

```text
rawHaar.restrict rawDetChart
  <= Cdet * Measure.map Y (passiveSource.restrict V).
```

The scalar is unchanged:

```text
Cprior =
  ENNReal.ofReal Kprior *
    (((cHaar^{-1} : NNReal) : ENNReal) * (Cdet * epsilon^{-1})).
```

## Boundary

This is still only a sufficient-condition wrapper.  It does not prove the
eventual pullback bounds, nor continuity, positivity, or concrete
identification of `sourceImageDensity` or the prior density.  It does not
prove a source-image coverage theorem, determinant-chart Haar transport,
exact raw-Haar pushforward, raw-Haar normalization, normal crossings, pole
order, or RLCT extraction.

The shrink `V` is allowed to depend on `epsilon`, `density`, and `Kprior`.
Uniformity in all future density bounds is not claimed.
