# A2 Case 2: source-image lower bound for the canonical determinant wrapper

Status: pen-and-paper reproduction checked; Lean target selected.

## Question

The determinant-domination finite-integral wrapper currently asks, on the
returned passive-theta shrink `V`, for the measure-theoretic lower bound

```text
forall-ae z with respect to baseJ.restrict V, epsilon <= sourceDensity z.
```

Here

```text
sourceDensity z := sourceImageDensity (sourceChart z).
```

One stronger chart-side sufficient hypothesis is the pointwise image bound

```text
forall E in sourceChart '' V, epsilon <= sourceImageDensity E.
```

The goal is to expose a finite-integral wrapper using this chart-side bound.

## Calculation

For any measurable set `V`, the restricted measure `baseJ.restrict V` is
supported on `V`:

```text
forall-ae z with respect to baseJ.restrict V, z in V.
```

Therefore, if `z in V`, then `sourceChart z in sourceChart '' V`.  The
pointwise image bound gives

```text
epsilon <= sourceImageDensity (sourceChart z) = sourceDensity z.
```

Thus the image bound implies exactly the a.e. source-density lower bound
required by the already-proved canonical determinant wrapper.  The finite
integral conclusion then follows without changing the determinant-side reverse
domination or the prior-density hypothesis.

## Boundary

This does not prove that such an image lower bound holds.  It only adds a
stronger sufficient chart-image socket on the returned `sourceChart '' V`.
The converse implication is not claimed: an a.e. lower bound on
`baseJ.restrict V` may fail at null points whose images still lie in
`sourceChart '' V`.

It does not prove determinant-chart Haar transport, exact raw-Haar
pushforward, raw-Haar normalization, source-image coverage, source-rank
coverage, original source-prior transport, normal crossings, pole order, or
RLCT extraction.
