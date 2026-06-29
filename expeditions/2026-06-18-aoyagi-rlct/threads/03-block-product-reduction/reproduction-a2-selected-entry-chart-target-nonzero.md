# A2 selected-entry chart-target nonzero measure

## Scope

This note records the elementary finite-coordinate positivity calculation for
one selected-entry signed-box chart target.  It is a local chart-image
measure brick.  It is not an analytic atlas construction, not a source-prior
transport theorem, and not an RLCT extraction.

The Aoyagi source formula is the selected-entry blow-up substitution in the
product-reduction proof (PDF pp. 15-22, especially the Case 2 block on
pp. 19-22):

```text
x_p = u,
x_i = u r_i  for i != p.
```

Here `p` is the selected pivot in a finite center set `E`.

## Target inner box

Let `R_i > 0` for every `i in E`.  Define a concrete target box `U` by

```text
R_p / 2 < x_p < R_p,
|x_i| < R_p R_i / 4  for i != p.
```

Equivalently,

```text
U = product_i U_i,
U_p = (R_p/2, R_p),
U_i = (-(R_p R_i/4), R_p R_i/4)  for i != p.
```

Each interval is nonempty and open because the radii are positive, so `U` is a
nonempty open subset of the finite product coordinate space.  Therefore finite
product Lebesgue measure gives

```text
volume(U) != 0.
```

This uses the existing open-positive-measure instance for finite products.

## Inclusion in the selected-entry chart image

For `x in U`, the pivot coordinate satisfies

```text
x_p > R_p/2 > 0,
|x_p| = x_p < R_p.
```

For each `i != p`,

```text
|x_i / x_p| = |x_i| / x_p
  < (R_p R_i / 4) / (R_p / 2)
  = R_i / 2
  < R_i.
```

The already-proved horn membership criterion for the selected-entry chart
image says that, under positive radii,

```text
x in chartMap(p)(signedBox(R))
```

whenever either `x = 0` or the pivot is nonzero, `|x_p| < R_p`, and all
quotient coordinates satisfy `|x_i/x_p| < R_i`.  Thus

```text
U subset chartMap(p)(signedBox(R)).
```

Since `volume(U) != 0`, monotonicity gives

```text
volume(chartMap(p)(signedBox(R))) != 0.
```

Equivalently,

```text
volume.restrict(chartMap(p)(signedBox(R))) != 0.
```

## Punctured source image

The existing signed-box measure theorem already removes the pivot hyperplane
`u = 0` up to a null set and then restores the full image by a null-image
argument.  Therefore the full chart image and the image of

```text
signedBox(R) intersect {y | y_p != 0}
```

are equal almost everywhere for Lebesgue measure.  The nonzero target measure
therefore also holds for the punctured-source image and its restricted
Lebesgue measure.

## Weighted source nonzero

The existing Jacobian pushforward theorem is

```text
map chartMap ((prod_i volume|(-R_i,R_i)).withDensity sourceDensity)
  = volume.restrict(chartMap(p)(signedBox(R))).
```

If the weighted source measure were zero, its pushforward would be zero,
contradicting the nonzero restricted target measure.  Hence the weighted
signed-box source measure is nonzero.

The same argument with the punctured-source pushforward proves nonzero for

```text
(volume.restrict(signedBox(R) intersect {y | y_p != 0}))
  .withDensity sourceDensity.
```

## Chart-point bridge

The chart-point adapter is the finite coordinate presentation

```text
theta(y) = (y_p, y|_{E \ {p}}).
```

The previous chart-point bridge proves

```text
formalChartMap(theta(y)) = chartMap(y)
```

and the two-stage pushforward equality through `theta`.  Since the weighted
source measure is nonzero, `Measure.map theta` of it is nonzero by the general
`Measure.map_ne_zero_iff` lemma.  Since the two-stage chart-point pushforward
equals the nonzero restricted target measure, it is also nonzero.

## Kill conditions

- Kill if this is described as an analytic atlas construction.
- Kill if this is described as a natural product-measure theorem on
  chart-point coordinates.
- Kill if this is used as original/source-prior transport, determinant-chart
  Haar transport, source coverage, source-rank coverage, transition
  regularity, source production, normal-crossing extraction, pole order, or
  RLCT.
- Kill if the pivot hyperplane is treated as injective chart locus rather than
  as a null set handled by the existing punctured-source theorem.

