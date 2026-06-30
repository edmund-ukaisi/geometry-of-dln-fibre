# Reproduction - A2 passive theta source-image Jacobian bridge

Date: 2026-06-30.

## Question

Suppose a measure on the local source side is already given as a bounded
density over the chart-produced source-image base

```text
sourceImageBase = Measure.map sourceChart (baseJ.restrict W),
```

where `baseJ` is the globally Jacobian-weighted passive-theta reference
measure.  Can the existing theta-domain residual-source theorem be consumed
without pretending this source-image measure is an original DLN prior?

Answer: yes.  The bridge is measure-theoretic: turn the source-image density
`g : EdgeFamily -> ENNReal` into the theta-domain density `g ∘ sourceChart`,
apply the existing theta-domain bounded-density theorem, and identify the
resulting pushforward with `sourceImageBase.withDensity g`.

## Calculation

Let

```text
baseJ = passiveSource.withDensity jacobianDensity
sourceImageBase = Measure.map sourceChart (baseJ.restrict W)
sourceImageMeasure = sourceImageBase.withDensity g.
```

The existing theta-domain theorem applies to

```text
sourceDensity(theta) = g (sourceChart theta).
```

It needs the a.e. bound

```text
g (sourceChart theta) <= C
```

with respect to `baseJ.restrict W`.  If `sourceChart` is a.e.-measurable for
`baseJ.restrict W`, then a source-image a.e. bound

```text
g(E) <= C  for sourceImageBase-a.e. E
```

pulls back to the theta-domain bound by `ae_of_ae_map`.

It remains to identify the pushed theta-domain measure.  Since `W` is open and
hence measurable,

```text
(baseJ.withDensity (g ∘ sourceChart)).restrict W
  =
(baseJ.restrict W).withDensity (g ∘ sourceChart).
```

If `sourceChart` is a.e.-measurable for `baseJ.restrict W` and `g` is
a.e.-measurable for `sourceImageBase`, then the standard map-with-density
identity gives

```text
Measure.map sourceChart
  ((baseJ.restrict W).withDensity (g ∘ sourceChart))
  =
(Measure.map sourceChart (baseJ.restrict W)).withDensity g.
```

Thus the measure `mu` produced by the theta-domain residual-source theorem is
exactly `sourceImageMeasure`.  The local-source support equality, residual
square-sum positivity a.e., and finite residual negative-power integrability
therefore transfer by rewriting.

## Source Boundary

This is not a new Aoyagi source-prior theorem.  Aoyagi's p.13 coordinate
calculation motivates the local passive-theta chart, and the p.6 template says
that a true coordinate-change theorem should produce a prior-times-Jacobian
density.  This bridge only consumes a density once it has already been supplied
on the chart-produced source-image base.

The full original-prior transport still needs the p.13 regular variables and
a real coordinate/source-measure theorem.  The passive-theta source image by
itself is not the full original DLN prior chart.

## Nonclaims

No original/source prior density identity, no domination for arbitrary
external measures, no Haar transport, no determinant-chart or raw-order Haar
identification, no source-rank coverage, no normal crossings, no pole order,
and no RLCT extraction.
