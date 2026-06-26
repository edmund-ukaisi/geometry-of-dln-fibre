# Reproduction - A2 p.13 left-step local raw-det support

Date: 2026-06-26.

Status: controller pen-and-paper reproduction before Lean.  This is local
determinant-chart support for the actual p.13 left-step section.

## Source Boundary

Aoyagi p.13 writes the post-product-reduction block tuple with regular
coordinates in the upper-left block and a residual product in the lower-right
block.  In the Lean p.13 left-step tuple the raw source coordinates are the
section

```text
C1 = I,
D  = Dtail,
F3 = F3,
A1 = Ctop(u),
A2 = -Ctop(u) F2,
A3 = 0,
A4 = C0.
```

The raw determinant chart for the product-step map asks for `det C1` and
`det A1` to be units.  This reproduction proves only local membership in that
chart for the actual section.  It does not identify the image measure with
full raw Haar measure on the raw determinant chart.

## Pen-And-Paper Check

For every source coordinate `x` and regular coordinate `u`, the previously
proved p.13 left-step identity gives

```text
leftStepRaw(x,u) = rawPreimage(x,u).
```

The raw preimage tuple has first block `C1 = I`, so

```text
det C1 = 1
```

is a unit over `R`.

Its passive determinant-chart block is

```text
A1 = Ctop(u).
```

At the centered regular coordinate `u = 0`, the p.13 coordinate convention
gives

```text
Ctop(0) = I,
```

hence `det Ctop(0) = 1`.  The determinant of `Ctop(u)` is continuous in the
finite Euclidean coordinate `u`, and the unit locus in `R` is open around
`1`.  Therefore, for every prescribed `Rmax > 0`, there is a radius
`0 < R <= Rmax` such that

```text
u in ball(0,R)  =>  det Ctop(u) is a unit.
```

Combining these two facts gives

```text
u in ball(0,R)  =>
  leftStepRaw(x,u) in rawDetChart
```

for all base/source coordinates `x`.

Consequently, if a measure on `(x,u)` is supported a.e. on this regular
coordinate ball, then the left-step raw tuple lands in the raw determinant
chart a.e.

## Lean Target

Add in `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepRegularDensity.lean`:

```text
p13ProductCoordinateLeftStepRawTopologyTuple_mem_rawDetChartSet
exists_pos_radius_le_forall_p13ProductCoordinateLeftStepRawTopologyTuple_mem_rawDetChartSet
ae_p13ProductCoordinateLeftStepRawTopologyTuple_mem_rawDetChartSet_of_ae_regular_mem_ball
exists_pos_radius_le_ae_p13LeftStepRaw_mem_rawDetChartSet_of_ae_regular_mem_ball
```

## Boundary

- Proves local raw determinant-chart support for the actual p.13 section.
- Uses only `C1 = I`, `A1 = Ctop(u)`, and smallness of `u`.
- No raw-Haar/full-chart pushforward.
- No original source chart, source/image equality, or source-measure transport.
- No signed-box density identification, regular-suspension certificate,
  normal crossings, pole order, or RLCT.
