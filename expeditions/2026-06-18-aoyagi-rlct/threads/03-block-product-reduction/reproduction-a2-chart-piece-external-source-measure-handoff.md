# Reproduction - A2 chart-piece external-source measure handoff

Date: 2026-06-30.

## Claim

Let `sourceImageMeasure` be the chart-produced source-image measure already
used by the Case 2 passive-theta Jacobian bridge.  The existing finite-integral
socket gives integrability for every product measure dominated by a finite
scalar multiple of

```text
(sourceImageMeasure.restrict sourceLocal).prod nu
```

where `sourceLocal = U inter sourceStratum`.

If `chartPiece` is any measurable subset of `sourceLocal`, and an external
source measure satisfies on `chartPiece`

```text
externalSourceMeasure.restrict chartPiece
  =
(sourceImageMeasure.withDensity externalDensity).restrict chartPiece
```

with

```text
externalDensity <= Cext
  a.e. with respect to sourceImageMeasure.restrict chartPiece,
```

then the product measure `(externalSourceMeasure.restrict chartPiece).prod nu`
also satisfies the same finite-integral conclusion.

## Pen-And-Paper Check

This step is measure bookkeeping, not new Aoyagi algebra.  The Aoyagi p. 13
block-product calculation supplies the local coordinates and the existing
loss-power finite-integral theorem supplies the integrability over
`sourceLocal`.  We only shrink the source side to a measurable piece.

Write `mu = sourceImageMeasure`, `s = chartPiece`, and `T = sourceLocal`.
Assume `s subset T` and `s` is measurable.  The local density bound gives

```text
(mu.withDensity externalDensity).restrict s
  <= Cext * mu.restrict s.
```

Using the supplied equality on `s`, this is

```text
externalSourceMeasure.restrict s
  <= Cext * mu.restrict s.
```

Since `s subset T`,

```text
mu.restrict s <= mu.restrict T,
```

so by monotonicity of scalar multiplication of measures,

```text
externalSourceMeasure.restrict s
  <= Cext * mu.restrict T.
```

Producting with the fixed regular-coordinate Haar measure `nu` preserves this
finite-scalar domination:

```text
(externalSourceMeasure.restrict s).prod nu
  <= Cext * (mu.restrict T).prod nu.
```

The existing external-product finite-integral theorem then transfers
integrability from `(mu.restrict T).prod nu` to
`(externalSourceMeasure.restrict s).prod nu`, provided `Cext < infinity`.

## Boundary

This proves no chart-image measurability and no equality
`sourceChart '' W = sourceLocal`.  It also does not identify the original DLN
prior with the external source measure.  It is only the bounded-density
handoff over a caller-supplied measurable piece, such as a measurable chart
image once that measurability is available separately.
