# Reproduction - A2 p.13 Formal-product Density Identity

Date: 2026-07-01.

Status: pen-and-paper check completed before Lean.

## Question

The p.13 formal-product chart measure is already proved to be a positive Haar
scalar multiple of the restricted original edge-family volume on every
measurable chart piece contained in the named p.13 source set. Can this be
restated in the bounded-density identity form consumed by the source-image
density sockets?

## Calculation

Let `formal` be the p.13 formal-product source-chart measure restricted to
`chartPiece`, and let `original` be
`originalEdgeFamilyVolume.restrict chartPiece`. The existing bridge gives

```text
formal = c • original
```

for the tuple-side Haar scalar `c`, with `0 < c`. Therefore the existing
inverse-scalar corollary gives

```text
original = c^{-1} • formal.
```

For any measure `μ`,

```text
μ.withDensity (fun _ => a) = a • μ.
```

Applying this with `μ` equal to the unreduced formal-product chart measure and
then restricting to `chartPiece` gives

```text
originalEdgeFamilyVolume.restrict chartPiece =
  (formalProductMeasure.withDensity (fun _ => c^{-1})).restrict chartPiece.
```

The bounded-density hypothesis required by later sockets is tautological:

```text
c^{-1} <= c^{-1}
```

almost everywhere for `formalProductMeasure.restrict chartPiece`.

## Nonclaims

This does not identify the formal-product p.13 chart measure with the
passive-theta source-image reference. It does not prove source coverage,
source-rank coverage, scalar normalization `c = 1`, normal crossings, pole
order, or RLCT extraction.
