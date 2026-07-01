# Reproduction - A2 p.13 Formal-product to Original-volume Domination

Date: 2026-07-01.

Status: pen-and-paper check completed before Lean.

## Question

Suppose the p.13 formal-product chart-piece measure is already dominated by a
source reference measure. Does the restricted original edge-family volume inherit
a domination by the same reference measure, with the inverse tuple-side Haar
scalar multiplying the bound?

## Calculation

Let `formal` be the p.13 formal-product chart measure restricted to
`chartPiece`, and let `original` be
`originalEdgeFamilyVolume.restrict chartPiece`. The existing inverse-scalar
comparison gives

```text
original = c^{-1} • formal.
```

If a supplied source-reference comparison gives

```text
formal <= D • sourceRef,
```

then scalar monotonicity and associativity give

```text
original <= c^{-1} • (D • sourceRef)
         = (c^{-1} * D) • sourceRef.
```

If the source-reference comparison itself is supplied in bounded-density form,

```text
formal = (sourceRef.withDensity formalDensity).restrict chartPiece,
formalDensity <= D  sourceRef.restrict chartPiece-a.e.,
```

then `restrict_withDensity_le_smul_of_ae_le` first gives

```text
formal <= D • sourceRef,
```

and the preceding calculation applies.

## Nonclaims

This does not prove the formal-product/source-reference domination, the
formal-product/source-reference density identity, passive-theta source-image
equality, source coverage, source-rank coverage, scalar normalization, normal
crossings, pole order, or RLCT extraction.
