# Reproduction - A2 single-edge residual-product realisation

Date: 2026-06-25.

Status: pen-and-paper reproduction before Lean.  This is one-edge finite block
algebra for Aoyagi p.13 product coordinates.

## Source Boundary

Aoyagi p.13 introduces the regular blocks `Ctop - I`, `F2`, `F3` and a
residual block `D`.  In the endpoint-collapsed one-edge case, the raw
product-coordinate edge matrix is

```text
[ Ctop,       -Ctop F2
  -F3 Ctop,   D + F3 Ctop F2 ].
```

This note proves that the transformed Schur residual product of this single
edge is the supplied residual matrix `D`.  It is independent of the
Lehalleur-Rimanyi/quiver material.

## Calculation

Let

```text
E p = productCoordinateSingleEdgeMatrix F2 F3 Ctop D
```

for the unique edge `p : Fin 1`, and assume `IsUnit Ctop.det`.  The terminal
suffix state has

```text
B = 0, Ctop = I, D = I, L = I.
```

Thus the first transformed edge is the raw block matrix above.  Its Schur
residual block is

```text
(D + F3 Ctop F2) - (-F3 Ctop) Ctop^{-1} (-Ctop F2).
```

On the determinant chart, `Ctop^{-1}` is the inverse used by the Schur
residual definition.  Therefore

```text
(-F3 Ctop) Ctop^{-1} (-Ctop F2) = F3 Ctop F2,
```

and the Schur residual block is exactly `D`.

The existing suffix-field theorem records the same computation as

```text
S.D = D
```

for

```text
S = suffixState E p.succ p.castSucc (Fin.castSucc_le_succ p).
```

The existing suffix-state bridge gives

```text
S.D = residualProduct E p.succ p.castSucc (Fin.castSucc_le_succ p).
```

Combining the two equalities gives

```text
residualProduct E p.succ p.castSucc (Fin.castSucc_le_succ p) = D.
```

For the fixed-base real constructor `G(u,D)`, the unique edge matrix is exactly
`productCoordinateSingleEdgeMatrix F2 F3 Ctop D`, where `F2`, `F3`, and `Ctop`
are read from the regular Euclidean coordinate vector `u`.  The same theorem
therefore gives

```text
residualProduct G (Fin.last 1) 0 = D.
```

## Lean Target

Add in `ProductReduction.lean`:

```text
ChartLocalSuffixState.residualProduct_productCoordinateSingleEdge_eq
```

Add in `RegularSuspensionCoordinates.lean`:

```text
paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean_residualProduct_eq
```

## Boundary

- This is the transformed Schur residual product, not the raw lower-right
  block of the edge matrix.
- The determinant-unit hypothesis on `Ctop` is used for the Schur complement
  cancellation.
- This is a one-edge result.  It does not remove the intermediate-factor
  obstruction in multi-edge chains.
- It does not choose `D` from source data, construct a source chart, prove
  source coverage, transport measures, produce normal crossings, prove pole
  order, or extract RLCT.
