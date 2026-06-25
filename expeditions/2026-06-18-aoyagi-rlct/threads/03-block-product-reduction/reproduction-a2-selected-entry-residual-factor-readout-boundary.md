# Reproduction - A2 selected-entry residual-factor readout boundary

Date: 2026-06-25.

Status: Lean target implemented for the finite residual-product handoff;
source/image equality remains supplied.

## Source Anchor

Aoyagi's p.13 product-reduction display leaves the cleaned residual term as an
ordered product of residual factors, written schematically as
`product_s C^(s)`.  The later selected-entry blow-up pages, especially pp.
15-22, work with a displayed residual block and following factors: one
selected entry is normalized, regular `Q` and `P` operations clear its row and
column, and the proof continues with a smaller residual block and compatible
following-factor product.

The source supports a factor-product reading.  It does not support replacing
the full multi-edge residual product by an arbitrary terminal selected-entry
matrix.

## Calculation

Let `E(y)` be the fixed-base matrix family obtained by evaluating the base edge
family at the selected-entry chart point `chartMap pivot y`.  Let `Cfac y p`
be a supplied family of compatible residual factors, one for every edge.

Assume that every transformed Schur residual block in the suffix recursion
reads as the corresponding factor:

```text
residualBlock(E(y), last, p) = Cfac(y,p).
```

The existing residual-factor theorem gives

```text
residualProduct(E(y), last, 0)
  = residualFactorProduct(Cfac(y), last, 0).
```

Now assume the real selected-entry product identity:

```text
residualFactorProduct(Cfac(y), last, 0)
  = matrix(c ↦ chartMap(pivot,y)(e c)).
```

Here `e` is the residual-index equivalence from fixed-base residual
coordinates to the selected-entry center coordinates.  Combining the two
equalities gives the selected-entry residual-product matrix identity required
by the existing readout bridge:

```text
residualProduct(E(y), last, 0)
  = matrix(c ↦ chartMap(pivot,y)(e c)).
```

This is the correct Aoyagi-shaped residual socket: the selected-entry matrix is
obtained as an ordered product through compatible intermediate residual
factors.

## Lean Target

Implemented in `SelectedEntryOriginalLossLocalMeasure.lean`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  paperEndpointFixedBaseResidualProduct_eq_selectedEntryCenter_matrix_of_residualFactorProduct_eq_matrix
```

The theorem consumes:

- a compatible factor family `Cfac`;
- block-readout equalities `residualBlock(E(y),last,p)=Cfac(y,p)`;
- the factor-product selected-entry identity;
- the residual-index equivalence.

It returns the residual-product matrix identity used by the existing
selected-entry residual-coordinate readout bridge.

## Nonclaims

- No construction of the compatible factor family.
- No proof of the factor-product selected-entry identity.
- No proof of the residual-index equivalence.
- No source chart construction or source/image equality.
- No source-measure transport, density/Jacobian identity, normal crossings,
  pole order, or RLCT.

## Review

Review:
`review-a2-selected-entry-residual-factor-readout-boundary.md`.

The boundary matches the xhigh source/API scout reports from `Kant` and
`Kuhn`: a fixed-pivot local selected-entry calculation is source-backed, but
the original p.13 source/image equality is not; the residual readout should
flow through compatible factors, not an arbitrary terminal matrix.
