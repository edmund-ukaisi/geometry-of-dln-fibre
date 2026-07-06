# A2 p.13 inverse-Jacobian density local bound

## Source calculation

Aoyagi's Lemma 2 performs one block elimination on a matrix

```text
A = (A1 A2; A3 A4)
```

with `A1` invertible.  The elementary substitutions are

```text
C4 = -A3 A1^{-1} A2 + A4
F2 = -A1^{-1} A2
F3 = -A3 A1^{-1}.
```

Theorem 3 iterates this step through the product.  In the induction step on
pp. 12-13, the new product-reduction variables are obtained from an invertible
block `C1' A1'`; after rewriting, the displayed substitutions are

```text
C^(S+1) = -A3' A1'^{-1} A2' + A4'
F2'' = -A1'^{-1} A2'
F3'' = F3' - (prod_{s=1}^S C^(s)) A3' (C1' A1')^{-1}.
```

In the Lean p.13 left-endpoint packaging, this appears as a raw-shaped target
tuple

```text
(Ctop, Dtail, F3, A1, F2, A3, C0)
```

with the p.13 section constraints

```text
A1 = Ctop,
A3 = 0.
```

The corresponding raw preimage tuple is

```text
(1, Dtail, F3, Ctop, -Ctop * F2, 0, C0).
```

This is a section of the ambient raw determinant chart, not the full ambient
raw chart.  Consequently the local density bound below is a bound for the
chart-side inverse determinant density evaluated along the p.13 section; it is
not a raw-Haar or original-prior transport statement.

## Elementary bound

Let

```text
Y(x,u) = paperEndpointFixedBaseP13RawOrderTuple(...)(x,u)
delta(x,u) = productReductionStepRawOrderInverseJacobianDensity(Y(x,u)).
```

The existing p.13 Lean calculation proves two facts at the self-base point:

1. `Y` is continuous at `(x0,0)` when the edge-family base is continuous at
   `x0` and equals the fixed reverse edge family there.
2. `Y(x0,0)` lies in the raw determinant chart, hence `delta(x0,0) > 0`.

Since the inverse-Jacobian density is continuous at determinant-chart target
points, `delta` is continuous at `(x0,0)`.  Put `d0 = delta(x0,0)`.  By
continuity and `0 < d0`, there is a product neighborhood of `(x0,0)` on which
`delta` is nonnegative and bounded above.  Shrinking the Euclidean factor gives
a radius `R` with `0 < R <= Rmax`; the upper bound may be taken as any
nonnegative constant above the local supremum produced by this continuity
argument.

For a relative source set `source`, the same conclusion is expressed in
`nhdsWithin x0 source`.  Unfolding the eventual statement gives an open
neighborhood `U` of `x0` such that for every `x in U cap source` and every
regular-coordinate vector `u` with `u in ball(0,R)`,

```text
0 <= delta(x,u)
delta(x,u) <= C.
```

This is the exact local handoff needed by downstream finite-integral arguments:
the p.13 inverse-Jacobian factor is a bounded nonnegative unit on a sufficiently
small product-coordinate neighborhood.

## Lean target

Implemented in:

```text
lean/DLNFibre/DLN/Aoyagi/ProductReductionStepRegularDensity.lean
```

Declarations:

```text
exists_pos_radius_le_eventually_nhdsWithin_productReductionStepRawOrderInverseJacobianDensity_paperEndpointFixedBaseP13RawOrderTuple_selfBase_bounds

exists_pos_radius_le_open_productReductionStepRawOrderInverseJacobianDensity_paperEndpointFixedBaseP13RawOrderTuple_selfBase_bounds
```

## Boundary

This proves only local boundedness of the p.13 chart-side inverse-Jacobian
density along the reduced section.  It does not identify formal-product Haar,
ambient determinant/raw Haar, selected-entry source measure, original prior,
normal crossings, pole order, or RLCT.
