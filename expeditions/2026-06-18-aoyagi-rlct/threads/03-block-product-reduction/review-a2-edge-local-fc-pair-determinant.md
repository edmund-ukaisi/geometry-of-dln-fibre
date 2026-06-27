# Review - A2 edge-local `(F,C)` pair determinant

Reviewer: xhigh read-only scout `Lagrange the 4th`.

Status: passed; no blocking issues.

## Findings

No blocking issues were found.

The Lean formula theorem `edgeLocalFCPairLinearMap_apply` matches the stated
map.  The factorization is:

```text
(F, C) |-> (F, C - G*F)
(F, C) |-> (-A*F, C)
(F, C) |-> (F + H*C, C).
```

The composite is exactly

```text
(F, C) |->
  (-(A + H*G)*F + H*C,
   -G*F + C)
```

in `(F,C)` input and `(Y12,Y22)` output order.

The determinant sign and orientation are correct.  No product-coordinate swap
appears in the final edge-local map; the internal `prodComm` used in the
upper-shear determinant proof is only a conjugation, so any swap determinant
cancels.

The determinant proof over `CommRing` is legitimate.  It uses product-map
determinants, block lower-triangular determinant calculation for the lower
shear, conjugation invariance, and determinant multiplicativity under
composition.  It does not use field, invertibility, analytic derivative,
density, or RLCT assumptions.

## Low Items Addressed

The reproduction and statement card now state the Lean hypotheses: `CommRing K`,
finite index types, and the `DecidableEq rho` assumption for the square
determinant.

The notes now say that the Lean theorem is proved rather than planned.

The promoted generic product/shear determinant helpers are now used by
`ProductReductionStepJacobian.lean`, replacing the previous private duplicate
helpers there.

## Scope Check

No overclaiming was found.  The slice remains finite matrix-linear determinant
arithmetic only.  It is not a full retained-passive determinant theorem,
analytic `fderiv` theorem, density/pushforward theorem, normal-crossing
theorem, pole-order theorem, or RLCT theorem.
