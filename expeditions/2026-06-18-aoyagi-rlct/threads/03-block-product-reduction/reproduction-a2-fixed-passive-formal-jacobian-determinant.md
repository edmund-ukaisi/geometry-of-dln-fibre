# A2 fixed-passive formal Jacobian determinant

Status: reproduced by controller; independently checked by xhigh
pen-and-paper scout; Lean-proved as a finite formal determinant theorem.

## Scope

This note reproduces the determinant of the one-step fixed-passive p.13
formal tangent map

```text
productStepFixedPassiveFormalJacobian
```

from `ProductReductionStepJacobian.lean`.  The calculation is purely finite
linear algebra.  It is not an analytic derivative theorem, source-prior
pushforward, normal-crossing statement, pole-order theorem, or RLCT theorem.

The variables are

```text
raw:   (dC1, dF3old, dA2, dA4)
chart: (dCtop, dF3,    dF2, dC)
```

with fixed parameters `D`, `A1`, and `A3`.

## Formal formulas

The fixed-passive formal tangent map is

```text
dCtop = dC1 * A1

dF2 = - A1^{-1} * dA2

dF3 = dF3old
       + D * A3 * Ctop^{-1} * dCtop * Ctop^{-1}
where Ctop = C1 * A1

dC = dA4 - A3 * A1^{-1} * dA2.
```

After exposing the diagonal variable

```text
dF2 = -A1^{-1} * dA2,
```

the last line becomes

```text
dC = dA4 + A3 * dF2.
```

Thus the map factors as

```text
(F3 shear) o (C shear) o (diagonal map).
```

## Determinant factors

The diagonal map is

```text
dC1    |-> dC1 * A1
dF3old |-> dF3old
dA2    |-> -A1^{-1} * dA2
dA4    |-> dA4.
```

The first nontrivial block is right multiplication by `A1` on
`rho x rho` matrices, hence contributes

```text
det(A1)^(|rho|).
```

The second nontrivial block is left multiplication by `-A1^{-1}` on
`rho x nu` matrices, hence contributes

```text
det(-A1^{-1})^(|nu|).
```

The `C`-coordinate shear

```text
(dF2, dA4) |-> (dF2, dA4 + A3 * dF2)
```

has determinant `1`.  The `F3`-coordinate shear

```text
(dCtop, rest) |->
  (dCtop, rest + (D * A3 * Ctop^{-1} * dCtop * Ctop^{-1}, 0, 0))
```

also has determinant `1`.

Therefore, in the raw-to-chart orientation,

```text
det J =
  det(A1)^(|rho|)
  * det(-A1^{-1})^(|nu|).
```

Over the reals, on the determinant chart where `det A1` is nonzero, this
simplifies to

```text
|det J| = |det A1|^(|rho|) * |det A1|^(-|nu|).
```

The sign factor from `det(-A1^{-1})` and the reciprocal absolute-value
simplification are intentionally not simplified in Lean; the Lean theorem is a
formal determinant identity for the linear map as defined, without chart
invertibility hypotheses.

## Lean status

Lean now proves the factorization and determinant formula in
`ProductReductionStepJacobian.lean`:

```text
productStepFixedPassiveDiagonalFormalJacobian
productStepFixedPassiveCShear
productStepFixedPassiveF3Shear
productStepFixedPassiveFormalJacobian_eq_shear_comp_diagonal
productStepFixedPassiveDiagonalFormalJacobian_det_eq
productStepFixedPassiveCShear_det_eq_one
productStepFixedPassiveF3Shear_det_eq_one
productStepFixedPassiveFormalJacobian_det_eq_multiplication_blocks
productStepFixedPassiveFormalJacobian_det_eq
```

The final theorem is

```text
LinearMap.det (productStepFixedPassiveFormalJacobian C1 D A1 A3)
  = A1.det ^ Fintype.card rho
    * (-A1^{-1}).det ^ Fintype.card nu.
```

## Caveats

This theorem is for the fixed-passive one-step map with `D`, `A1`, and `A3`
held fixed.  It must not be compared directly with the retained-passive total
formula without matching orientation and endpoint solves.  In particular, the
retained-passive total formula has additional `Tail`, edge-local `A p`, and
`LastTop` factors, and its intended density use is in the retained
coordinate-to-raw-order orientation.
