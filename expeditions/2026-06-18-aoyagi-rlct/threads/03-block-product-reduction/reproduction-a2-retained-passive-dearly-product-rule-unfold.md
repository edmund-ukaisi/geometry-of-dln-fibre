# Reproduction - A2 retained-passive dEarly product-rule unfold

Date: 2026-06-27.

Status: controller pen-and-paper reproduction; Lean proved; focused and full
builds passed; `scripts/sorries`, `git diff --check`, and axiom audit passed;
xhigh math and Lean-terrain scout checks and implementation review passed.

This note is independent of the quiver-based paper.  It is the next elementary
retained-passive `dEarly` rung after the recursive derivative unfold.  It
expands only the derivative of the current summand in the recurrence.

## Setup

Let `N = M + 1`.  For a determinant-chart tuple `y`, write

```text
A_y(r) = coord_y.solvedA1(r),
G_y(r) = retainedPassiveA3WithoutLast(data_y.A3seed)(r),
C_y(r) = data_y.C(r).
```

For `p : Fin N`, define

```text
E_p(y) =
  retainedPassiveLowerLeftProductTailSum
    A_y G_y C_y p.val (Nat.le_of_lt p.isLt),

D_p(y) =
  residualFactorProduct C_y (Fin.last N) p.succ p.succ.le_last,

G_p(y) =
  retainedPassiveA3WithoutLast(data_y.A3seed)(p),

P_p(y) =
  residualFactorProduct A_y (Fin.last N) p.castSucc p.castSucc.le_last,

E_next(y) =
  retainedPassiveLowerLeftProductTailSum
    A_y G_y C_y (p.val + 1) (Nat.succ_le_of_lt p.isLt).
```

The already-landed recurrence gives

```text
dE_p =
  d[-(D_p * G_p * P_p^-1)] + dE_next.
```

All products are matrix products, so their order is part of the statement.

## Product-Rule Calculation

Fix a determinant-chart point `z` and a tangent `v`.  Abbreviate

```text
D  = D_p(z),      dD = d(D_p)_z(v),
G  = G_p(z),      dG = d(G_p)_z(v),
P  = P_p(z),      dP = d(P_p)_z(v),
dN = d(E_next)_z(v).
```

The current product is

```text
Q(y) = D_p(y) * G_p(y) * P_p(y)^-1.
```

Using the product rule in the parenthesization `(D_p * G_p) * P_p^-1`,

```text
dQ =
  (dD * G + D * dG) * P^-1
    + D * G * d(P^-1).
```

Distributing the right multiplication by `P^-1` gives

```text
dQ =
  dD * G * P^-1
  + D * dG * P^-1
  + D * G * d(P^-1).
```

On the determinant chart, `P.det` is a unit.  Matrix inversion has derivative

```text
d(P^-1) = -P^-1 * dP * P^-1.
```

Therefore

```text
d[-Q] =
  -dD * G * P^-1
  -D * dG * P^-1
  +D * G * P^-1 * dP * P^-1.
```

Combining this with the already-landed recursive split gives

```text
dE_p =
  -dD * G * P^-1
  -D * dG * P^-1
  +D * G * P^-1 * dP * P^-1
  +dN.
```

No factors commute.  The positive inverse-derivative term is associatively
`(((D * G) * P^-1) * dP) * P^-1`.

## Terminal Edge

At the terminal edge, `G_p` is still the retained-passive early family

```text
retainedPassiveA3WithoutLast(data_y.A3seed)(p),
```

not the solved terminal lower-left block.  Hence for terminal `p` the value is
zero, and the `dG` derivative is the derivative of the constant-zero terminal
branch.  This slice must not replace it by `coord.solvedA3(Fin.last M)`.

## Lean Scope

Lean proves the expanded recurrence as

```text
fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_apply
```

in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

The theorem leaves `(fderiv Cprod)`, `(fderiv A3p)`, `(fderiv Pcast)`, and the
successor-tail derivative explicit.  It only expands the current summand by
the product rule and the matrix-inverse derivative.

## Independent Checks

Xhigh math scout `Cicero` passed the displayed calculation and confirmed the
noncommutative order, the determinant-chart input for `P^-1`, and the
retained-passive terminal-zero caveat.

Xhigh Lean-terrain scout `Euler` confirmed the proof route using
`hasFDerivAt_matrix_inv_of_isUnit_det`, `matrixMulContinuousLinearMap`, and
`ContinuousLinearMap.hasFDerivAt_of_bilinear`.

Xhigh implementation reviewer `Wegener` passed the Lean theorem
`fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_apply`.

## Kill Conditions

- If the inverse derivative is written with `dP` on the left, the calculation
  is wrong.
- If `D`, `G`, `P^-1`, or `dP` are commuted, the calculation is wrong.
- If the terminal `G` is replaced by solved terminal `A3`, the recurrence is
  for the wrong lower-left tail.
- If this is advertised as source staging or target staging for `dD`, `dG`, or
  `dP`, it overclaims.
- If this is advertised as determinant equality, measure transport, normal
  crossings, pole order, or RLCT, it overclaims.

## Nonclaims

No source or target staging for `dD`, `dG`, or `dP`; no full positive-tail `F3`
target staging; no whole-tuple target-side normalization; no determinant-one
target-side `LinearEquiv`; no actual derivative determinant formula; no
measure transport; no normal crossings; no pole order; and no RLCT follows
from this product-rule unfold.
