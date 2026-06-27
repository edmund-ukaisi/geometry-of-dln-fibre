# Reproduction - A2 retained-passive dEarly recursive unfold

Date: 2026-06-27.

Status: controller pen-and-paper reproduction; Lean proved; focused and full
builds passed; `scripts/sorries`, `git diff --check`, and axiom audit passed;
xhigh math/Lean/hardener scout checks and implementation review passed.

This note is independent of the quiver-based paper.  It isolates the next
elementary piece needed after the positive-tail terminal `dLast` substitution:
the Frechet derivative of the earlier lower-left product-tail sum `Early`.

## Setup

Let `N = M + 1`.  For a retained-passive tuple `y`, write

```text
A_y(r) = coord_y.solvedA1(r),
B_y(r) = retainedPassiveA3WithoutLast(data_y.A3seed)(r),
C_y(r) = data_y.C(r).
```

The earlier lower-left tail used in the `F3` bridge is

```text
Early(y) =
  retainedPassiveLowerLeftProductTailSum
    A_y B_y C_y 0 (Nat.zero_le N).
```

For a general edge `p : Fin N`, define the tail from `p` by

```text
E_p(y) =
  retainedPassiveLowerLeftProductTailSum
    A_y B_y C_y p.val (Nat.le_of_lt p.isLt).
```

Also define the current products

```text
D_p(y) =
  residualFactorProduct C_y (Fin.last N) p.succ p.succ.le_last,

P_p(y) =
  residualFactorProduct
    A_y (Fin.last N) p.castSucc p.castSucc.le_last,

G_p(y) = B_y(p).
```

Then the existing tail-sum recurrence gives

```text
E_p(y) = -(D_p(y) * G_p(y) * P_p(y)^-1) + E_{p+1}(y),
```

where

```text
E_{p+1}(y) =
  retainedPassiveLowerLeftProductTailSum
    A_y B_y C_y (p.val + 1) (Nat.succ_le_of_lt p.isLt).
```

The order is part of the definition: `D_p` multiplies the lower-left block
`G_p` on the left, and the top product inverse `P_p^-1` multiplies on the
right.

## Derivative Calculation

Fix a determinant-chart point `z` and a tangent `v`.  Abbreviate evaluation at
`z` by omitting `(z)`, and write

```text
dD_p = d(D_p)_z(v),
dG_p = d(G_p)_z(v),
dP_p = d(P_p)_z(v),
dE_p = d(E_p)_z(v).
```

The product rule for the current summand gives

```text
d(D_p * G_p * P_p^-1)
  = dD_p * G_p * P_p^-1
      + D_p * dG_p * P_p^-1
      + D_p * G_p * d(P_p^-1).
```

On the determinant chart the top product `P_p` has unit determinant, so the
matrix inverse derivative is

```text
d(P_p^-1) = -P_p^-1 * dP_p * P_p^-1.
```

Therefore the recursive derivative unfold is

```text
dE_p =
  -(dD_p * G_p * P_p^-1
      + D_p * dG_p * P_p^-1
      + D_p * G_p * d(P_p^-1))
    + dE_{p+1}.
```

Equivalently, after substituting the inverse derivative,

```text
dE_p =
  -dD_p * G_p * P_p^-1
  -D_p * dG_p * P_p^-1
  +D_p * G_p * P_p^-1 * dP_p * P_p^-1
  +dE_{p+1}.
```

All products are noncommutative and must stay in the displayed order.

## Terminal Edge

The terminal lower-left seed for this early tail is not the solved terminal
lower-left block.  By definition,

```text
B_y(Fin.last M) = 0.
```

Thus the terminal summand in `Early` is zero.  Its derivative is also zero:
the `dD` and `dP` terms are multiplied by `G_p = 0`, and the `dG` term is zero
because the terminal `B` family is the constant zero function.  This is why
`Early` excludes the terminal `F3`-dependent solved lower-left block.

## Lean Scope

The first Lean target should be a recursive derivative theorem for an arbitrary
`p : Fin (M + 1)`, not a full positive-tail `F3` theorem.  A useful first
statement is the product-rule version

```text
fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_apply
```

for the functions `E_p`, `D_p`, `G_p`, and `P_p` above.  It should either keep
`d(P_p^-1)` explicit or include a companion inverse-derivative rewrite using
`hasFDerivAt_matrix_inv_of_isUnit_det`.

This recurrence is a derivative expansion only.  It is not yet target staging
for `dEarly`.  Target staging will still require replacing the derivative
pieces for `D_p`, `G_p`, and `P_p` by the appropriate source- or
target-recovered tangent data and then iterating the recurrence.

## Independent Checks

Xhigh math scout `Tesla` passed this recurrence and confirmed that it is a
derivative expansion only, not source-staged or target-staged.

Xhigh Lean-terrain scout `Beauvoir` recommended the minimal first Lean theorem
`fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_apply`, keeping the
current summand derivative explicit before expanding inverse derivatives.

Xhigh hardener/fidelity scout `Linnaeus` passed the scope as a retained-passive
derivative hardening step and warned not to call it full positive-tail `F3`
target staging.

Xhigh implementation reviewer `Faraday` passed the Lean theorem
`fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_apply`.

## Kill Conditions

- If the terminal `G_p` in `Early` is replaced by `coord.solvedA3(Fin.last M)`,
  the recurrence is for the wrong tail.
- If the displayed right multiplication by `P_p^-1` is commuted past another
  factor, the noncommutative product rule is wrong.
- If the inverse derivative is written as `-dP_p * P_p^-1 * P_p^-1` or with
  any other order than `-P_p^-1 * dP_p * P_p^-1`, the matrix inverse
  derivative is wrong.
- If this is advertised as full positive-tail `F3` target staging, determinant
  equality, measure transport, normal crossings, pole order, or RLCT, it
  overclaims.

## Nonclaims

No full positive-tail `F3` target staging, no whole-tuple target-side
normalization, no determinant-one target-side `LinearEquiv`, no actual
derivative determinant formula, no measure transport, no normal crossings, no
pole order, and no RLCT follows from this recursive derivative unfold.
