# Reproduction - A2 Retained-Passive Raw-Order Derivative/Jacobian Plan

Date: 2026-06-26.

Status: pen-and-paper derivative target and Lean API plan.  The exact
determinant formula below is a candidate for further checking; the current
Lean checkpoint proves only pointwise raw-block formulas.

## Source And Coordinate Order

This note concerns the retained-passive tuple endomap

```text
topologyTupleEdgeRawOrder :
  TopologyTuple rho kappa R -> TopologyTuple rho kappa R.
```

Write a source tuple in Lean order as

```text
z = (a, (f, (ell, (c, (s, h)))))
```

where

```text
a   : Fin M -> Matrix rho rho R
f   : Fin (M+1) -> Matrix rho (kappa p.castSucc) R
ell : Fin M -> Matrix (kappa p.castSucc.succ) rho R
c   : Fin (M+1) -> Matrix (kappa p.succ) (kappa p.castSucc) R
s   : Matrix rho rho R
h   : Matrix (kappa (Fin.last (M+1))) rho R.
```

The embedded full coordinate data has

```text
A1seed_0 = 0,        A1seed_(q+1) = a_q,
F2full_p = f_p,      F2full_last = 0,
A3seed_q = ell_q,    A3seed_last = 0,
C = c, Ctop = s, F3 = h.
```

The solved full variables are

```text
A_p = solvedA1_p,
L_p = solvedA3_p.
```

Concretely, if `T = A_M ... A_1`, then

```text
A_0 = T^{-1} s.
```

For the lower-left endpoint, with `L_p = ell_p` for `p < M`,

```text
Early = sum over p < M of the earlier retained-passive lower-left tail,
L_M = -(h - Early) * (A_M ... A_1).
```

The Lean definitions express `Early` by
`retainedPassiveLowerLeftProductTailSum` and the final product by
`residualFactorProduct`.

## Raw Edge Formula

For each edge `p : Fin (M+1)`, put

```text
G_p = F2full_(p.succ).
```

The fixed-base edge is

```text
fromBlocks 1 G_p 0 1 *
  fromBlocks A_p (-(A_p * F2full_(p.castSucc))) L_p
    (C_p - L_p * F2full_(p.castSucc)).
```

Therefore its raw blocks are

```text
X_p = A_p + G_p * L_p
B_p = -(A_p * F2full_(p.castSucc))
        + G_p * (C_p - L_p * F2full_(p.castSucc))
Y_p = L_p
Z_p = C_p - L_p * F2full_(p.castSucc).
```

The raw target tuple packs these blocks as

```text
A1passive target q = X_(q.succ)
F2 target p        = B_p
A3passive target q = Y_(q.castSucc)
C target p         = Z_p
Ctop target        = X_0
F3 target          = Y_last.
```

This is the current Lean checkpoint.

## Differential Shape

The endpoint solve for the first top-left block contributes

```text
dA_0 = T^{-1} ds - T^{-1} (dT) A_0.
```

The endpoint solve for the final lower-left block contributes

```text
dL_M = -dh * T + dEarly * T - (h - Early) * dT.
```

For each raw edge block:

```text
dX_p = dA_p + dG_p * L_p + G_p * dL_p
dY_p = dL_p
dZ_p = dC_p - dL_p * F2full_(p.castSucc)
        - L_p * dF2full_(p.castSucc)
dB_p = -dA_p * F2full_(p.castSucc)
        - A_p * dF2full_(p.castSucc)
        + dG_p * Z_p + G_p * dZ_p.
```

After output shears and a descending-edge ordering, the expected diagonal
pieces are

```text
dA_p,
-A_p * dF2full_(p.castSucc),
dL_p,
dC_p.
```

The determinant-unit theorem should be proved first by constructing a formal
linear equivalence from these triangular pieces, not by committing to an
exact signed determinant formula.

## Candidate Absolute Determinant

Let `r = |rho|` and `k_i = |kappa_i|`.  The candidate absolute determinant
from the reproduction scouts is

```text
J =
  |det T|^{-r}
  * product_{p=0}^M |det A_p|^{k_p}
  * |det A_M|^{k_{M+1}}.
```

The first factor comes from `s -> A_0` by left multiplication with `T^{-1}`;
the last factor comes from `h -> L_M` by right multiplication with `-T` in
the endpoint solve.  For `M = 0`, this predicts

```text
J = |det s|^{k_0 + k_1}.
```

The signed determinant is not fixed here because it depends on basis order,
the signs in the `F2` and `F3` blocks, and tuple permutations.

## Lean Strategy

The safe Lean order is:

1. Prove pointwise raw block formulas for the fixed-base edge map and
   `topologyTupleEdgeRawOrder`.
2. Prove `DifferentiableAt topologyTupleEdgeRawOrder` at determinant-chart
   points over `R = Real`, using the matrix inverse derivative and the
   determinant-chart unit hypotheses.
3. Define a formal tangent equivalence for the retained-passive map and prove
   its determinant is a unit on the determinant chart.
4. Only after the formal tangent map is identified with `fderivWithin`, define
   the positive Jacobian density and state a measure pushforward.

## Nonclaims

This note proves no derivative, determinant theorem, density continuity,
measure pushforward, source-rank coverage, original-loss comparison, normal
crossing theorem, pole order, or RLCT statement.
