# Reproduction - A2 signed-box model-loss adapter

Date: 2026-06-25.

Status: pen-and-paper reproduction and Lean formalisation for a generic
comparison adapter.

## Target

The signed-box theorem already proves finite lower-integral control for an
actual loss `loss` once we have, a.e. on the signed box,

```text
c * prod_i |x_i|^(2*k_i) <= loss(x),
0 <= density(x),
density(x) <= C * prod_i |x_i|^h_i.
```

For p. 13 applications, the natural lower bound may first be obtained for an
intermediate model loss.  This adapter records the elementary handoff from a
model loss to the actual loss.

## Derivation

Let

```text
M(x) = prod_i |x_i|^(2*k_i).
```

Assume `c>0`, `K>0`, and a.e.

```text
c * M(x) <= modelLoss(x),
modelLoss(x) <= K * loss(x).
```

Then a.e.

```text
c * M(x) <= K * loss(x).
```

Since `K>0`, divide by `K`:

```text
(c * M(x)) / K <= loss(x).
```

Equivalently,

```text
(c/K) * M(x) <= loss(x).
```

Also `c/K>0`.  Therefore the existing signed-box residual/density theorem
applies to `loss` with lower-bound constant `c/K`, the same density bounds,
and the same strict inequalities

```text
2*t*k_i < h_i + 1.
```

The comparison used here is one-way:

```text
modelLoss(x) <= K * loss(x).
```

It is not a two-sided comparability theorem.

## Lean Shape

Lean proves this in

```text
lean/DLNFibre/DLN/Aoyagi/MonomialChartIntegrability.lean
```

as

```text
lintegral_ofReal_loss_rpow_neg_mul_density_signedBox_lt_top_of_modelLoss_le_const_mul_loss
```

## Boundary

This theorem is only a signed-box comparison adapter.  It does not construct
the model loss, prove p. 13 source-filter inequalities as a.e. signed-box
chart statements, prove density/Jacobian transport, prove chart coverage,
handle endpoint/divergent behavior, produce normal crossings, or extract RLCT.
