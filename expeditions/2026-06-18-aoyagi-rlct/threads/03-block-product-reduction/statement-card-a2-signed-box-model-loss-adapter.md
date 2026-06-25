# Statement Card - A2 signed-box model-loss adapter

## Statement

On a signed box, suppose

```text
c * prod_i |x_i|^(2*k_i) <= modelLoss(x),
modelLoss(x) <= K * loss(x),
0 <= density(x),
density(x) <= C * prod_i |x_i|^h_i
```

a.e., with `c>0`, `K>0`, `C>=0`, `t>=0`, `R_i>0`, and

```text
2*t*k_i < h_i + 1.
```

Then

```text
int^- x, ofReal(loss(x)^(-t) * density(x)) < infinity
```

for the signed-box product measure.

## Lean Name

```text
lintegral_ofReal_loss_rpow_neg_mul_density_signedBox_lt_top_of_modelLoss_le_const_mul_loss
```

## Proof Input

The proof derives

```text
(c/K) * prod_i |x_i|^(2*k_i) <= loss(x)
```

and delegates to

```text
lintegral_ofReal_loss_rpow_neg_mul_density_signedBox_lt_top
```

## Nonclaims

No p. 13 chart construction, model-loss construction, source-filter to
signed-box a.e. handoff, Jacobian/prior transport, endpoint theorem,
normal-crossing construction, pole order, or RLCT extraction is proved.
