# Obstruction - A2 retained-passive dEarly terminal Psucc is not empty

Date: 2026-06-27.

Status: xhigh review obstruction; false cleanup attempt removed.

## Finding

The terminal `dPcast` substitution theorem uses

```text
q = Fin.last M : Fin (M+1),
p = q.castSucc : Fin ((M+1)+1),
r = q.succ     : Fin ((M+1)+1).
```

For the solved-`A1` suffix product, the successor product starts at
`p.succ`, not at `r.succ`.

```text
Psucc(y) = residualFactorProduct solvedA1_y final p.succ.
```

Here `p.succ` is the penultimate endpoint.  The final endpoint is `r.succ`.
Equivalently, `p.succ = r.castSucc`, not `r.succ`.  Therefore `Psucc` is a
one-edge suffix, not the empty product.

## Consequence

The attempted cleanup

```text
Psucc(y) = 1,
dPsucc_z(v) = 0
```

is false at these indices.  The terminal `dPcast` substitution must keep
`Psucc` and `dPsucc` explicit unless a separate one-edge formula is proved.

The already banked theorem

```text
fderiv_retainedPassiveLowerLeftProductTailSum_last_product_dCprod_dG_dPcast_apply
```

is correctly scoped because it leaves `Psucc` explicit.

## Review Source

Read-only xhigh reviewer `Meitner` found the indexing obstruction.  The build
failure on the false cleanup attempt produced the same obstruction: Lean could
not prove

```text
(Fin.last M).castSucc.succ = Fin.last ((M+1)+1).
```

## Kill Conditions

- Do not state terminal `Psucc = 1` for the indices above.
- Do not replace terminal `dPsucc` by zero.
- Do not source-stage `d(solvedA1 p)` as a passive tangent.
- Preserve the factor order in the existing terminal `dPcast` substitution.

## Next Route

The viable next step is the solved-`A1` derivative split:

```text
d(solvedA1 q.succ) = v.1 q,
d(solvedA1 0) = Tail^-1*dCtop - Tail^-1*dTail*Tail^-1*Ctop.
```

The zero branch must keep the inverse-tail product-rule order and determinant
chart hypothesis.
