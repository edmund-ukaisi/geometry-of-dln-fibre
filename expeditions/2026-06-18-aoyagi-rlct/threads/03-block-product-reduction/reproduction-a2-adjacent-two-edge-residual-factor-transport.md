# A2 adjacent two-edge residual-factor transport

## Boundary

This slice is finite product algebra for the explicit residual-factor product
`ChartLocalSuffixState.residualFactorProduct`. It isolates an adjacent
two-edge window inside a longer supplied residual-factor family.

It does not construct residual factors from a suffix state, prove Schur
residual blocks equal supplied factors, align fixed-base endpoint complement
indices with Case 2 row/column intervals, collapse a full retained-passive
suffix to an adjacent window, prove a pivot nonzero condition, construct a
source chart, prove source image coverage, prove measure pushforward or
Jacobian transport, compare the original loss, prove normal crossings, compute
pole order, or extract an RLCT.

## Pen-and-paper reproduction

For an explicit family

```text
C q : Matrix (kappa(q+1)) (kappa(q)).
```

the residual-factor product is the decreasing ordered product from a right
endpoint to a left endpoint. Over one edge, from `p+1` to `p`, this product is
just the single supplied factor:

```text
residualFactorProduct(C, p+1, p) = C_p.
```

For an adjacent two-edge window in a longer chain, use endpoints

```text
lo  = p,
mid = p+1,
hi  = p+2.
```

The transitivity theorem for residual-factor products splits the interval at
`mid`:

```text
residualFactorProduct(C, hi, lo)
  = residualFactorProduct(C, hi, mid)
      * residualFactorProduct(C, mid, lo).
```

Each one-edge factor then reduces to the corresponding supplied matrix:

```text
residualFactorProduct(C, hi, mid) = C_(p+1),
residualFactorProduct(C, mid, lo) = C_p.
```

Therefore the adjacent two-edge product has the fixed order

```text
residualFactorProduct(C, p+2, p) = C_(p+1) * C_p.
```

If the three endpoints are reindexed by equivalences

```text
e2 : kappa2 ~= kappa(hi),
e1 : kappa1 ~= kappa(mid),
e0 : kappa0 ~= kappa(lo),
```

then matrix product reindexing gives

```text
residualFactorProduct(C, hi, lo).submatrix(e2,e0)
  = C_(p+1).submatrix(e2,e1) * C_p.submatrix(e1,e0).
```

This is the generic transport needed before a Case 2 adjacent-window bridge:
the row, middle, and column endpoint equivalences plus factor identities must
still be supplied separately.

## Checks

- The factor order is right-to-left: upper/right edge `C p.succ` multiplies
  lower/left edge `C p.castSucc`.
- The middle endpoint is the canonical adjacent index
  `p.succ.castSucc`, propositionally aligned with `p.castSucc.succ`.
- The submatrix theorem uses only `Matrix.submatrix_mul_equiv`.
- Full fixed-base residual products still contain factors outside the adjacent
  window unless those are separately transported or shown to be absorbed.
