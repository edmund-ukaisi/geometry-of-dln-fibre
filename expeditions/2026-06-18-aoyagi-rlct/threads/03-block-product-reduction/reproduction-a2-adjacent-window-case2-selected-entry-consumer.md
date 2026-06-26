# A2 adjacent-window Case 2 selected-entry consumer

## Boundary

This slice consumes the generic adjacent two-edge residual-factor transport
for the displayed Case 2 post-pivot lower product.  It is still conditional:
the endpoint equivalences and the two factor identities are supplied.

It does not construct endpoint equivalences, identify fixed-base endpoint
complements with Case 2 row/column intervals, collapse a full retained-passive
suffix to this adjacent window, prove the fixed successor pivot is nonzero,
construct a source chart, prove source image coverage, prove pushforward or
Jacobian transport, compare the original loss, prove normal crossings, compute
pole order, or extract an RLCT.

## Pen-and-paper reproduction

Let `C` be a supplied residual-factor family in a longer chain, and choose an
adjacent window

```text
lo  = p,
mid = p+1,
hi  = p+2.
```

The previous generic transport proves

```text
residualFactorProduct(C, hi, lo) = C_(p+1) * C_p.
```

Suppose the three window endpoints are identified with the Case 2 post-pivot
domains:

```text
e2 : Case2ResidualRowIndex(n,S,J+1) ~= kappa(hi),
e1 : Case2ResidualColIndex(n,S,J+1) ~= kappa(mid),
e0 : tau ~= kappa(lo).
```

Assume the two visited factors are the displayed post-pivot residual block and
following factor after these reindexings:

```text
C_(p+1).submatrix(e2,e1) = D_(J+1),
C_p.submatrix(e1,e0) = C'_+.
```

Then reindexing the adjacent product gives

```text
residualFactorProduct(C, hi, lo).submatrix(e2,e0)
  = D_(J+1) * C'_+
  = case2DisplayedPostPivotFreeTwoEdgeFactorProduct.
```

If an entrywise selected-entry readout identifies that displayed product with
a center-coordinate matrix, then equality after endpoint equivalences upgrades
the unreindexed adjacent product to that center-coordinate matrix.

For the fixed-pivot nonzero variant, we do not prove nonzero.  We only reuse
the existing finite selected-entry inverse: a supplied nonzero value of the
displayed product at the fixed successor pivot produces `yNext`, hence the
entrywise readout, hence the adjacent-window residual-factor matrix identity.

## Checks

- Factor order is `C p.succ` followed by `C p.castSucc`.
- The theorem is about the adjacent product from `p+2` to `p`, not a full
  endpoint product.
- The pivot nonzero condition, when used, remains a supplied displayed-product
  hypothesis.
