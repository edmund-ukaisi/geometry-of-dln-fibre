# Review - A2 Case 2 endpoint-transport factor alignment

Reviewer: xhigh read-only checker `Epicurus`.

Verdict: PASS for the proposed statement shape and endpoint orientation.

The bridge-ready identities should be stated on submatrices of
`transported.C`, not as direct equalities unless the transported endpoint
family is literally the displayed endpoint family.  Since endpoint transport
defines

```text
(data.endpointTransport e).C p =
  (data.C p).submatrix (e p.succ).symm (e p.castSucc).symm,
```

the displayed factors are recovered by submatrixing with the forward
equivalences:

```text
(transported.C 1).submatrix (e 2) (e 1)
```

for the post-pivot residual block, and

```text
(transported.C 0).submatrix (e 1) (e 0)
```

for the free following factor.

Product order is `C 1 * C 0`: edge `1` is the displayed post-pivot residual
block and edge `0` is the displayed free following factor.

Nonclaims checked: no source production, no arbitrary retained-passive suffix
alignment, no canonical endpoint choices, no analytic/RLCT content, and no
quiver-paper input.

## Implementation Review

Reviewer: xhigh read-only implementation reviewer `Meitner`.

Verdict: PASS, no blocking findings.

Checks:

- The Lean endpoint orientation matches `endpointTransport`: transported
  factors are pulled back by `e.symm`, and the new lemmas recover displayed
  factors by submatrixing with forward `e`.
- The product order is `C 1 * C 0`: the residual block is edge `1`, and the
  free following factor is edge `0`.
- The all-pivot consumer removes only `hD` and `hF` for the explicit
  endpoint-transported datum.  It still requires displayed-product nonzeroness.
- The documentation records the same boundary and does not claim arbitrary
  `ofTopologyTuple` factor alignment, source-readback provenance, Jacobian
  comparison, normal crossings, pole order, or RLCT.
