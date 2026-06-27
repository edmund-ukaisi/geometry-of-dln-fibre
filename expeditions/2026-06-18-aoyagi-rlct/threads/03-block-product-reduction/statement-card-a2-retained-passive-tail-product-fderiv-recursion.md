# Statement Card - A2 Retained-Passive Tail Product FDeriv Recursion

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

## Lean Names

```text
differentiableAt_retainedPassiveA1seed_residualFactorProduct
fderiv_retainedPassive_A1seed_residualFactorProduct_self_apply
fderiv_retainedPassive_A1seed_residualFactorProduct_succ_castSucc_apply
```

## Reproduction

```text
reproduction-a2-retained-passive-tail-product-fderiv-recursion.md
```

## Claim

Let

```text
P_i(y) = residualFactorProduct
  (ofTopologyTuple y).A1seed (Fin.last (M+1)) i.
```

Then the endpoint product has zero derivative:

```text
d(P_j)_z(v) = 0.
```

For `q : Fin M`, with `p=q.succ : Fin (M+1)`,

```text
d(P_{p.castSucc})_z(v)
  = d(P_{p.succ})_z(v) * A1seed_z(p)
    + P_{p.succ}(z) * v.A1passive_q.
```

This is the recursive product rule for the passive top-left tail factors.

## Proof Plan

1. Prove differentiability of every suffix product by decreasing induction on
   the starting index, using the existing residual-product recursion and
   `differentiableAt_A1seed`.
2. Prove the endpoint derivative by reducing the endpoint product to the
   constant identity matrix.
3. Prove the recursive derivative step from the residual-product recursion and
   the bilinear matrix product derivative.
4. Rewrite the derivative of `A1seed(q.succ)` to the source tangent `v.1 q`.

## Status

Pen-and-paper reproduction written and Lean implementation proved.  Independent
xhigh implementation review passed after a documentation wording fix.  Focused
and full `DLNFibre` builds passed.  `scripts/sorries` reported `0 sorry`,
`0 #exit`, `0 native_decide`, and `0 axiom`; `git diff --check` passed.  Axiom
audit for the three new theorems reported only `propext`, `Classical.choice`,
and `Quot.sound`.

## Nonclaims

This is not a closed finite-sum formula for `dTail`.  It is not an inverse-tail
derivative theorem, not full `Ctop` source staging, not `F3` source staging,
not a determinant-one shear, not determinant equality, not a measure theorem,
not a normal-crossing theorem, not a pole-order theorem, and not an RLCT
theorem.
