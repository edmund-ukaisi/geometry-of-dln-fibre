# Statement Card - A2 Retained-Passive Ctop Tail Endpoint Substitution

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

## Lean Names

```text
Ctop_tail_zero_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
Ctop_tail_pos_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

## Reproduction

```text
reproduction-a2-retained-passive-ctop-tail-endpoint-substitution.md
```

## Claim

Starting from the existing Ctop bridge

```text
rawCtop - staged successor terms
  + Tail^{-1} * dTail * Tail^{-1} * coord.Ctop
= formalCtop,
```

substitute the endpoint derivative formula for `dTail`.

For `M=0`, `dTail=0`, so the tail term disappears.

For `0 < M`, with

```text
q = ⟨0,hM⟩ : Fin M,
p = q.succ,
Psucc(y) = residualFactorProduct A1seed(y) (Fin.last (M+1)) p.succ,
```

the substituted term is

```text
Tail^{-1}
  * ((fderiv Psucc z) v * data.A1seed p + Psucc z * v.1 q)
  * Tail^{-1}
  * coord.Ctop.
```

## Proof Plan

1. Invoke
   `Ctop_tail_fderiv_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`.
2. In the zero case, rewrite `dTail` by
   `fderiv_retainedPassive_A1TailAfterFirst_zero_apply`.
3. In the positive case, rewrite `dTail` by
   `fderiv_retainedPassive_A1TailAfterFirst_pos_apply`.
4. Simplify only zeros and definitions.  Do not commute or reassociate except
   as forced by the existing parenthesization.

## Status

Pen-and-paper reproduction written and Lean implementation proved locally.
Pen-and-paper scout `Godel` and Lean/API scout `Hooke` both recommended this
boundary.  Focused
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` build passed.
Independent xhigh implementation review `Galileo` passed.  Full `DLNFibre`
build passed.  `scripts/sorries` reported `0 sorry`, `0 #exit`,
`0 native_decide`, and `0 axiom`; `git diff --check` passed.  Axiom audit for
the two new theorems reported only `propext`, `Classical.choice`, and
`Quot.sound`.

## Nonclaims

This is not a closed finite-sum formula for `dTail`, not full `Ctop` source
staging, not `F3` staging, not determinant equality, not measure transport,
not normal crossings, not pole order, and not RLCT.
