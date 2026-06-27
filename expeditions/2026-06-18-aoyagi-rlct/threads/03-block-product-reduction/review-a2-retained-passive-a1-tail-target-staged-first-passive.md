# Review - A2 retained-passive A1-tail first passive target staging

Date: 2026-06-27.

Reviewer: xhigh read-only reviewer `Banach the 2nd`.

Verdict: PASS.  No required fixes.

## Scope Reviewed

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Reviewed names:

```text
fderiv_retainedPassive_A1seed_residualFactorProduct_succ_castSucc_target_staged_apply
fderiv_retainedPassive_A1TailAfterFirst_pos_target_staged_apply
Ctop_tail_pos_firstA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
Ctop_tail_pos_firstA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
```

Companion docs:

```text
reproduction-a2-retained-passive-a1-tail-target-staged-first-passive.md
statement-card-a2-retained-passive-a1-tail-target-staged-first-passive.md
```

## Findings

- The Lean names are present and accurately scoped.  The names do not overclaim:
  `firstA1_target_staged` signals only the first passive `A1` replacement, and
  the residual `(fderiv Psucc z) v` remains explicit.
- The indexing is faithful.  The first passive coordinate is `q : Fin M` with
  `p = q.succ`; the passive `A1` replacement uses `q.succ`, not the separate
  `Ctop` endpoint shear index `0 : Fin (M+1)`.
- Matrix order is preserved:

  ```text
  (fderiv Psucc z) v * data.A1seed p + Psucc z * targetA1
  Tail⁻¹ * (...) * Tail⁻¹ * coord.Ctop
  ```

- The reproduction and statement card match the Lean slice and preserve the
  nonclaims.

## Nonclaims Rechecked

No empty-suffix cleanup for `M = 1`, no terminal raw lower-left zero claim, no
full `Ctop` or `F3` target staging, no determinant equality, no measure
transport, no normal crossings, no pole order, and no RLCT.
