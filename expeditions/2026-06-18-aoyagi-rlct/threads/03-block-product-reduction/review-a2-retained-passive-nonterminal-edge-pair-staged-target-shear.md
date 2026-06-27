# Review - A2 retained-passive nonterminal edge-pair staged target shear

Date: 2026-06-27.

Status: PASS after repair.

## Scope

This review covers the one-step nonterminal retained-passive `(F2,C)` staged
target package in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`, with the
matching reproduction and statement card:

- `reproduction-a2-retained-passive-nonterminal-edge-pair-staged-target-shear.md`;
- `statement-card-a2-retained-passive-nonterminal-edge-pair-staged-target-shear.md`.

## First Review

The first xhigh read-only review failed the initial Lean statement because the
public theorem used a staged input identified only with the derivative of the
successor extended `F2` coordinate, while the reproduction and statement card
claimed the staged input was the source tangent `v.F2_(p.succ)`.

The issue was conceptual, not a Lean elaboration failure: the missing bridge was
the projection derivative from the extended nonterminal successor slot to the
stored successor source coordinate, with the dependent-index cast between
`p.succ.castSucc` and `p.castSucc.succ`.

## Repair Checked

Lean now proves
`fderiv_retainedPassive_toCoordinateData_F2_nonterminal_succ_apply`, identifying
the Frechet derivative of

```text
(ofTopologyTuple y).toCoordinateData.F2 p.castSucc.succ
```

with

```text
cast_{p.succ.castSucc = p.castSucc.succ}(v.2.1 p.succ).
```

The source-staged public theorems then use that casted source tangent as
`Xsucc`:

```text
F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F2
F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_C
```

The derivative-staged theorems remain only as bridge lemmas.

## Re-Review Verdict

Xhigh reviewer `Pascal` passed the repaired slice.

Checks:

- The projection derivative unfolds the `Fin.snoc` zero-extension at the
  nonterminal `castSucc` slot and returns the stored successor source tangent,
  transported by the dependent-index cast.
- The source-staged theorems state only the one-step nonterminal claim:
  `q = p.castSucc`, `Xsucc` is the casted successor source tangent, `(U_F,U_C)`
  equals the formal edge pair, and the formal inverse recovers the current
  `F2` and `C` tangents.
- Boundary cases are correct: `M = 0` has no `p : Fin M`; the edge immediately
  before the terminal edge still uses stored successor `F2`; the terminal zero
  extended slot is handled only by the separate terminal theorem.
- The reproduction and statement card now match the Lean statements, including
  the dependent-index cast and the nonclaim boundary.

## Nonclaims Preserved

No full descending induction, no target-side `LinearEquiv`, no determinant
equality, no actual derivative determinant formula, no measure transport, no
normal crossings, no pole order, and no RLCT is proved by this slice.
