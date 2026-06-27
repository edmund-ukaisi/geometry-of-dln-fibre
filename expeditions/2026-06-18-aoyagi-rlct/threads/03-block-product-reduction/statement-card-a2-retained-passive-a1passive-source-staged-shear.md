# Statement Card - A2 Retained-Passive A1 Passive Source-Staged Shear

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

## Lean Names

```text
retainedPassiveSourceStagedSuccessorA3
retainedPassiveSourceStagedSuccessorA3_castSucc
retainedPassiveSourceStagedSuccessorA3_last
fderiv_retainedPassive_toCoordinateData_solvedA3_castSucc_apply
fderiv_retainedPassive_toCoordinateData_F2_succ_apply
retainedPassive_F2_succ_mul_fderiv_solvedA3_eq_sourceStagedSuccessorA3
A1passive_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

## Reproduction

```text
reproduction-a2-retained-passive-a1passive-source-staged-shear.md
```

## Claim

For a retained-passive determinant-chart point `z`, tangent `v`, and passive
top-left index `p : Fin M`, the actual raw-order derivative's passive `A1`
component agrees with the point-specialized formal raw-order Jacobian after
replacing the two source-side derivative terms in the old passive `A1` bridge by
explicit staged source tangents:

```text
Dzv.A1passive_p
  - X_F(p.succ) * coord.solvedA3_{p.succ}
  - coord.F2_{p.succ.succ} * X_G(p.succ)
= formal(z)(v).A1passive_p.
```

Here `X_F` is the already-landed staged successor `F2` family, and `X_G` is the
new staged successor lower-left family: stored `A3passive` tangents on
nonterminal indices and zero at the terminal index.

## Proof Plan

1. Prove the nonterminal projection derivative
   `d(solvedA3_{r.castSucc})_z(v) = v.A3passive_r`.
2. Prove the all-edge successor `F2` derivative readout using the existing
   nonterminal and terminal `F2` projection lemmas.
3. Prove the all-edge multiplier identity
   `coord.F2_{q.succ} * d(solvedA3_q)_z(v) =
    coord.F2_{q.succ} * X_G(q)`.
   The terminal case is valid only because the extended `coord.F2` has terminal value
   zero.
4. Rewrite the old passive `A1` component bridge with these two readouts.

## Review

```text
review-a2-retained-passive-a1passive-source-staged-shear.md
```

## Status

Implemented in Lean.  Focused and full builds passed.  `scripts/sorries` and
`git diff --check` passed.  The new Lean theorems depend only on
`[propext, Classical.choice, Quot.sound]`.  Independent xhigh boundary review
passed.

## Nonclaims

This is not a fully source-staged tuple and not a determinant argument.  It
does not stage `Ctop` or `F3`; those branches still carry derivative-stage
corrections.
