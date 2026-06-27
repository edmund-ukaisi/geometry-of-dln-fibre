# Review - A2 Retained-Passive Ctop Tail Endpoint Substitution

Date: 2026-06-27.

Reviewer: xhigh `Galileo`.

Verdict: PASS.

## Scope Reviewed

Lean:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Theorems:

```text
Ctop_tail_zero_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
Ctop_tail_pos_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

Reproduction and statement card:

```text
reproduction-a2-retained-passive-ctop-tail-endpoint-substitution.md
statement-card-a2-retained-passive-ctop-tail-endpoint-substitution.md
```

## Findings

No blocking findings.

The sign is correct: the existing bridge already converted the inverse-tail
term from `-dTailInv * coord.Ctop` to
`+ Tail⁻¹ * dTail * Tail⁻¹ * coord.Ctop`.  The positive theorem preserves the
noncommutative order, keeping the substituted derivative between the two
`Tail⁻¹` factors:

```text
d(Psucc) * data.A1seed p + Psucc z * v.1 q.
```

The `M=0` theorem is correctly specialized to the empty tail and drops only
the tail correction term.  The positive theorem uses
`fderiv_retainedPassive_A1TailAfterFirst_pos_apply`, with
`q = ⟨0,hM⟩`, `p=q.succ`, and `Psucc` starting at `p.succ`; no dummy
`A1seed 0` is included.

The determinant-chart hypothesis is retained only because the upstream
Ctop/inverse-tail bridge requires it.  The endpoint derivative lemmas
themselves are not strengthened with extra chart hypotheses.  The
documentation keeps the nonclaim boundary: no closed finite-sum formula, no
determinant equality, no measure transport, no normal crossings, no pole
order, and no RLCT.

## Reviewer Build Note

The reviewer ran the focused Lean file, `git diff --check`, a named-file
forbidden-token scan, and the two theorem axiom audits.  The controller also
ran the focused/full builds, full `scripts/sorries`, `git diff --check`, and
axiom audit for this slice.
