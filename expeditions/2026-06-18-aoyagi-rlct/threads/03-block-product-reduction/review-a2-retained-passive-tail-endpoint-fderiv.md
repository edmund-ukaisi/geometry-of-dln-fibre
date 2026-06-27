# Review - A2 Retained-Passive Tail Endpoint Frechet Derivative

Date: 2026-06-27.

Reviewer: xhigh `Russell`.

Verdict: PASS.

## Scope Reviewed

Lean:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

Theorems:

```text
fderiv_retainedPassive_A1TailAfterFirst_zero_apply
fderiv_retainedPassive_A1TailAfterFirst_succ_apply
fderiv_retainedPassive_A1TailAfterFirst_pos_apply
```

Reproduction and statement card:

```text
reproduction-a2-retained-passive-tail-endpoint-fderiv.md
statement-card-a2-retained-passive-tail-endpoint-fderiv.md
```

## Findings

No blocking findings.

The zero theorem handles `M=0` as the empty tail derivative.  The successor
and positive wrappers use the first passive source index, with
`q = 0` or `q = ⟨0,hM⟩` and `p = q.succ`, and recurse from `p.castSucc` to
`p.succ` in the correct orientation.

The multiplication order is faithful to the residual-product recurrence:

```text
d(Psucc) * A_p + Psucc * v.A1passive_q.
```

The theorem does not use dummy `A1seed 0` as a tail factor and does not require
determinant-chart membership.  The documentation keeps the nonclaim boundary:
endpoint recurrence only, no closed finite-sum formula, no Jacobian
determinant theorem, no measure transport, no normal crossings, no pole order,
and no RLCT.

## Reviewer Build Note

The reviewer did not rerun Lean because the review was read-only.  The
controller ran the focused and full builds for this exact slice.
