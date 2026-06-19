# Review - A4 Case 1(1) Selected-Old Lowered Recurrence Boundary

Reviewer: xhigh subagent `Raman the 3rd`.

Status: passed with no findings.

## Verdict

The checkpoint keeps the recurrence boundary supplied.  The pre/post
recurrence states both live over the same introduced-label domain `(S,J)`, and
the only recurrence bridge fields are:

```text
pre.step  = mulStepAt(baseStep,u,J+J1),
post.step = mulStepAt(baseStep,u,J).
```

There is no derivation of `baseStep` from arbitrary source recurrence data.

`selectedOldPostWeight_eq_postWeight` correctly rewrites the pre/post weights
to `monomialRec pre.step` and `monomialRec post.step`, applies the supplied
step equalities, and delegates to the pure lowered-recurrence lemma.

The source-matrix projections combine the Case 1(1) row-strip source algebra
with the supplied pre/post recurrence rewrite.  The source-coordinate theorem
is only the residual-coordinate specialization.

## Scope Check

The boundary stays at `(S,J)` and does not introduce `(S,J+1)`.  It projects
the selected old label `(s0,k0)` and its level `J+J1`, rather than using the
displayed Case 1(2) pivot.

No overclaim was found: chart construction, `Q/P`, coverage, regularity,
Jacobian, normal crossings, RLCT extraction, and full transition invariance
remain outside the checkpoint.

Residual risk: the interface still assumes the supplied `baseStep`, `pre`, and
`post` recurrence data rather than proving they arise from an actual
chart/source construction.

## Reviewer Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
