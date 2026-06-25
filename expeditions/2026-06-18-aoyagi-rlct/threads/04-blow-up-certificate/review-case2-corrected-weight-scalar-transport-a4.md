# Review - A4 Case 2 corrected weight scalar transport

Date: 2026-06-25.

Reviewer: controller, using xhigh source scout `Zeno` and Lean/API scout
`Noether`.

## Verdict

Pass.  The Lean theorem matches the algebra forced by Aoyagi's own p. 20
weight convention and avoids the apparent extra scalar in the p. 21 display.

## Checks

- Source locality: the theorem uses only the Case 2 displayed chart on PDF
  pp. 19-21.
- Scalar accounting: `D_J = u N` and `b'_i = u b_i` imply
  `diag(b) D_J = diag(b') N`; the selected scalar is already in the new
  weights.
- Row operation: the quotient hypothesis
  `u*b_i = q_i*(u*b_0)` is the exact finite condition for the `P` rows to
  clear the first column after `Q`.
- Orientation: the following factor appears as `Q * C'` on the old side and
  as `C'` on the cleared side, matching `C' = Q^-1 C`.
- Scope: the theorem is pure finite matrix algebra.  It does not produce
  source charts, coverage, successor data, normal crossings, pole order, or
  RLCT.

## Lean Check

Focused check passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
```

Full build passed:

```text
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb
```

Sorry scan passed:

```text
scripts/sorries
```
