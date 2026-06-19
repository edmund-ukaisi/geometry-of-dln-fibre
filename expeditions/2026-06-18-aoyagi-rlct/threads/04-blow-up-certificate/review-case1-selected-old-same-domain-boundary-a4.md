# Review - A4 Case 1(1) Selected-Old Same-Domain Boundary

Reviewer: xhigh subagent `Gibbs the 3rd`.

Status: passed with no findings.

## Verdict

The checkpoint faithfully represents Case 1(1) as a same-domain selected-old
branch.  The post-data updates the selected old label `(s0,k0)` and preserves
only labels already introduced at `(S,J)`.  The resulting theorem returns
`IntroducedLabelExponentCertificates L n S J`, not a domain advanced to
`(S,J+1)`.

The source-coordinate projections keep the selected-old denominator separate
from the displayed Case 1(2) pivot.  They take an explicit scalar for the
Case 1(1) row-wise algebra and do not mention displayed pivot normalization,
`(S,J+1)`, or `Q/P`.

The numerator increment uses actual width:

```text
J1 * (n_(S+1)-J).
```

Non-selected labels are preserved only through supplied post-data fields.

## Scope Check

The Lean docstrings and reproduction note explicitly disclaim chart
construction, domain advancement, `Q/P`, atlas coverage, regularity,
Jacobians, normal crossings, RLCT extraction, and transition invariants.

Residual risk: the boundary is intentionally supplied/algebraic.  It does not
type-level identify the scalar with the actual coordinate `u_(s0,k0)` and does
not assert source-validity or chart construction.

## Reviewer Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `./scripts/sorries`
- `git diff --check`
