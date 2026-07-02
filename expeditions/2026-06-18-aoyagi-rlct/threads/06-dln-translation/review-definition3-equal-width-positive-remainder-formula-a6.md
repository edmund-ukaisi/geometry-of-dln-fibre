# Review - Equal-Width Positive-Remainder Formula Wrapper

Date: 2026-07-02.

Reviewer: xhigh read-only reviewer `Aristotle the 2nd`.

Verdict: PASS after documentation source-wording fix.

## Findings And Fix

The reviewer found no Lean/API-scope issue.  The positive-remainder
decomposition

```text
q = (w - 1) / L,
a = (w - 1) % L + 1
```

is the expected Euclidean division construction under `0 < L` and `0 < w`,
and the equal-width `_pos` theorem only wraps the existing decomposition-based
equal-width formula theorem.

The reviewer did find a documentation source-fidelity issue: Aoyagi's
equal-width example is printed as a ceiling inequality and residue formula,
not literally as `w = L*q + a`.  The reproduction and statement card were
updated to say that `w = L*q+a`, `0<a<=L` is the Lean positive-remainder
translation of the printed equal-width formulas.

## Verification At Review Time

The reviewer ran a direct elaboration check of
`DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`, which passed.  The controller
had already run warning-clean direct elaboration and a focused module build.
