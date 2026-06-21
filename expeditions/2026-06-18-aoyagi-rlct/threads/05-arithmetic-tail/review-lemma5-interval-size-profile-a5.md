# Review - Lemma 5 interval-size profile

Reviewers: controller review; exact-diff reviewer pending.
Verdict before exact-diff return: finite arithmetic is source-faithful.

## Findings

No issue was found in the controller check.

The Lean statements reproduce the three-region cardinality profile displayed
in Aoyagi Lemma 5 using the existing definition

```text
aoyagiLemma5IntervalSize ell a j
  = 1 + min(j, ell-j, a, ell-a).
```

The combined theorem uses a boundary-inclusive conditional form.  This is
equivalent to the PDF's `min+1 <= j` and `max+1 <= j` phrasing because the
first branch has already removed `j<=min`, and the second branch has already
removed `j<=max`.

## Checks

Controller check:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean
```

passed before this note was written.

## Residual Risks

This is only interval-size arithmetic.  It does not prove displayed-vector
construction, terminal `tilde t=0`, vector admissibility, chart sequence,
normal crossings, RLCT extraction, or Lemma 5's order count.
