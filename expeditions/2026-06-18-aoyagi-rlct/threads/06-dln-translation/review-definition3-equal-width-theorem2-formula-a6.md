# Review - Definition 3 equal-width Theorem 2 formula package

Date: 2026-06-26.

Reviewer: xhigh independent explorer `Hypatia the 2nd`.

## Verdict

PASS, no blocking source/math findings.

## Checked Formula

For `ell = L` and constant selected widths `m_j = w`, the selected pair sum is

```text
((L + 1) * L * w^2) / 2
```

over `Q`.  Since Aoyagi's finite lambda formula uses `pairSum / 2`, the
lambda contribution is

```text
((L + 1) * L * w^2) / 4.
```

The explicit ceiling datum is also correct: from `w = L*q+a`, `0<a<=L`, the
existing constructor gives

```text
ceilWidth = w + q + 1,
aParam = a,
```

including the divisible case by taking `a=L`.  The order formula is therefore

```text
a * (L - a) + 1.
```

## Scope Check

The reviewer recommended keeping the statement as a pure finite specialization
of `aoyagiTheorem2Lambda_fromCeilData`, not as an RLCT or pole-order theorem.
The branch-selection audit remains in force: this equal-width result should
not be generalized to arbitrary Definition 3 source-data choices without a
source-backed branch-selection theorem.

## Verification

The controller ran the repo build wrapper:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.Definition3Bridge
```

The focused build passed on 2026-06-26.
