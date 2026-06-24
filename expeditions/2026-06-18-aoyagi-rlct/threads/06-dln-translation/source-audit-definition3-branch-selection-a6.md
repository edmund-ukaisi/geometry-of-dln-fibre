# Source audit - Definition 3 branch selection

Date: 2026-06-24.

Auditor: xhigh source auditor `Einstein the 3rd`.

## Question

Do Aoyagi Definition 3 or Theorem 2, PDF pp. 8-9, contain a source-backed
tie-breaker that rules out the `L=2` branch-overlap diagnostics for
`(2,3,3)` or `(1,2,2)`?

## Verdict

No.  The PDF does not give a tie-breaker that excludes those branch overlaps.
Arbitrary quantification over Definition 3 source-data choices is therefore
unsafe for the finite Theorem 2 payload unless a separate source convention is
found.

## Source Read

Definition 3 defines the selected value set

```text
M = { M^(S_j) : j = 1,...,ell+1 }
```

and applies the nonselected clauses to source widths whose values are not in
that selected value set.  This is value-level membership, not source-position
membership.

Theorem 2 then defines its `M`, residue `a`, lambda formula, and order formula
from the already chosen `ell` and selected source data.  The local text on
pp. 8-9 does not say to choose minimal `ell`, maximal `ell`, all source
positions, distinct selected values, or any other canonical branch.

The equal-width example on p. 9 sets `ell = L` when all source widths are
equal.  Thus a proposed convention such as "selected values must be distinct"
or "choose minimal `ell`" is not supported by the printed example.

## Formal Diagnostics

The Lean diagnostics already record two concrete consequences:

- `(2,3,3)` at `L=2,r=0` admits both an `ell=1` repeated-positive package and
  an `ell=2` all-source triangle package, with finite lambda values `3` and
  `5/2`.
- `(1,2,2)` at `L=2,r=0` admits both packages, with finite lambda value `1`
  in both branches but finite order formulas `1` and `2`.

These are diagnostics about the printed finite Definition 3/Theorem 2 payload
as formalised.  They are not claims that the analytic RLCT is ambiguous.

## Controller Consequence

Final A6 statements should keep selected source data supplied, or restrict to
a source-backed branch where the selected data is produced.  Do not prove or
use a theorem that quantifies over arbitrary Definition 3 source-data choices
and concludes a branch-independent Theorem 2 finite lambda/order payload.

