# Review - A2 p.13 source regular-suspension boundary

Date: 2026-06-24.

Reviewer: xhigh `Gibbs the 4th`.

Verdict: accepted.

## Checked Artifacts

- `reproduction-a2-p13-source-regular-suspension-boundary.md`
- `statement-card-a2-p13-source-regular-suspension-boundary.md`

## Verdict

The boundary is source-faithful and non-overclaiming.

The key checks pass:

- the p. 13 lower-right block is treated as `prod_s C^(s) - F3 F2`, not as
  the residual `prod_s C^(s)` itself;
- the p. 13 RLCT shift is marked as a source assertion, not a Lean-ready
  analytic construction;
- the p. 14 `r(s)=r` residual reduction is separated as depending on Theorem
  4, not Theorem 3 alone;
- the Lean boundary in `RegularSuspensionCoordinates.lean` matches the safe
  target: existential fixed-base source data plus the factor-`2` comparison on
  `nhdsWithin` of the source-rank stratum;
- `RegularSuspensionInterface.lean` remains correctly supplied/conditional for
  the actual regular-suspension chart, ideal transport, coverage, Jacobian, and
  extraction obligations.

## Required Edits

None.

## Lean Target

The proposed Lean wrapper is acceptable provided it stays exactly at the
source-data plus source-stratum factor-`2` literal/cleaned square-sum boundary.
It must not mention RLCT equality, full chart construction, normal crossings,
Jacobian/prior shift, or Theorem 4 reduction as proved.
