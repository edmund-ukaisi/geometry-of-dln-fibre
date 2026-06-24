# Review - A2 null-origin radial integrability

Date: 2026-06-24.

Reviewer: xhigh `Jason the 4th`.

Scope:

- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`;
- `reproduction-a2-null-origin-radial-integrability.md`;
- `statement-card-a2-null-origin-radial-integrability.md`;
- relevant expedition ledger updates.

## Verdict

PASS after bookkeeping fixes.

The first review verdict was FAIL only because this review artifact was already
referenced before the file existed, and because one reproduction sentence could
be sharper about the nonpunctured representative's value at the origin.  Both
issues were fixed before commit.

## Findings

1. Missing review artifact referenced as present.

Resolution: this file records the xhigh review.

2. Minor wording risk in the reproduction note around the origin.

The original text could suggest that indicator-extension by zero itself made
the origin analytically harmless.  It now says that the nonpunctured `Iio` and
ball representatives include the origin and rely on Lean's total point value
there, while the theorem transfers by a.e. equality and integrability ignores
changes on null sets.

## Audit

The Lean theorem statements are honest and scoped correctly.  The origin is
handled by `[NoAtoms mu]` and `Measure.ae_ne`, not by a hidden regularity claim.
The quadratic corollaries keep the strict hypothesis `2*s < finrank` and use
`Iio`/`Metric.ball`, not closed balls or endpoint/boundary assertions.

No silent citation to Aoyagi Lemma 1, Aoyagi Theorem 4,
regular-coordinate/Fubini additivity, normal-crossing production, pole order,
or RLCT extraction was found.

## Verification

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
scripts/sorries DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
git diff --check
```

The Lean target passed.  The scanner reported `0 sorry, 0 #exit`,
`0 native_decide`, and `0 axiom`.  The diff check passed.

## Nonclaims Confirmed

- No pointwise regularity at the origin.
- No closed-ball theorem or boundary-sphere nullity.
- No endpoint theorem.
- No lower/divergence theorem.
- No uniform asymptotic in `a`.
- No density theorem.
- No product-coordinate `+k/2` threshold.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No normal crossings, pole order, or RLCT theorem.
