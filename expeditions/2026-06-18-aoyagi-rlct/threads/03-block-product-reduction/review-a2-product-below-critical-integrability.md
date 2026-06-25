# Review - A2 product below-critical integrability

Date: 2026-06-24.

Reviewer: xhigh `Hypatia the 4th`.

Scope:

- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`;
- `reproduction-a2-product-below-critical-integrability.md`;
- `statement-card-a2-product-below-critical-integrability.md`;
- relevant expedition ledger updates.

## Verdict

PASS after bookkeeping fix.

The review found no Lean or mathematical blocker.  The only commit-readiness
failure was that the expedition ledgers already referenced this review artifact
before it existed.  This file is the bookkeeping fix.

## Findings

1. Missing review artifact referenced as present.

Resolution: this file records the xhigh review.

## Audit

The Lean theorem is scoped correctly: finite base measure, additive Haar
regular factor, a.e. nonnegative `a`, `R > 0`, `s >= 0`, strict
`2*s < finrank`, and open-ball support.

The origin issue is handled by excluding `u = 0` almost everywhere using
`Measure.ae_ne` on the Haar regular factor.  The proof does not assert a
pointwise inequality at the regular origin.

No measurability hypothesis on `a` is hidden.  The proof uses only a.e.
domination by a measurable majorant depending on the regular variable.

The product-measure order is correct: the majorant is a function of the second
coordinate, and `lintegral_prod_mul` factors it as `mu univ` times the regular
factor integral.

The reproduction note, statement card, and ledgers match the Lean theorem and
explicitly exclude the threshold-shift, endpoint, divergence, asymptotic,
density/prior, p.13 chart/Jacobian, normal-crossing, pole-order, and RLCT
claims.

No silent citation to Aoyagi Lemma 1, Aoyagi Theorem 4,
regular-coordinate/Fubini additivity, normal-crossing production, pole order,
or RLCT extraction was found.

## Verification

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
```

The target passed.  The reviewer also checked that no `sorry`, `admit`,
`axiom`, or `unsafe` appears in the target Lean file.

## Nonclaims Confirmed

- No regular-variable `+ dim(E)/2` threshold shift.
- No theorem for `s >= dim(E)/2`.
- No endpoint theorem.
- No lower/divergence theorem.
- No uniform asymptotic in `a`.
- No bounded-density/prior theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No normal crossings, pole order, or RLCT theorem.
