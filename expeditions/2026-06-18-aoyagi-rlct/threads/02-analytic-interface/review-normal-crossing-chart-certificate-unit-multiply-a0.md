# Review - Chart-certificate unit multiplication

Date: 2026-06-23.

Reviewer: xhigh Lean/API reviewer `Epicurus`.

## Verdict

Accepted after documentation fixes.  The Lean/API review found no soundness
issue in the certificate operation.

## Lean/API Check

The new Lean operation

```text
AoyagiNormalCrossingChartCertificate.unitMultiply
```

requires supplied unit witnesses for both chartwise multipliers, absorbs them
into the recorded loss and Jacobian/prior unit fields using `IsUnit.mul`, and
leaves `lossExp` and `jacobianPriorExp` definitionally unchanged.

The projection theorem

```text
AoyagiNormalCrossingChartCertificate.exponentData_unitMultiply
```

is `rfl`, so the finite minimum and order preservation lemmas are exactly
rewrites along unchanged exponent data.

## Required Fixes Applied

The review flagged three documentation issues:

- the review artifact was referenced before it existed;
- the reproduction note still said the Lean implementation was pending;
- the monomial wording overstated the Lean API by saying coordinate monomial
  factors were excluded syntactically.

The controller fixed these by adding this review card, marking the reproduction
as formalised, and replacing the monomial wording with the precise condition:
divisor monomial shifts are outside the intended use of `unitMultiply` unless
the caller separately supplies unit witnesses; exponent-changing monomial
shifts belong to APIs such as `jacobianPriorLossShift`.

## Nonclaims

This review accepts only certificate algebra on supplied chart data.  It does
not accept chart construction, chart coverage, analytic unit neighbourhoods, a
Jacobian/volume-form theorem, global normal crossings, pole order, RLCT
extraction, or extraction transfer from a reduced certificate.
