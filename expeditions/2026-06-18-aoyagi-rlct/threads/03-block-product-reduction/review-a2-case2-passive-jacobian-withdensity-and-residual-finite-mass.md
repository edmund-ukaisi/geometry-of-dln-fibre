# Review - A2 Case 2 Passive Jacobian WithDensity and Residual Finite-Mass

Date: 2026-06-29.

Reviewer: Aristotle the 3rd, xhigh read-only review.

Status: PASS.

## Scope

The reviewer checked the new Lean claims:

```text
withDensity_ofReal_sandwich_of_ae_bounds
exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive_passiveProductMeasure
residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_finiteMass
```

## Verdict

No findings.

The generic `withDensity` lemma is exactly the monotonicity statement it
claims: it rewrites constant densities with `withDensity_const` and applies
`withDensity_mono` to the two a.e. `ENNReal.ofReal` bounds.

The specialized sandwich theorem obtains the existing local a.e. bounds,
splits them, and applies the generic `withDensity` lemma.  The reviewer found
no hidden source-prior transport, determinant-chart Haar transport, source-
image coverage, normal-crossing, pole-order, or RLCT content.

The finite-passive-mass residual theorem is scoped correctly: finite passive
mass is explicit and is used to make the scaled target integral finite.  It
remains a residual marginal/integrability statement.

## Verification

The reviewer also reported:

```text
direct Lean elaboration of RetainedPassiveCase2LocalJacobianMeasure.lean passed
git diff --check passed
no sorry/axiom/native_decide/#exit found in the two touched files
```

The controller separately ran the focused `scripts/lb` build, `git diff
--check`, `scripts/sorries`, and direct axiom probes for the three new
constants.

