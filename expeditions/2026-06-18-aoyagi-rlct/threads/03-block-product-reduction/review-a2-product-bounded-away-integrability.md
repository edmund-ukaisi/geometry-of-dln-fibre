# Review - A2 product bounded-away integrability

Date: 2026-06-25.

Reviewer: xhigh `Hilbert the 4th`.

Scope:

- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`;
- `reproduction-a2-product-bounded-away-integrability.md`;
- `statement-card-a2-product-bounded-away-integrability.md`;
- `scout-a2-regular-square-threshold-shift-lean-route.md`;
- relevant expedition ledger updates.

## Verdict

PASS.

No blocking findings.

## Audit

The Lean theorem name and scope are correct:

```text
DLNFibre.DLN.Aoyagi.lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_ae_pos_le
```

The proof is mathematically sound.  It pulls the a.e. lower bound to the
product measure, uses `epsilon <= a(x)+||u||^2` and `s>=0` to reverse the
real-power inequality, bounds by the constant-ball majorant, proves that
majorant finite using `measure_ball_lt_top` and `lintegral_indicator_const`,
and factors the product integral by `lintegral_prod_mul`.

The reproduction, statement card, priorities, synthesis, theorem ledger, and
thread log do not overclaim the `+dim/2` threshold shift.  They state that this
is only the away-from-zero/bounded-away integrability slice.  The scout file is
correctly marked as a route probe for the later threshold-shift theorem, not a
proved theorem.

No silent citation to Aoyagi Lemma 1, Aoyagi Theorem 4,
regular-coordinate/Fubini additivity, normal-crossing production, pole order,
or RLCT extraction was found.

## Verification

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
git diff --check
```

Both passed.  The reviewer also checked the fully qualified theorem name and
type with `#check`.

Controller verification also passed:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionIntegrability
scripts/sorries
git diff --check
```

## Nonclaims Confirmed

- No singular-base theorem where `a(x)` approaches zero.
- No regular-variable `+ dim(E)/2` threshold shift.
- No endpoint theorem.
- No lower/divergence theorem.
- No uniform asymptotic in `a`.
- No bounded-density/prior theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No normal crossings, pole order, or RLCT theorem.
