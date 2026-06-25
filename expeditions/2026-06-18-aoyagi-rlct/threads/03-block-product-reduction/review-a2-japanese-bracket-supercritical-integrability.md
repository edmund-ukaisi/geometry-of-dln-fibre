# Review - A2 Japanese-bracket supercritical integrability

Date: 2026-06-25.

Reviewer: xhigh `Pauli the 4th`.

Scope:

- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`;
- `reproduction-a2-japanese-bracket-supercritical-integrability.md`;
- `statement-card-a2-japanese-bracket-supercritical-integrability.md`;
- relevant expedition ledger updates.

## Verdict

PASS.

No blocking findings.

## Audit

The Lean theorem names and scope are correct:

```text
DLNFibre.DLN.Aoyagi.integrable_one_add_norm_sq_rpow_neg
DLNFibre.DLN.Aoyagi.lintegral_ofReal_one_add_norm_sq_rpow_neg_lt_top
DLNFibre.DLN.Aoyagi.lintegral_ofReal_norm_sq_add_pos_rpow_neg_lt_top
```

The Lean slice proves only the Japanese-bracket model and fixed `a > 0`
lower-integral finiteness.  It does not prove sharp `a^(finrank/2-s)`
dependence, a base-product theorem, the regular-variable threshold shift, pole
order, or RLCT.

The reproduction, statement card, theorem ledger, synthesis, priorities, and
thread log match that boundary and explicitly exclude the stronger analytic
claims.

No silent citation to Aoyagi Lemma 1, Aoyagi Theorem 4,
regular-coordinate/Fubini additivity, normal-crossing production, pole order,
or RLCT extraction was found.

## Verification

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
```

It passed.  The reviewer also checked that no `sorry`, `axiom`,
`native_decide`, or `#exit` appears in the touched Lean file.

Controller verification also passed:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionIntegrability
scripts/sorries
git diff --check
```

## Nonclaims Confirmed

- No sharp `a^(finrank/2-s)` bound.
- No product theorem with a base function `a(y)` approaching zero.
- No regular-variable `+ dim(E)/2` threshold shift.
- No endpoint theorem.
- No lower/divergence theorem.
- No uniform asymptotic in `a`.
- No bounded-density/prior theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No normal crossings, pole order, or RLCT theorem.
