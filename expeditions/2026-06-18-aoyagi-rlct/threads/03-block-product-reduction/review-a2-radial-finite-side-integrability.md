# Review - A2 radial finite-side integrability

Date: 2026-06-24.

Reviewer: xhigh `Volta the 4th`.

Scope:

- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`;
- `reproduction-a2-radial-finite-side-integrability.md`;
- `statement-card-a2-radial-finite-side-integrability.md`.

## Verdict

PASS.

No blocking issues.

## Findings

Minor documentation precision only:

- The reproduction and statement card used notation such as
  `1_(0,R)(||x||) * ||x||^(-t)`.  This could be read as evaluating the
  negative power at the origin.  The Lean statements use `Set.indicator`,
  hence indicator-extension by zero.  The documentation was updated to say
  this explicitly.
- The module note said the file does not prove a "polar-coordinate estimate".
  Since the file now proves a radial estimate using Mathlib's Haar-to-sphere
  theorem, the wording was changed to say that it does not prove a Euclidean
  ball polar-coordinate equality or asymptotic.

## Audit

The Lean statements are scoped correctly: punctured `Set.Ioo 0 R`, hypotheses
`a >= 0`, `s >= 0`, strict `2*s < finrank`, and only `Integrable` plus
`ENNReal.ofReal` finite-lintegral handoff.

The proof does not hide origin, sign, endpoint, or Haar-measure issues.  The
origin is excluded by the indicator; positivity of `r^2+a` is derived on
`0 < ||x||`; the exponent comparison uses `s >= 0`; the endpoint is strict;
and the Haar measure step goes through Mathlib's
`integrable_fun_norm_addHaar`, not through an unstated Aoyagi/Fubini/additivity
citation.

The reproduction and statement card are accurate relative to the Lean theorem
names and hypotheses after the wording fixes above.

No silent citation to Aoyagi Lemma 1, Aoyagi Theorem 4, regular-coordinate
additivity, or RLCT extraction was found.

## Verification

The reviewer ran:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionIntegrability
```

and it passed.  The reviewer also checked that no `sorry`, `axiom`,
`native_decide`, or `#exit` appears in the target Lean file.

## Nonclaims Confirmed

- No ball/null-origin transfer.
- No endpoint theorem.
- No lower/divergence theorem.
- No uniform asymptotic in `a`.
- No density theorem.
- No product-coordinate `+k/2` threshold.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No normal crossings, pole order, or RLCT theorem.
