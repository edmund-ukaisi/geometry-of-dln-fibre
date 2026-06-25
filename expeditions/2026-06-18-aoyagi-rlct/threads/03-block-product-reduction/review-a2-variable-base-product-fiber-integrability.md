# Review - A2 variable-base product fiber integrability

Date: 2026-06-25.

Reviewer: xhigh `Planck the 4th`.

Status: passed after low-severity wording/name fixes.

## Scope

Reviewed the new variable-base product estimates in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
```

especially:

```text
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_le_scale
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_ae_pos_of_base_lt_top
```

## Findings

Low: the reproduction note said the "remaining task" for the full
regular-variable threshold shift is proving the residual-base hypothesis.
Resolution: softened this to "a remaining finite-side input" and explicitly
kept endpoint, lower/divergence, bounded-density, chart/Jacobian, and RLCT
questions separate.

Low / naming precision: the finiteness theorem name mentioned a.e.
positivity but not the essential finite base-power lower-integral hypothesis.
Resolution: renamed the theorem to

```text
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_ae_pos_of_base_lt_top
```

No mathematical falsehood, missing hypothesis, or citation-boundary overclaim
was found.

## Soundness Notes

The absence of an `AEMeasurable a mu` hypothesis is acceptable for this
one-sided lower-integral theorem.  The proof uses Mathlib's
`lintegral_prod_le`, which has no measurability premise, rather than Tonelli
equality.

The strict positivity hypothesis `a(x)>0` a.e. is the right nondegeneracy
condition for this route: Lean's totalized `Real.rpow` and `ENNReal.ofReal`
do not faithfully represent the singular behavior at zeros in the
supercritical exponent.

The constant pullout is sound because the Japanese-bracket constant is proved
finite before applying `lintegral_mul_const'`.

## Verification

The controller reran:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionIntegrability
scripts/sorries
git diff --check
```

The focused module build passed, the sorry audit reported zero `sorry`,
`#exit`, `native_decide`, and `axiom`, and `git diff --check` was clean.

## Boundary

This is a sufficient finite-side product criterion.  It does not prove an
iff, an endpoint theorem, a lower/divergent-side theorem, the residual-base
integrability hypothesis for Aoyagi's actual residual variables,
bounded-density/prior transport, the Aoyagi p.13 analytic chart/Jacobian
construction, normal crossings, pole order, or RLCT.
