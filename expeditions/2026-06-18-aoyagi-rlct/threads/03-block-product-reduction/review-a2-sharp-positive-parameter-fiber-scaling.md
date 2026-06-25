# Review - A2 sharp positive-parameter fiber scaling

Date: 2026-06-25.

Reviewer: xhigh `Socrates the 4th`.

Status: passed after low-severity wording/name fixes.

## Scope

Reviewed the new Haar scaling and fixed positive-parameter fiber estimates in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
```

especially:

```text
lintegral_comp_inv_smul_eq_mul_addHaar
ofReal_add_norm_sq_pos_rpow_neg_eq_mul_one_add_norm_sq_inv_sqrt_smul
lintegral_ofReal_add_norm_sq_pos_rpow_neg_eq_scale
lintegral_ofReal_add_norm_sq_pos_rpow_neg_indicator_ball_le_scale
lintegral_ofReal_add_norm_sq_pos_rpow_neg_indicator_ball_lt_top_of_supercritical
```

## Findings

Low: the first docstring for the whole-space scaling theorem described the
identity as "supercritical", although the theorem only assumes `a>0` and is
valid for all real `s`.  Resolution: changed the docstring to state that it is
a positive-parameter scaling identity and that supercriticality enters only in
later finiteness applications.

Low / naming precision: the new theorem names used `norm_sq_add_pos` while
the displayed model is syntactically `a + ||x||^2`.  Resolution: renamed the
new declarations to use `add_norm_sq_pos`, matching the displayed model and
the surrounding product-coordinate naming convention.  The older pre-existing
fixed-parameter finiteness theorem was not renamed in this slice.

No mathematical falsehood, missing hypothesis, or citation-boundary overclaim
was found.  The reviewer checked the Haar factor for `x -> r^(-1) x` and the
resulting exponent `a^(finrank/2-s)`.

## Verification

After the fixes, the controller reran:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionIntegrability
scripts/sorries
git diff --check
```

The focused module build passed, the sorry audit reported zero `sorry`,
`#exit`, `native_decide`, and `axiom`, and `git diff --check` was clean.

## Boundary

The review confirms this slice remains fixed-positive-parameter fiber
scaling.  It does not prove the variable-base product theorem, residual-base
integrability of `a(x)^(finrank/2-s)`, a full regular-variable threshold
shift, endpoint or divergent-side results, bounded-density/prior transport,
the Aoyagi p.13 analytic chart/Jacobian construction, normal crossings, pole
order, or RLCT.
