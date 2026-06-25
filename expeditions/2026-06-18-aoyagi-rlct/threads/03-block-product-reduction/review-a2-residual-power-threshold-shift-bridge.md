# Review - A2 residual-power threshold-shift bridge

Date: 2026-06-25.

Reviewer: xhigh `Ampere the 4th`.

Status: passed after low-severity docstring fix.

## Scope

Reviewed the residual-power threshold-shift wrappers in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
```

especially:

```text
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_le_residual_power_scale
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top
```

and the accompanying reproduction, statement card, and memory updates.

## Findings

Low: the docstring for the `..._le_residual_power_scale` theorem described
finite product integrability even though the theorem proves only an
inequality and does not assume the residual base integral is finite.

Resolution: changed the docstring to say that the theorem bounds the product
lower integral by the residual negative `t`-power lower integral times the
Japanese-bracket factor.  The finiteness wording remains only on the
`..._lt_top_of_residual_power_lt_top` theorem.

No high- or medium-severity issue was found.

## Soundness Notes

The theorem is the substitution

```text
s = t + finrank_R(E)/2
```

in the variable-base product theorem.  The hypothesis `0<t` gives
`finrank_R(E)/2<s`, and the base exponent rewrites as

```text
finrank_R(E)/2 - s = -t.
```

The a.e. strict positivity hypothesis is inherited correctly from the
positive-parameter fiber-scaling theorem and avoids relying on Lean's
totalized `Real.rpow` at zero.

The notes do not silently use Aoyagi Lemma 1, Aoyagi Theorem 4,
regular-coordinate additivity, threshold equality, Aoyagi residual-base
integrability, normal-crossing production, pole order, or RLCT extraction.

## Boundary

This is a finite-side bridge from a supplied residual negative-power
integrability input to a full square-suspension product integrability
conclusion.  It does not prove that Aoyagi's reduced residual coordinates
satisfy that residual input, does not cover a positive-measure zero set of
`a`, and does not prove endpoint/divergence, threshold equality,
bounded-density/prior transport, p.13 analytic chart/Jacobian construction,
normal crossings, pole order, or RLCT.
