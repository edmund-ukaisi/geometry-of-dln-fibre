# Review - A2 two-sided loss-density supplied comparison iff

Date: 2026-06-29.

Reviewer: xhigh `Pauli the 2nd`.

Status: PASS after precision fixes.

## Reviewed Claim

The new supplied-bound theorems compare an actual loss-density lower integral
with the coordinate-square-sum regular-suspension model under explicit local
two-sided hypotheses:

```text
cL * model <= loss <= CL * model,
dρ <= density <= Dρ.
```

The p.13 wrapper only adapts the regular-coordinate count and square-sum
notation.

## Initial Findings

The first review found no Lean proof error or constant-direction error, but it
flagged precision issues:

- the reverse helper docstring omitted the supplied `loss > 0` hypothesis;
- the reverse helper name hid that supplied loss-positivity input;
- the statement card did not list the model-iff hypotheses and constants.

## Fixes

The reverse helper was renamed to

```text
lintegral_ofReal_residual_power_lt_top_of_loss_rpow_neg_mul_density_coordinateSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_loss_pos_of_loss_le_const_mul_of_const_le_density
```

and its docstring now states supplied loss positivity.  The statement card now
lists a.e. measurability, `0<R`, residual positivity, residual boundedness,
`0<t`, `[SFinite nu]`, `[nu.IsAddHaarMeasure]`, and the comparison-constant
hypotheses.

## Final Verdict

PASS.  The reviewer confirmed the findings were resolved and that the current
diff builds with

```text
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean
```

and passes `git diff --check`.

## Nonclaims Preserved

- No proof of the supplied comparison hypotheses.
- No p.13 chart construction or coverage.
- No source-prior, Jacobian, density, or measure-transport theorem.
- No normal-crossing theorem, pole-order theorem, or RLCT extraction.
