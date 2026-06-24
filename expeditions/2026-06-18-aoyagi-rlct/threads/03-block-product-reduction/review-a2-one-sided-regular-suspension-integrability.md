# Review - A2 one-sided regular-suspension integrability

Date: 2026-06-24.

Reviewer: xhigh subagent Copernicus the 4th.

## Verdict

Pass.  No issues found in the scoped patch.

## Scope Reviewed

- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`
- `lean/DLNFibre.lean`
- `reproduction-a2-one-sided-regular-suspension-integrability.md`
- `statement-card-a2-one-sided-regular-suspension-integrability.md`

## Findings

None.

## Notes

The Lean statements are narrow and mathematically correct.  The pointwise
comparison is exactly ENNReal monotonicity plus inverse order reversal.  The
finite-factor theorem concludes only finiteness of the product integral from a
finite base integral and finite extra measure.  The restricted version is the
same theorem applied to restricted measures, with finiteness from
`nu t < infinity`.

The proof does not hide an RLCT, threshold, or additivity claim.  The only
product-measure step is the explicit separable upper-bound factorization via
`lintegral_prod_mul`, followed by finite-factor multiplication.

The documentation accurately states the nonclaims: no `+ k/2` threshold shift,
no regular-coordinate/Fubini additivity, no Aoyagi Lemma 1 or Theorem 4, and
no normal-crossing-to-RLCT extraction.

Names and placement are appropriate for the Aoyagi-only expedition.  The new
module is grouped with the neighboring regular-suspension Aoyagi modules, and
the aggregator import is appended at the end.

## Residual Risk

This remains only the one-sided finite-factor comparison, not the radial
regular-square estimate.  Downstream use for a `+ k/2` shift still needs a
separate analytic theorem.  The finite theorem assumes `AEMeasurable a`,
rather than the weaker measurability of `fun x => a x ^ (-s)`; this is
conservative, not unsound.
