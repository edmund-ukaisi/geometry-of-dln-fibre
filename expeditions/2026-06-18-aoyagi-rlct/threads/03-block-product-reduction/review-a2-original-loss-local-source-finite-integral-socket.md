# Review - A2 original-loss local-source finite-integral socket

Date: 2026-06-25.

## Verdict

Accepted at local-source plumbing scope.

The theorem discharges exactly the adapted-to-original comparison for the
concrete square-Frobenius `lossDLN` of a chain-coordinate tuple, then delegates
to the existing local-source adapted-loss finite-integral socket.  It does not
claim that Aoyagi states this exact Lean theorem; it is a downstream
formalisation interface for the p.13 finite-integral reduction.

## Independent Audit Inputs

The Lean/API audit recommended delegating to

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_const_mul_adaptedProductDifferenceSquareSum_le_loss
```

and using the finite endpoint comparison

```text
exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_lossDLN_chainMapMatrixTuple
```

with the reverse rewrite from adapted Frobenius loss to adapted square-sum.
The landed proof follows that skeleton.

The source-fidelity audit found no source-boundary blocker provided the theorem
is presented as a plumbing specialization rather than a source-stated p.13
result.  Aoyagi p.13 supports the surrounding product-coordinate loss shape,
but this wrapper itself does not construct the chart or density transport.

## Scope Checks

- The source set `source` is supplied and only required to be measurable.
- Residual positivity and residual negative-power integrability remain
  hypotheses over `source`.
- Density nonnegativity and upper bounds remain local source-filter hypotheses.
- The product-coordinate adapted lower bound remains supplied.
- The only discharged hypothesis is the adapted-square-sum-to-`lossDLN`
  comparison, by finite endpoint basis comparison.

## Risks and Use Guidance

This theorem is not a nonvacuous chart theorem: it does not require
`x0 in source` and does not produce `source`.  If a later caller has the full
source-rank stratum plus density continuity/positivity, the radius-shrinking
source-stratum original-loss theorem is a better front end.  If the caller has
the explicit self-base multi-edge product family, the existing product-family
original-loss front ends should be preferred because they remove the separate
adapted lower-bound hypothesis.

## Nonclaims

No p.13 chart construction, source coverage, pushforward or Jacobian identity,
source-density derivation, residual monomial identity, statistical/KL loss
comparison, normal-crossing extraction, pole order, or RLCT statement is
proved.
