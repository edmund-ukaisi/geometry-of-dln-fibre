# Review - A2 source-filter adapted product-difference bound

Date: 2026-06-25.

Reviewers: xhigh API scout Volta the 5th; xhigh pen-and-paper scout Hooke the
5th; focused Lean build.

## Verdict

No blocking issues found.

## Checks

- The theorem is a filter-upward lift of the pointwise fixed-base adapted
  product-difference bound under eventual certificate and multiplier-bound
  hypotheses.
- The cleaned consequence uses the already-landed finite p. 13 half-bound
  through the generic supplied-loss handoff.
- The multiplier bound remains supplied eventually on the source-rank filter;
  no local boundedness or openness theorem is inferred.
- Constants `c >= 0` and `c*Kmul <= 1` are enough for the formal inequality.
  Later negative-power applications must separately require `c > 0`.
- `lean/scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates` passed.

## Boundary

The adapted product-difference square-sum is not the original DLN/statistical
loss.  The theorem does not prove covariance lower bounds, basis norm
equivalence, local multiplier boundedness, source-rank openness, analytic
chart construction, Jacobian/prior transport, regular-suspension theorem,
normal crossings, pole order, or RLCT extraction.
