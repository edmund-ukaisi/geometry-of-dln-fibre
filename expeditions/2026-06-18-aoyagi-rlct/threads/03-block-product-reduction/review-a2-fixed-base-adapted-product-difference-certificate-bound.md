# Review - A2 fixed-base adapted product-difference certificate bound

Date: 2026-06-25.

Reviewers: xhigh API scout Volta the 5th; xhigh pen-and-paper scout Hooke the
5th; focused Lean build.

## Verdict

No blocking issues found for the pointwise certificate-facing theorem.

## Checks

- The deterministic fields match the generic p. 13 theorem with
  `F2 = -S.B`, `F3 = lowerLeftBlock S.L`, `Ctop = S.Ctop`, and `D = S.D`.
- The fixed-base certificate supplies the same triangular identity through
  `PaperEndpointFixedBaseProductReductionCertificate.blockDiagonal`; the
  left multiplier is rewritten using
  `ChartLocalSuffixState.suffixState_L_eq_lowerUnitriangular`.
- The multiplier square-sum bound remains a supplied hypothesis.  No theorem
  here derives local boundedness from determinant-unit or unitriangular shape.
- The constants `c >= 0` and `c*Kmul <= 1` are sufficient for the algebraic
  inequality.  Strict positivity is a later requirement for negative-power
  and RLCT-facing use.
- `lean/scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates` passed
  after the Lean implementation.

## Boundary

The right-hand side is only the adapted fixed-base product-difference
square-sum `squareSum(T(x)-T0)`.  This is not `lossDLN` and not the original
statistical loss.  No covariance lower bound, basis norm equivalence, local
multiplier boundedness theorem, source-rank openness, analytic chart
construction, Jacobian/prior transport, regular-suspension theorem, normal
crossings, pole order, or RLCT extraction is proved.
