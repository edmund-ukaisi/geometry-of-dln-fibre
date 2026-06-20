# Statement card - A5 Lemma 3 endpoint arithmetic

## Lean Artifact

Files:

- `lean/DLNFibre/DLN/Aoyagi/ArithmeticTail.lean`
- `lean/DLNFibre.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma3A`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma3A_eq_min_add`
- `DLNFibre.DLN.Aoyagi.int_mul_succ_nonneg`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma3A_min_le`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma3A_at_right`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma3A_at_left`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma3A_eq_min_iff`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma3A_eq_min_iff_source_Icc`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma3A_eq_min_iff_source_Icc_zero`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma3A_eq_min_iff_source_Icc_top`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma3A_isLeast_image_Icc`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma3A_isLeast_image_Icc_zero`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma3A_isLeast_image_Icc_top`

## Statement

Lean now proves the endpoint-corrected integer arithmetic behind Aoyagi's
Lemma 3 after clearing the denominator `ell^2`.

## Proved

- The numerator
  `b(ell-a)^2 + (ell-1-b)a^2 + (b(ell-a)-(ell-1-b)a)^2`
  equals
  `a*ell*(ell-a) + ell^2*(b-a)*(b-a+1)`.
- The consecutive-integer product `x(x+1)` is nonnegative over `Z`.
- Therefore `a*ell*(ell-a)` is a universal lower bound for the numerator.
- Under `1 <= ell` and `0 <= a <= ell`, this lower bound is the least value
  over all integers `b` with `0 <= b <= ell-1`.
- If `ell != 0`, equality with the lower bound occurs exactly at `b=a` or
  `b=a-1`; intersecting with `0 <= b <= ell-1` gives the endpoint-truncated
  candidates.
- The endpoints are explicit: `a=0` has least value `0` with witness `b=0`,
  and `a=ell` has least value `0` with witness `b=ell-1`.

## Assumed

- The minimum theorem assumes only integer inequalities:
  `1 <= ell`, `0 <= a`, and `a <= ell`.

## Cited

- None in Lean.  This is elementary integer algebra.

## Deferred

- The terminal candidate set and the `\tilde t_{s,k}=0` restriction.
- Feasibility of the minimizing `b` patterns as exponent chains.
- The quadratic rewrite from terminal exponents to Lemma 3 data.
- Lemma 4, Lemma 5, pole-order counting, normal crossings, and RLCT
  extraction.

## Review

- Reproduction:
  `reproduction-lemma3-endpoint-arithmetic-a5.md`.
- Review artifact:
  `review-lemma3-endpoint-arithmetic-a5.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/ArithmeticTail.lean`
