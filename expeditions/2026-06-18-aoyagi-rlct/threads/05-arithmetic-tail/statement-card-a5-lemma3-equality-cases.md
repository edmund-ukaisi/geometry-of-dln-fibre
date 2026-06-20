# Statement card - A5 Lemma 3 equality cases

## Lean Artifact

Files:

- `lean/DLNFibre/DLN/Aoyagi/ArithmeticTail.lean`
- `lean/DLNFibre.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma3A_eq_min_iff`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma3A_eq_min_iff_source_Icc`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma3A_eq_min_iff_source_Icc_zero`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma3A_eq_min_iff_source_Icc_top`

## Statement

Lean now proves the exact equality cases for the isolated cleared integer
numerator in Aoyagi's Lemma 3 arithmetic tail.

## Proved

- If `ell != 0`, then
  `aoyagiLemma3A ell a b = a*ell*(ell-a)` iff `b=a` or `b=a-1`.
- Under `1 <= ell` and the source interval `0 <= b <= ell-1`, equality is
  equivalent to
  `(b=a and a <= ell-1) or (b=a-1 and 1 <= a)`.
- At `a=0`, the source interval leaves only `b=0`.
- At `a=ell`, the source interval leaves only `b=ell-1`.

## Assumed

- The exact equality theorem assumes `ell != 0`.
- The source-interval theorem assumes only `1 <= ell` and the interval bounds
  on `b`.

## Cited

- None in Lean.  This is elementary integer algebra.

## Deferred

- The terminal candidate set and the `\tilde t_{s,k}=0` restriction.
- Feasibility of these equality cases as Aoyagi exponent chains.
- The quadratic rewrite from terminal exponents to Lemma 3 data.
- Lemma 4, Lemma 5, pole-order counting, normal crossings, and RLCT
  extraction.

## Review

- Reproduction:
  `reproduction-lemma3-equality-cases-a5.md`.
- Review artifact:
  `review-lemma3-equality-cases-a5.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/ArithmeticTail.lean`
