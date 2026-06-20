# Statement card - A5 Lemma 3 equality count

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/ArithmeticTail.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma3AMinimizerSet`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma3AMinimizerSet_eq_zero`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma3AMinimizerSet_eq_top`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma3AMinimizerSet_eq_interior`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma3AMinimizerSet_card_zero`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma3AMinimizerSet_card_top`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma3AMinimizerSet_card_interior`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma3AMinimizerSet_card`

## Statement

Lean now counts the integer `b` values in the source interval
`0 <= b <= ell-1` that attain the isolated Lemma 3 numerator lower bound.

## Proved

- The finite equality set is `{0}` at `a=0`.
- The finite equality set is `{ell-1}` at `a=ell`.
- In the strict interior `0<a<ell`, the finite equality set is `{a-1,a}`.
- Under `1 <= ell` and `0 <= a <= ell`, the cardinality is
  `1 + if 0 < a and a < ell then 1 else 0`.

## Assumed

- Integer hypotheses only: `1 <= ell` and, for the combined count theorem,
  `0 <= a <= ell`.

## Cited

- None in Lean.  This is finite integer arithmetic.

## Deferred

- The terminal candidate set and the `\tilde t_{s,k}=0` restriction.
- Feasibility of the counted values as exponent chains.
- Lemma 5's chart-family and order-count construction.
- Pole-order counting, normal crossings, and RLCT extraction.

## Review

- Reproduction:
  `reproduction-lemma3-equality-count-a5.md`.
- Review artifact:
  `review-lemma3-equality-count-a5.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/ArithmeticTail.lean`
