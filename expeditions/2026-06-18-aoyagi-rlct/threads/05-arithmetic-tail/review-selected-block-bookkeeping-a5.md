# Review - selected-block bookkeeping

Reviewer: xhigh `Helmholtz`.

Status: passed.

## Findings

No blocking findings.

The selected-block support lemmas are source-faithful and useful.  They
formalise only the half-open interval bookkeeping Aoyagi uses in Lemma 5
equations `(3)` and `(4)`, not vector existence or coverage.

The reviewer confirmed the theorem shapes:

```text
AoyagiSelectedCutpoints.cut_strictMono
AoyagiSelectedCutpoints.point_strict_of_lt
AoyagiSelectedCutpoints.point_le_of_le
AoyagiSelectedCutpoints.block_index_unique
AoyagiSelectedCutpoints.block_leftEndpoint_iff
```

## Pitfalls Checked

- No global `StrictMono C.point` is stated, because `point` is total and
  returns `0` outside `i<ell+1`.
- Nat subtraction by `1` is used only with positivity/ordering hypotheses in
  place.
- The last selected cutpoint `point C ell - 1` is not claimed to be in a
  selected block.
- The zero-based translation is correct:
  `point C b = S_(b+1)` and `block C b S` means
  `S_(b+1)-1 <= S < S_(b+2)-1`.

## Nonclaims

- No displayed-vector construction.
- No terminal `tilde t=0`.
- No total source-layer coverage or chart-family coverage.
- No Lemma 5 order count, pole order, normal crossings, or RLCT extraction.
