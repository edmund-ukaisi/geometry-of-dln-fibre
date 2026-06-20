# Statement card - A5 Htilde value-set count

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiHtildeIntervalValueSetNat`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeIntervalValueSetNat_card_of_lt`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeIntervalValueSetNat_card`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeIntervalValueSetNat_excess_sum_Icc`

## Statement

Lean now proves the source-facing finite count for same-coordinate values
between Aoyagi's displayed `Htilde` and `Htilde'` chains:

```text
1 + sum_{j=1}^{ell-1} (|I_j|-1) = a(ell-a)+1.
```

Here `I_j` is the finite set of integer values between the lower and upper
displayed chain values at coordinate `j`.

## Proved

- A Nat-indexed wrapper for the already-defined same-coordinate interval value
  set.
- In-range cardinality is Aoyagi's displayed interval size.
- Out-of-range cardinality is explicitly `0`.
- Under `1 <= ell` and `a <= ell`, the source-interval excess sum is
  `a(ell-a)`, hence the baseline-plus-excess count is `a(ell-a)+1`.

## Assumed

- The source-facing bounds `1 <= ell` and `a <= ell`.
- Only finite selected-width/chain data already present in the `Htilde`
  arithmetic module.

## Cited

- None in Lean.  This is finite arithmetic.

## Deferred

- Aoyagi Lemma 5's chart-family admissibility and coverage.
- The displayed vector constructions in equations (3) and (4).
- Pole-order interpretation, normal crossings, RLCT extraction, transition
  invariance, and repair of the printed Case 2 vector mismatch.

## Review

- Reproduction checked by xhigh `Plato the 5th`.
- Landed-patch review passed by xhigh `Goodall the 5th`:
  `review-htilde-value-set-count-a5.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
