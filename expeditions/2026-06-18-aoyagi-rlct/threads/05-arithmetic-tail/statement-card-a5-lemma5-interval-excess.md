# Statement card - A5 Lemma 5 interval-excess arithmetic

## Lean Artifact

Files:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean`
- `lean/DLNFibre.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5IntervalExcess`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5IntervalSize`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5IntervalExcessFiber`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5IntervalExcessFiber_eq_Ico_card`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5IntervalExcessFiber_eq_excess`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5IntervalExcessFiber_sum_range`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5IntervalExcess_sum_range`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5IntervalExcess_zero`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5IntervalExcess_top`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5_range_succ_eq_insert_endpoints_Icc`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5IntervalExcess_sum_Icc`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5IntervalSize_excess_sum_Icc`

## Statement

Lean now proves the elementary interval-excess sum used in Aoyagi's Lemma 5:

```text
1 + sum_{j=1}^{ell-1} (intervalSize(ell,a,j)-1)
  = a(ell-a)+1.
```

## Proved

- The closed excess formula is
  `min j (min (ell-j) (min a (ell-a)))`.
- This closed formula equals a rectangle-fiber count for the level map
  `(p,q) |-> p+q+1` on `range a x range (ell-a)`.
- Summing the excesses over all levels counts the rectangle:
  `a*(ell-a)`.
- Under `1 <= ell` and `a <= ell`, the same excess sum over
  `j in Icc 1 (ell-1)` is `a*(ell-a)`.
- Therefore one baseline contribution plus these excesses is
  `a*(ell-a)+1`.

## Assumed

- For the source-facing `Icc 1 (ell-1)` theorem: `1 <= ell` and `a <= ell`.

## Cited

- None in Lean.  This is finite arithmetic.

## Deferred

- Lemma 5's chart-family admissibility and coverage.
- The displayed vector constructions and exclusions on PDF pp. 26-27.
- The pole-order interpretation, normal crossings, and RLCT extraction.

## Review

- Reproduction:
  `reproduction-lemma5-interval-excess-a5.md`.
- Review artifact:
  `review-lemma5-interval-excess-a5.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean`
