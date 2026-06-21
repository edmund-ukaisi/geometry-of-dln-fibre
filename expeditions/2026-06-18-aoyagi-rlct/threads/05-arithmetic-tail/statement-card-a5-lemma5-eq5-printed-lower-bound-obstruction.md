# Statement card - A5 Lemma 5 Eq5 Printed Lower-Bound Obstruction

## Lean Names

```text
aoyagiLemma5Eq5_piecewise_belowLowerCounterexample_allWidthsFour
aoyagiLemma5Eq5_piecewise_not_lowerBounded_allWidthsFour
```

## File

```text
lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
```

## Claim

For `ell=6`, `a=4`, integer `M=5`, all selected widths equal to `4`, and
equation `(5)` parameters `p=2`, `alpha=1`, any supplied equation `(5)`
piecewise certificate assigns Lean's zero-based selected coordinate `4` the
value `-1`, while the lower `Htilde` chain at that coordinate is `0`.
Consequently the supplied piecewise data is not lower bounded there.

## Inputs

- A supplied `AoyagiLemma5Eq5PiecewiseSourceVector` certificate.
- A selected cutpoint package `C`.

## Output

The theorem is a conditional obstruction:

```text
T (C.point 4 - 1) < HtildeLower(4).
```

## Boundaries

- No source-vector existence theorem.
- No source-label legality theorem.
- No claim that every Eq5 parameter choice fails.
- No Lemma 5 order-count theorem.
- No normal-crossing or RLCT extraction theorem.

## Source

Aoyagi Lemma 5 equation `(5)`, PDF p. 27, and the Lemma 4 bound requirement,
PDF p. 25.
