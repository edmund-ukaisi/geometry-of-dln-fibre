# Pen-and-paper reproduction - A4 Case 2 displayed frontier branch

Status: reproduced and formalised the finite frontier branch arithmetic after
Aoyagi's displayed Case 2 pivot.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  The displayed chart selects the top-left
residual-block entry `(J+1,J+1)`.  After this pivot, the continuing lower-right
residual block has rows strictly after `J+1` in the current prefix range and
columns strictly after `J+1` in the next actual-width range.

This note uses the corrected certificate convention already isolated in Lean:
actual widths `n(S+1)` stay separate from prefix minima `prefixMinNat n S`.

## Reproduction

Write

```text
muS     = prefixMinNat n S,
w       = n(S+1),
muNext  = prefixMinNat n (S+1).
```

For `1 <= S`, the prefix recurrence gives

```text
muNext = min(muS,w).
```

The displayed pivot is valid under

```text
J+1 <= muNext.
```

After pivoting at `(J+1,J+1)`, the post-pivot lower-right domain is

```text
rows    J+2..muS,
columns J+2..w.
```

This entry set is nonempty exactly when

```text
J+2 <= muNext.
```

If this next-continuation bound fails while the displayed pivot was valid, then

```text
muNext = J+1.
```

Since `muNext = min(muS,w)`, at least one of the two stopped-side equalities
holds:

```text
muS = J+1
```

or

```text
w = J+1.
```

These alternatives are not mutually exclusive.  If `w=J+1`, the post-pivot
column complement is empty and the top row of `Q^-1 C` is the original source
row.  If `muS=J+1`, the current-prefix row side is exhausted, but the surviving
pivot row remains the transported top row of `Q^-1 C`; it need not be an
original source row unless actual-width exhaustion also holds.

## Lean Shape

Lean adds a supplied branch witness:

```text
Case2DisplayedStepBranch n S J
```

with constructors:

```text
continuing          : J+2 <= prefixMinNat n (S+1)
actualWidthStopped  : n(S+1) = J+1
rowExhaustedStopped : prefixMinNat n S = J+1
```

The finite arithmetic cover is:

```text
case2DisplayedFrontier_next_or_actualWidth_or_rowExhausted_of_cont
```

The displayed supplied boundary projection is:

```text
Case2DisplayedSuppliedChartFamilyBoundary.frontierBranch
```

## Proved

- Under displayed pivot validity, either the next same-stage residual center is
  nonempty or an actual-width/current-prefix stopped equality holds.
- A displayed supplied boundary carries this finite branch witness through its
  existing `stage_pos` and `continuation` fields.

## Assumed

- The displayed pivot validity hypothesis `J+1 <= prefixMinNat n (S+1)`.
- For the boundary projection, the existing supplied displayed boundary data.

## Not Claimed

- No mutual exclusivity of stopped alternatives.
- No chart or atlas result.
- No source-produced recurrence or exponent post-data.
- No successor chart-family boundary.
- No original-row claim in the row-exhausted wide-next branch.
- No Jacobian, normal-crossing, pole-order, or RLCT statement.
- No repair of Aoyagi's printed Case 2 vector mismatch.
