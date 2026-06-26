# Reproduction - A6 Definition 3 `L=2` branch formula rank-width removal

Date: 2026-06-26.

Status: pen-and-paper reproduction before Lean implementation.

## Source Anchor

Aoyagi Definition 3 and Theorem 2, PDF pp. 8-9, define the selected source
data and then compute the finite Theorem 2 formula from the chosen branch.  The
source audit
`source-audit-definition3-branch-selection-a6.md` records that pp. 8-9 do not
choose a canonical branch.  Therefore this slice keeps the repeated-positive
and all-source triangle branches separate.

## Calculation

The existing `L=2` branch formula packages still take the source-range
rank-width hypothesis

```text
hr : forall s, 1 <= s -> s <= 3 -> r <= H s.
```

For the concrete width packages this hypothesis is already encoded in the
integer width equalities.

If

```text
aoyagiReducedWidthInt H r s = (w : Int)
```

for a natural number `w`, then

```text
0 <= aoyagiReducedWidthInt H r s.
```

Since `aoyagiReducedWidthInt H r s = H(s) - r` in `Int`, this gives

```text
r <= H(s).
```

Thus the repeated-positive branch, which supplies natural widths `w1,w2,w3`
for the three source positions, can derive `hr` pointwise before delegating to
the already-proved repeated-positive finite formula package.

For the all-source triangle branch, the three strict inequalities

```text
2*w_i < w1+w2+w3
```

and the three integer width equalities give the all-source strict selected
inequality

```text
2 * M^(s) < sum_j M^(j)
```

for every `s=1,2,3`.  The existing theorem
`sourceRangeRankWidth_of_all_selected_strict` then derives the same pointwise
rank-width hypothesis.  The parity-specific formula packages can therefore be
called without exposing `hr`.

## Lean Shape

Add in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`:

```text
rank_le_of_aoyagiReducedWidthInt_eq_natCast
sourceRangeRankWidth_of_three_reducedWidthInt_eq_natCast
exists_consecutive_three_widths_theorem2Formula_of_triangle_odd
exists_consecutive_three_widths_theorem2Formula_of_triangle_even
exists_ell_one_theorem2Formula_of_L_eq_two_positive_repeated
```

The new formula theorems have the same branch-specific conclusions as the
existing `_rankWidth` versions, but no longer expose `hr`.

## Boundary

This is finite Definition 3/Theorem 2 arithmetic only.  It does not choose a
canonical branch, prove branch independence, construct Eq5 payloads, produce
charts, identify pole order, construct normal crossings, or extract an RLCT.
