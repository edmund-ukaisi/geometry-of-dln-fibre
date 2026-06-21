# Pen-and-paper reproduction - Lemma 5 equation (5) source range and width bound

Status: checked conditional source-range and width-bound wrapper.

This note refines the equation `(5)` own-block source-label bridge.  It does
not construct the displayed vector, prove actual-width dominance from
Definition 3, or prove terminal `tilde t=0`.

## Source

Aoyagi Definition 3 selects layer indices

```text
S_1 < ... < S_(ell+1)
```

inside the layer-index range.  In the Lean cutpoint API this is represented by
`C.point 0,...,C.point ell`, and the source-shaped range compatibility is

```text
C.point ell <= L+1.
```

Aoyagi Lemma 5 equation `(5)`, PDF p. 27, uses the own-block condition

```text
S_(j0+1)-1 <= s < S_(j0+2)-1.
```

In Lean this is `C.block p S`.

## Source Range

The selected-block API already proves that any block member lies in the
half-open selected span:

```text
C.point 0 - 1 <= S < C.point ell - 1.
```

Therefore, if the last selected cutpoint is source-compatible,

```text
C.point ell <= L+1,
```

then `C.point ell - 1 <= L`, because `C.point ell` is positive.  The strict
selected-span upper bound gives

```text
S <= L.
```

Together with the previous Eq5 own-block positivity argument from
`1<=alpha<p`, this supplies both source-range halves of `actualWidthLabel`.

## Width Bound

The existing label arithmetic proves

```text
1 <= k <= W_p,
```

where

```text
k = Htilde'_p + 1 - alpha.
```

For `actualWidthLabel L n S k`, equality `n(S+1)=W_p` is stronger than needed.
It is enough to assume the lower bound

```text
W_p <= n(S+1).
```

Then

```text
k <= W_p <= n(S+1).
```

The supplied Eq5 piecewise certificate gives the own-block value

```text
T(S)=Htilde'_p-alpha=k-1.
```

Thus the source-facing wrapper proves both `T(S)=k-1` and
`actualWidthLabel L n S k` from:

```text
C.block p S,
C.point ell <= L+1,
W_p <= n(S+1).
```

## Lean Targets

```text
AoyagiSelectedCutpoints.selectedSpan_sourceIndex_le_of_terminalEndpoint_le
AoyagiSelectedCutpoints.selectedSpan_sourceIndex_le_of_lastPoint_le
AoyagiSelectedCutpoints.block_sourceIndex_le_of_terminalEndpoint_le
AoyagiSelectedCutpoints.block_sourceIndex_le_of_lastPoint_le
aoyagiLemma5Eq5_actualWidthLabel_at_of_widthBound
aoyagiLemma5Eq5_piecewise_block_actualWidthLabel_of_widthBound
aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_widthBound
aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthCompatibility
aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthBound
```

## Nonclaims

- No construction or existence proof for equation `(5)`'s displayed vector.
- No proof that Definition 3 alone gives `W_p <= n(S+1)` for every own-block
  point.
- No terminal `tilde t=0`.
- No vector admissibility or source-vector-to-chain correspondence.
- No Case 1(2) chart sequence.
- No Lemma 5 order count, pole order, normal crossings, or RLCT extraction.
