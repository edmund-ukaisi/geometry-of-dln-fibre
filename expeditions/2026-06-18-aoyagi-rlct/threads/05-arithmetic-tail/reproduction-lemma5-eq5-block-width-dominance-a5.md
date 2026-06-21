# Pen-and-paper reproduction - Lemma 5 equation (5) block width dominance

Status: checked conditional block-width bridge; Definition 3 alone is not
enough.

This note fills the next conditional bridge below the Eq5 source-label wrapper.
It derives the width bound

```text
W_p <= n(S+1)
```

for a point `S` in the own selected block, but only from explicit index-level
width data.  It does not claim that Aoyagi Definition 3 alone supplies this
bound.

## Source

Aoyagi Definition 3 selects width values/layers

```text
M = {M(S_j) : j=1,...,ell+1}
```

and states the dominance condition for widths whose value is not in this
selected set.  Aoyagi Lemma 5 equation `(5)` uses the own-block guard

```text
S_(j0+1)-1 <= s < S_(j0+2)-1.
```

In Lean, this guard is `C.block p S`, and the corresponding source layer is
`t=S+1`.

## Block Arithmetic

From `C.block p S`,

```text
C.point p - 1 <= S < C.point (p+1) - 1.
```

Since `C.point p` is positive, this is equivalent to the source-layer interval

```text
C.point p <= S+1 < C.point (p+1).
```

Thus a block-local width hypothesis

```text
for every selected block i and every r with
C.point i <= r < C.point(i+1),
W_i <= n(r)
```

immediately gives `W_p <= n(S+1)`.

There is also a useful equivalent interface: if the selected left endpoint
has width `W_i`,

```text
n(C.point i)=W_i,
```

and the actual widths in the block are no smaller than the left-endpoint
width,

```text
n(C.point i) <= n(r),
```

then the same block-local bound follows.

Finally, an off-selected dominance interface is valid if it is stated at the
level of layer positions: if `t` is not equal to any selected cutpoint, then
every selected width is at most `n(t)`.  In the case `S+1=C.point p`, the
bound comes from the selected-width identity; otherwise `S+1` is strictly
between adjacent selected cutpoints and hence is not any selected cutpoint.

## Why Definition 3 Alone Is Not Enough

Definition 3's non-selected condition is value-level.  It applies to a layer
whose width value is not in the selected value set.  It does not apply to an
unselected layer whose width equals some selected width.

A concrete obstruction:

```text
ell = 3
selected cutpoints: 1, 3, 5, 7
selected widths:   1, 2, 2, 2
selected sum B = 7
```

The selected strict inequalities `3*1<7` and `3*2<7` hold.  Put an unselected
layer inside block `p=2` with width `1`, the same value as selected cutpoint
`S_1`.  Then for that source index,

```text
W_2 = 2
n(S+1) = 1
```

so `W_2 <= n(S+1)` is false.  The bad layer has a selected width value, so
Definition 3's value-level non-selected dominance does not apply to it.

## Lean Targets

```text
AoyagiSelectedCutpoints.block_sourceLayer_mem_Ico
AoyagiSelectedCutpoints.block_sourceLayer_eq_left_or_between
AoyagiSelectedCutpoints.point_ne_of_between_adjacent
AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block
AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block_of_leftEndpoint_min
AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block_of_offSelected
AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block_of_offSelected_lt
aoyagiLemma5Eq5_ownBlock_actualWidthLabel_of_lastPoint_blockWidth
aoyagiLemma5Eq5_ownBlock_actualWidthLabel_of_lastPoint_leftMin
aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_offSelected
aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_offSelected_lt
```

## Nonclaims

- No derivation of block-local width dominance from Definition 3 alone.
- No no-duplicate selected-width-value assumption.
- No construction or existence proof for equation `(5)`'s displayed vector.
- No terminal `tilde t=0`.
- No vector admissibility or source-vector-to-chain correspondence.
- No Case 1(2) chart sequence.
- No Lemma 5 order count, pole order, normal crossings, or RLCT extraction.
