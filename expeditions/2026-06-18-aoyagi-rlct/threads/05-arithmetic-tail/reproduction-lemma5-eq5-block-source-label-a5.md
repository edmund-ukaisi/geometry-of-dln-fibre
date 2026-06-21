# Pen-and-paper reproduction - Lemma 5 equation (5) block source label

Status: checked conditional arbitrary-own-block wrapper.

This note extends the equation `(5)` source-label bridge from the block's left
endpoint to an arbitrary source index in the own selected block.  It does not
construct the displayed vector or prove terminal `tilde t=0`.

## Source

Aoyagi Lemma 5 equation `(5)`, PDF p. 27, has the source guard

```text
S_(j0+1)-1 <= s < S_(j0+2)-1.
```

Under the repo convention this is `C.block p s`, with paper `j0` represented
by Lean coordinate `p`.

The label relation and label bounds are those of the previous source-label
slice:

```text
k = Htilde'_p + 1 - alpha,
1 <= alpha <= Htilde'_p-Htilde_p.
```

Definition 3's selected-width hypotheses prove

```text
1 <= k <= W_p,
```

where `W_p` is `aoyagiSelectedWidthNat ell m p`.

## Arbitrary Source Index

For the block's left endpoint, `W_p` can be interpreted as the actual width at
`C.point p-1`.  For an arbitrary `s` satisfying `C.block p s`, this equality
is not automatic from the selected-cutpoint bookkeeping.  The correct
conditional theorem therefore keeps the actual-width bridge explicit:

```text
n(s+1) = W_p.
```

Together with source-layer range data

```text
1 <= s <= L,
```

the already-proved label bounds give

```text
actualWidthLabel L n s k.
```

The lower source-layer bound `1<=s` can be derived in the own-block Eq. `(5)`
setting.  The supplied certificate carries `1<=alpha` and `alpha<p`, so
`0<p`.  Since selected cutpoints are positive and strictly increasing,

```text
1 <= C.point 0 < C.point p,
```

so `2<=C.point p` and hence `1<=C.point p-1`.  The block lower bound
`C.point p-1<=s` gives `1<=s`.

The supplied equation `(5)` piecewise certificate gives an own-coordinate
branch record, and this branch record applies to every `s` in `C.block p s`.
Therefore, under the label relation,

```text
T(s) = k-1.
```

## Lean Targets

```text
aoyagiLemma5Eq5_actualWidthLabel_at_of_widthCompatibility
aoyagiLemma5Eq5_piecewise_ownCoordinate_actualWidthLabel_of_block
aoyagiLemma5Eq5_sourceIndex_pos_of_ownBlock
aoyagiLemma5Eq5_piecewise_ownCoordinate_actualWidthLabel_of_ownBlock_widthCompatibility
```

## Nonclaims

- No proof of the upper source range `s<=L`.
- No proof that `n(s+1)=W_p` holds for arbitrary `s` in the block.
- No construction or existence proof for equation `(5)`'s displayed vector.
- No terminal `tilde t=0` theorem.
- No vector admissibility or source-vector-to-chain correspondence.
- No Case 1(2) chart sequence.
- No Lemma 5 order count, pole order, normal crossings, or RLCT extraction.
