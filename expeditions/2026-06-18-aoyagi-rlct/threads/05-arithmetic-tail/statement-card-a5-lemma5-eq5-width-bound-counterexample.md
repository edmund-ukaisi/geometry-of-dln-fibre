# Statement card - A5 Lemma 5 equation (5) width-bound counterexample

## Lean Name

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_blockWidthBound_not_forced_by_selectedWidthHypotheses_example`

## Claim

Definition 3-shaped selected-width data do not force the actual-width bound
needed for equation `(5)` source-label legality at every point of a selected
block.

There exist selected cutpoints `1,3,5,7`, selected widths `1,2,2,2`, actual
widths matching those selected widths at the selected cutpoints, and a block
member `S=5` in block `p=2`, such that:

```text
sum selected widths = 3*(3-1)+1,
3*m_i < sum selected widths for every selected i,
the value-level non-selected-width condition is satisfied,
but W_p <= n(S+1) is false.
```

The obstruction is that `n(S+1)=n(6)=1`, and `1` is already a selected width
value.  Aoyagi Definition 3's non-selected condition is value-level, so it
does not control this off-selected layer.

## Inputs

The theorem is closed and existential.  Its witness uses:

- `ell=3`, `M=3`, `a=1`;
- cutpoints `1,3,5,7`;
- selected widths `1,2,2,2`;
- actual width `n(6)=1`;
- block data `p=2`, `S=5`.

## Proves

- Selected cutpoint compatibility: `(n (C.point i.val) : Z)=m i`.
- Positive selected widths.
- Selected sum and strict selected-width inequalities.
- Value-level non-selected-width dominance.
- Failure of the Eq5 width bound:

```text
not aoyagiSelectedWidthNat 3 m p <= (n(S+1) : Z).
```

## Does Not Prove

- Any negative result about the conditional block-local dominance theorem.
- Any negative result about the index-level off-selected dominance theorem.
- Equation `(5)` displayed-vector construction or admissibility.
- Lemma 5 order count, pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi Definition 3, PDF pp. 8-9, and Lemma 5 equation `(5)`, PDF p. 27.

## Review

Paper/source scout: `Galileo the 2nd` (xhigh).
Lean/API scouts: `Dalton the 2nd`, `Hilbert the 2nd`, and `Hume the 2nd`
(xhigh).
