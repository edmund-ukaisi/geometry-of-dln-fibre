1. **Q1 verdict: FALSE in general.**

Fact from definitions:
For a column block index `c : Fin r ⊕ Fin (H2-r)`,

```text
(reindex rThr pivotThr (colPerm_π M))(_, c)
= colPerm_π M(_, pivotThr.symm c)
= M(_, π_J (pivotThr.symm c))
= M(_, rThr.symm (pivotThr (pivotThr.symm c)))
= M(_, rThr.symm c).
```

So

```text
reindex(rThr, pivotThr J)(colPerm_π M)
= reindex(rThr, rThr)(M),
```

not

```text
reindex(rThr, pivotThr J)(M).
```

Thus the pivot reindex does not recover the pivot-column reindex of `M`; it converts it to the threshold-column reindex. Equality with the desired pivot-reindexed matrix holds only if `pivotThr J = rThr`, equivalently the pivot columns are exactly `{0, ..., r-1}`.

Inference/assumption: this assumes the colPerm is an output-column permutation applied directly to the matrix before the outer reindex. If the product is instead `M · Pπ · QL` with a nontrivial `QL` after the permutation, then the outer reindex cannot generally absorb the permutation at all, because `QL` mixes columns.

2. **Q2 verdict: FALSE in general.**

Fact from the above identity: after the colPerm plus pivot reindex, the left column block is the threshold set `{0, ..., r-1}`. In the desired `M_conj`, the left column block is the pivot set `range J`.

The residual energy includes:

```text
top rows, all columns   +   bottom rows, left columns.
```

The top-row part is invariant under column permutation, but the bottom-left part is not unless the left column set is preserved.

Here the left set changes:

```text
pivot-left columns  -> threshold-left columns.
```

So the block partition relevant to the residual is not preserved relative to `M_conj`.

Concrete obstruction: take `r = 1`, `H2 = 2`, `J = {1}`. Then pivot-left is column `1`, threshold-left is column `0`. A matrix with one nonzero bottom-row entry in column `0` has different residual energies under the two splits.

3. **Cleanest provable form / rank.**

The clean entrywise statement you can prove is:

```text
reindex(rThr, pivotThr J)(colPerm_π M)
= reindex(rThr, rThr)(M).
```

So conjunct `(b)` is cleanly provable only if the chosen blocks `P00,P01,P10` are taken from the **threshold-reindexed** residual, or if `J` is the front pivot set. For the stated `hconj`, where the blocks come from

```text
reindex(rThr, pivotThr J)(P0 · (prod(symm w) - B) · QL),
```

the equality is not generally true, not even at Frobenius-energy level.

Rank: **(iii) genuinely needs a changed statement / extra hypothesis / corrected last-layer decode.** It is not merely notational unless `J = {0, ..., r-1}` or the colPerm is removed before the telescope target.