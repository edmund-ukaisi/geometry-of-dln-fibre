**STABLE.**

Let \(r=M(S+1)=\min\{M(S),M^{(S+1)}\}\). At rollover, the collapsed layer-\(S\) factor acts as either \([I_r\ 0]\) or \([I_r;0]\). Consequently, its product with \(C'^{(S+1)}\) retains precisely rows \(1,\ldots,r\) of that matrix. Thus the new working block occupies the static layer-\((S+1)\) slots
\[
(1,\ldots,M(S+1))\times(1,\ldots,M^{(S+2)}).
\]

The transpose distinguishes which side of the rectangular layer-\(S\) factor has surplus coordinates. It does not transpose, re-index, or re-orient \(C'^{(S+1)}\). In both cases the surviving coordinates are the contiguous leading rows; there is no row/column swap, leakage into layer-\(S\) slots, or non-contiguous truncation.

The transfer \(C'^{(S+1)}=Q^{-1}C^{(S+1)}\) is slot-preserving: left multiplication mixes row values, but the resulting entry \((i,j)\) remains stored in static layer-\((S+1)\) slot \((i,j)\).

Hence earlier-layer \(d\)-entries may influence the **values** through \(Q\), but not the slot addresses. No width configuration produces a failure.