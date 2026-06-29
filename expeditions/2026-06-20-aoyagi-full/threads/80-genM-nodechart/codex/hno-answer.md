1. **Bridge for chosen `tStar`: yes, defensible inference.** It should hold for any global minimizer, so `Classical.choose` ambiguity is not the issue. But it is **not** pure admissibility arithmetic.

Pure-admissibility counterexample: take `L=3`, `M=(4,3,1,1)`, `T=(2,1,0)`. Then `T` is admissible, `Text=[4,4,2,1]`, and `Text(L)=1=M[L-1]`. But at `s=1`, `Text(2)=2<Text(1)=4` and `2<M[1]=3`. So the admissible analogue of `BoundaryClean => NoInteriorBothDrop` is false.

2. **Invariant.** For a minimizing admissible `T` with deep equality `T[L-2]=M[L-1]`, every descent is saturated:
`T[i] < prev(i) => T[i] = bound(i)`, where `prev(0)=M0`, `prev(i)=T[i-1]`, and `bound(0)=min M0 M1`, `bound(i)=M[i+1]`.

Equivalently, at an interior drop `Text(s+1)<Text(s)`, admissibility gives `Text(s+1)≤M[s]`, and minimality upgrades this to equality, so the second conjunct of `NoInteriorBothDrop` fails.

Proof sketch: suppose a minimizer has an unsaturated descent at `i=s-1`: `T[i]<prev(i)` and `T[i]<bound(i)`. Deep equality gives a later saturated index, namely `L-2`. Let `q≥i` be the first saturated index. Then raise the block `T[i],...,T[q-1]` by `1`. This preserves admissibility: the left gap allows the first raise, unsaturation gives bounds, monotonicity is preserved, and the fixed final zero is untouched. The `Mval` change is strictly negative: the first term decreases strictly, internal block terms do not increase, and the exit term at `q` has zero cost increase because `T[q]=bound(q)`. Contradiction.

3. **Cheapest Lean route.** Prove a minimizer lemma, not an `InteriorDrop` lemma:

- from `BoundaryClean`, keep only `hDeep : Text L = M[L-1]`;
- translate `hDeep` to saturation of the last relevant `tStar` coordinate;
- prove `raiseBlock_admissible`;
- prove `Mval_raiseBlock_lt`;
- use minimality of `tStar` to rule out any `s` with both-drop.

`¬InteriorDrop` is probably unused for this bridge.

4. **Trap.** The trap is proving the wrong stronger lemma: “any admissible weakly decreasing `T` with `Text(L)=M[L-1]` has no interior both-drop.” That is false, as the `L=3`, `M=(4,3,1,1)`, `T=(2,1,0)` example shows. The minimizer/block-raising argument is the essential missing ingredient.