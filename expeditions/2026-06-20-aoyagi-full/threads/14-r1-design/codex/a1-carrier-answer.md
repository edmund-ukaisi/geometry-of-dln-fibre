codex
**Bridge Carrier**
- The conservation formula `uTel qFM i = (∑ R_i) − (∑ Mwidths.drop i)` is the right bridge: unrolling `uTel` gives `uTel qFM i = M⁰ + ∑_{k<i}(M^{k+1} − qFM_k)`, while the residual pool satisfies `∑ R_i = ∑ Ymulti − ∑_{k<i} qFM_k` and the suffix widths satisfy `∑ Mwidths.drop i = ∑_{k≥i} M^{k+1}`; subtracting those equalities shows the carrier depends only on already-chosen picks and the suffix data, exactly matching the local state.  
- If you want to hide `R_i`, package the state as an inductive carrier `FMState i := (pool_i, suffix_i, deficit_i)` with fields `pool_i := eraseIter i Ymulti`, `suffix_i := Mwidths.drop i`, and `deficit_i := uTel qFM i − M^{i}`; the conservation clause becomes a simple invariant `deficit_i = ∑ pool_i − ∑ suffix_i` that avoids naming `R_i` explicitly while still encoding the same arithmetic.

**Suffix Lemma**
- Define the iterated erasure `eraseIter : ℕ → Multiset ℤ → List ℤ → Multiset ℤ` by `eraseIter 0 R widths = R` and `eraseIter (i+1) R (w::ws) = eraseIter i (R.erase (maxPick w ws R)) ws`.  
- The structural lemma you need can be stated as  
  `forwardMax_drop_eq : ∀ i, forwardMax widths R = (forwardMax widths R).take i ++ forwardMax (widths.drop i) (eraseIter i R widths)`  
  and its corollary  
  `forwardMax_getD_eq : (forwardMax widths R).getD i 0 = headD (forwardMax (widths.drop i) (eraseIter i R widths)) 0`.  
  In Lean, phrase it with `List.getD`/`List.drop` and prove by induction on `i`, using the defining equation for `forwardMax`. This lemma provides the precise identification between the global entry `qFM_i` and the local head of the recursion at depth `i`.

**Circularity Check**
- `head'_i` depends on `uTel qFM i`, which in turn expands to `M⁰ + ∑_{k<i}(M^{k+1} − qFM_k)`; thus `head'_i` only references picks strictly before stage `i`.  
- The step `INV(i) ⇒ band(i)` uses `head'_i` solely as a lower bound obtainable from the already-known history; the proof of `qFM_i ≥ head'_i` rests on Dom-preservation of the candidate `y` and the maximality of `maxPick`, not on the target inequality for stage `i`.  
- Updating `INV(i+1)` uses the freshly chosen `qFM_i` only through explicit arithmetic in the window-count argument; no part of the update requires assuming the still-unproved band at stage `i+1`. The induction is therefore well-founded and free of hidden circularity.

**Target Statement**
- The reduction “per-step band ⇒ admBound” is already optimal: from `qFM_j ≥ uTel j`, the recursion gives `uTel (j+1) = uTel j + M^{j+1} − qFM_j ≤ M^{j+1}`, and the base inequality `qFM_0 ≥ max(M⁰,M¹)` yields `uTel 1 ≤ admBound 0`.  
- You can bundle the argument as an inductive statement `∀ j ≤ L, uTel j ≤ min (M^{j}, qFM_{j−1})` (with the `qFM_{−1}` term interpreted as `M⁰`) if you prefer a single invariant, but it decomposes back into the same per-step inequality plus the one-time base case.
tokens used
