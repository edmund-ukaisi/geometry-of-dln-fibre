**Q1**
1. **B-shortcut**: cheapest. Do not generalize Dtot; prove `BchartE ha = BchartLeaf ha` under `hdr0 : Text M (tach M) 2 = 0`, then reuse banked `BchartLeaf_abs_det_free`.
2. **C**: next best fallback. Directly show `BchartE` is a symbolic coordinate relabeling, but this still needs a `FlatIdx ↔ ChartIdx` slot proof.
3. **A**: viable but heavier. `measurePreserving_paramsPack_of_flatIdxEquiv` gives the symbolic permutation route, but proving the symbolic `hpack`/slot equation is the real work.

**Q2**
Winner lemma chain:

1. Prove:
   ```lean
   rfinDirect_eq_zero_of_hdr0 :
     hdr0 : Text M (tach M) 2 = 0 →
     rfinDirect ha y = 0
   ```
   by `ext i j`; `i : Fin (Text ... 2)` is impossible after `rw [hdr0]`.

2. Then:
   ```lean
   BparamsE_eq_BparamsLeaf_of_hdr0 :
     BparamsE ha y = BparamsLeaf ha y
   ```
   by unfolding `BparamsE`, `BparamsLeaf` and rewriting `rfinDirect`.

3. Then:
   ```lean
   BchartE_eq_BchartLeaf_of_hdr0 :
     BchartE ha = BchartLeaf ha
   ```

4. Rewrite the goal to `BchartLeaf`, then use banked:
   ```lean
   BchartLeaf_abs_det_free ha z (eihd_hreg ha)
   ```

5. Close the RHS with `hdr0`:
   ```lean
   (Matrix.of (readK M (tach M) ha z ⟨0, by decide⟩)).det = 1
   ```
   by showing the matrix equals `1` on a `Fin 0` index, then `Matrix.det_one`; finish with `abs_one`, `one_pow`.

Hardest sublemma: `BchartE_eq_BchartLeaf_of_hdr0`, specifically making the dependent zero matrix rewrite `rfinDirect ha y = 0` pass cleanly through `genBlkFlatLive`.

**Q3**
No direct bare `|det paramsEquivFlatCLE M| = 1` is the useful statement: `paramsEquivFlatCLE M` is not an endomorphism of one type for `LinearMap.det`.

For self-maps, this repo has the banked lemma:
```lean
continuousLinearMap_abs_det_eq_one_of_measurePreserving
```
The Mathlib lemma used inside it is:
```lean
MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
```
I am not sure v4.29 has a higher-level one-line Mathlib theorem for this; use the local wrapper.

**Q4**
Biggest wall: dependent rewriting around `Text ... 2 = 0`, not determinant theory. Avoid opening/genericizing Dtot and avoid symbolic slot permutations unless the `BchartE = BchartLeaf` rewrite unexpectedly fails.

**VERDICT**
Build Route B-shortcut: `BchartE = BchartLeaf` under `hdr0`, then reuse `BchartLeaf_abs_det_free`.

Prove first: `rfinDirect_eq_zero_of_hdr0`; then the determinant should be a short rewrite plus empty-`readK` det.