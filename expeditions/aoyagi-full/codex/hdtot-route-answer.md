**Ranking**

1. **C**: Best route. It uses the banked `lowerTri_det` at the linear-map level and avoids opaque `StairProd` recursion; the hard work becomes two projection equations plus determinant bookkeeping.
2. **A**: Viable but heavier. `stairMap_abs_det_twoConj` is tailored, but building `eIn/eOut : _ ≃ₗ StairProd V 2` and proving exact `stairMap` equality is likely more cast-heavy than the actual determinant argument.
3. **B**: Worst for this goal. Matrix reindexing worked for literal `(2,2,2)`, but opaque-width slot bijections plus per-entry collapse is exactly where Lean time disappears.

**Top Route: C Sub-Lemmas**

1. `slotEquiv_BparamsLeaf_twoBlock`
   Proves input/output flat coordinates split as `(V0 × V1)` with `V0 = SchurInc t r c`, `V1 = chain block`.
   Risk: **HIGH**. Hazard: opaque `Fin N` arithmetic through `chartIdxEquiv`, dependent layer widths, `Fin.cast`/`Fin.succ` coercions.

2. `fderiv_BparamsLeaf_hasValue`
   Proves `fderiv ℝ BparamsLeaf y₀` equals the assembled CLM from the banked `hasFDerivAt_*` atoms.
   Risk: **MED**. Hazard: CLM extensionality and coercions from `ContinuousLinearMap` to `LinearMap`.

3. `BparamsLeaf_block00_schur`
   Under the split, the `V0 → V0` block is `schurFrameDeriv X K N`.
   Risk: **HIGH**. Hazard: matching `readK/readX/readN/readE`, radial-1 frame, and `c0 = 0` collapse without losing definitional equality.

4. `BparamsLeaf_block01_zero`
   The layer-0 output is independent of `(W, leaf)`, so the upper-right block is zero.
   Risk: **LOW/MED**. Mostly follows from stated structure plus extensionality.

5. `BparamsLeaf_block11_chainUnit`
   The `V1 → V1` block for `(W, leaf) ↦ Agen1` has determinant absolute value `1`.
   Risk: **MED**. Hazard: whether this is already banked as a unit determinant or must be derived from a product/permutation form.

6. `BparamsLeaf_block10_exists`
   Packages the shared-`N` coupling into some `h : V0 →ₗ V1`; no determinant computation needed.
   Risk: **LOW**. Do not simplify it.

7. `BparamsLeaf_conj_lowerTri`
   Proves the split derivative equals `lowerTri f g h`.
   Risk: **HIGH**. Hazard: product extensionality plus all prior casts must line up exactly.

8. `hDtot_from_lowerTri`
   Applies `lowerTri_det`, `schurFrameDeriv_det`, `|det g| = 1`, and `Bchart_abs_det_eq_Dtot`.
   Risk: **MED**. Hazard: determinant of pre/post linear equivalences if input/output splittings differ; need the analogue of the stated `hreg`.

**Most Likely Wall**

The wall is `slotEquiv_BparamsLeaf_twoBlock` combined with `BparamsLeaf_block00_schur`: a green-looking reindex can silently put `N`, `E`, or the layer slices in the wrong order, and opaque `Fin` casts may make the final extensionality proof intractable.

Cheapest de-risk first: prove only the `V0 → V0` projection equation after splitting, with `W` and `leaf` increments set to zero, ending exactly in `schurFrameDeriv X K N`. Do not build `lowerTri` yet.

**Verdict**

Reachable only if the slot split and Schur block identification are already close to existing notation. Dominant cost is not determinant algebra; it is opaque-width coordinate plumbing. I agree with the prior “multi-tide wall” assessment unless the precise sub-goal

`projV0 ∘ fderiv BparamsLeaf y₀ ∘ inclV0 = schurFrameDeriv X K N`

can be made to close cleanly first.