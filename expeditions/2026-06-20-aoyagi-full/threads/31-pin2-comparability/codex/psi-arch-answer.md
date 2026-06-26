1. **Architecture**

**Pick (A). INFERENCE:** define `Ψ_split` by decode/edit/encode “lenses”, then wrap the raw deltas in a cutoff so the exported map is globally `ContDiff ⊤`. The existing bridge explicitly wants global smoothness, and the raw formula has inverse-bearing terms `A0⁻¹`, `A1⁻¹`, `W⁻¹`, so copying the `schurCutoffShift` pattern is necessary. I would not use (B): `coreShearHomeo` is a fiber translation with shift independent of core, while your `T1'` depends on `T1` and the `Y1` write depends on `T1'`; a composed shear version creates snapshot/order problems and still needs the same read-after-write lemmas.

Key lemmas for (A):

- `regGaugeSlotEquiv_write_lastY_read` and `paramsEquivFlat_write_lastT_read`: after editing the whole decoded function, `readY ... last = Y1'`, other `readX/readY/readZ` are unchanged, and `(paramsEquivFlat _).symm newCore last = T1'`.
- `contDiff_PsiSplit` via a cutoff version of the raw deltas:
  `T1_cut = T1 + χ q • (T1_raw' - T1)`, `Y1_cut = Y1 + χ q • (Y1_raw' - Y1)`, with `χ = 1` near `0` and support inside the unit locus for `A0,A1,W`.
- `PsiSplit_zero` and `hasStrictFDerivAt_PsiSplit_zero_id`, then conjugate by `deepestSplitCLE` using `contDiff_deepestSplit(_symm)` and `hasStrictFDerivAt_deepestSplit(_symm)`.

2. **Key Risk**

**Most likely failure mode (INFERENCE):** not overlap of reg/spectator slots, but writing the wrong last-layer `Y` index because of the `H_lastLayer_succ`/`finCongr` cast and pivot-vs-threshold column split. The actual read index is:

```lean
⟨lastLayer hL, Sum.inl (Sum.inr (i, j))⟩ : RegGaugeIdx H r
```

not “whatever corresponds to `P01` after pivot packing” unless you prove the cast bridge.

Cheap first test: before defining Ψ, prove tiny lens lemmas for a single write:

```lean
readY ... ((regGaugeSlotEquiv ...).symm g').1₂ (lastLayer hL) = Ynew
readX ... = readX ... old
readZ ... = readZ ... old
readY ... s = readY ... old   -- for s ≠ last or non-target entries
(paramsEquivFlat _).symm (paramsEquivFlat _ T') (lastLayer hL) = Tnew
```

If these do not close mostly by `Homeomorph.apply_symm_apply`, `MeasurableEquiv.symm_apply_apply`, `ext`, and `by_cases` on the exact `RegGaugeIdx`, fix the indexing before building Ψ.

3. **Product Level**

**NO**, do not try to prove the last framed layer, or the whole product matrix, is unchanged. **From the stated encoding:** the last factor changes under `Y1,T1`; only the full product’s regular blocks `P00−1,P01,P10` are preserved.

Route: prove `deepestEFull (Ψ_split q) = deepestEFull q` by unfolding `deepestEFull`, extensionality on `i`, and case-splitting on `regResidualPack H r hr i`. Use product-block algebra, not per-layer equality. The banked starting points are `twofactor_block_product` for the `G0·G1` block computation, plus `framedParamsPivot_last/of_ne_last` and `regResidualPack`. If you need the energy form, `deepestEFull_sq_sum_eq_blocks` is already the packed block-energy bridge, but for pointwise preservation you want a new narrow lemma: “the reindexed full product’s `toBlocks₁₁`, `toBlocks₁₂`, `toBlocks₂₁` are unchanged under the raw Ψ near `0`.”