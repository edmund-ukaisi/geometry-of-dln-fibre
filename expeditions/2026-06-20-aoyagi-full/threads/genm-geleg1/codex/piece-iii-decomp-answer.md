**1. Recursion Verdict**
Pick **(b')**: a prefix-accumulator fold, exposed as a final same-type self-map `BlockParamsGen H r → BlockParamsGen H r`. Mathematically, set `P_s = partProd C s` and eliminate layer `s` using only pivots `(P_s)₁₁` and `(P_{s+1})₁₁`; define reduced factors `R_s = C_s₂₂ - C_s₂₁ (P_{s+1})₁₁⁻¹ (P_{s+1})₁₂`. Lean inference: do not force each elementary step to be a same-type map; the accumulator width changes. The **final** chart can still be same-type by packing prefix top rows, final `P_L₂₁`, and the `R_s` into the original layer slots. Avoid (a) if it means adjacent original layers, and avoid (c).

**2. Reuse Map**
- `schurChartRaw`: **fresh**; define by prefix fold/packing, L=2 is specialization.
- `schurChartRawInv`: **induction-reuse**; backward reconstruction using prefix rows.
- 5 recon lemmas: **induction-reuse** after making the L=2 algebra type-generic.
- ContDiff-on-domain: **induction-reuse**; finite rational fold over prefix pivots.
- `schurChart_global`: **induction-reuse**; same local-inverse/globalization skeleton.
- `recoverProduct`: **fresh**; product of all reduced factors replaces two-factor rebuild.
- germ/readout: **induction-reuse** in structure, but statements are fresh general-L.

**3. Ladder**
1. `prefixPivotDomGen`: domain `∀ k≤L, det (P_k)₁₁ ≠ 0` plus piece(i) bridge. Risk low. Bank yes.
2. `blockSchur_partProd_succ_asym`: prove `Sch(P_{k+1}) = Sch(P_k) * R_k` using `schur_product_factor`, no hLayer. Risk med. Bank yes.
3. `blockSchur_partProd_asym_fold`: telescope `Sch(P_L)=∏ R_k` from prefix pivots only. Risk med. Bank yes.
4. `schurChartRawGen` + readback simp lemmas: same-type packed chart. Risk med-high. Bank yes. **Likely one-session ceiling.**
5. `recoverProductGen_schurChartRawGen`: rebuild full product from final top row, final lower-left, and `∏ R_k`. Risk high. Bank yes.
6. `schurChartRawInvGen`: backward inverse; reconstruct suffix layers, then first layer from final `P_L₂₁`. Risk high. Bank yes.
7. `contDiff_raw_inv_gen`: entrywise `ContDiffAt/On` on finite prefix-pivot domain. Risk med-high. Bank yes.
8. `schurChart_global_gen` and `schur_loss_germ_gen_at_pivot`: conjugate by `blockFlatEquivGen`, use `reindex_prod_eq_genPartProd`. Risk high. Bank yes.

**4. Risk**
- hLayer leaks only if you use `blockSchur_mul`/`schur_product_ldu_rec`; use the asymmetric factor step.
- IH must carry all prefix pivots, including `P_L`; piece(i) supplies exactly these.
- Cast pressure concentrates at `BlockParamsGen` ↔ `partProd/genChain` bridges and final readout.
- The inverse is the algebra ceiling: suffix reconstruction is clean, first-layer reconstruction uses final `P_L₂₁`.