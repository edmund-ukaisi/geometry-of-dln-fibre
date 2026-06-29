# Statement card — Step Ψ_conj (the conjugated joint-Ψ L=2 diffeo bridge)

Thread `genm-l2psi`. Module: `lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2Conj.lean`.
The CONJUGATED parallel of the bare joint-Ψ apparatus (`DeepestDiffeoBridgeL2`), closing the
RLCT-side half of the atom-free L2 bridge `hstep2 = Step Θ (banked) ∘ Step Ψ_conj`.

> **Claim (Step Ψ_conj).** The local RLCT of `Φscore` at `wstar` equals that of the conjugated
> absorbed-core energy `Φcore_conj` (reg term + `deepestCoreF ∘ deepestCoreAbsorbConj ∘ split`), via a
> basepoint-fixing local diffeo `psiL2Conj` whose derivative at `wstar` is the identity (`e = refl`).
>
> - **Lean:** `DLNFibre.DLN.RLCT.deepest_diffeo_bridge_L2_conj_impl`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2Conj.lean` @ `931060b7`)
> - **Gloss.** For `L = 2`, given the pivot-base units `hDA : ∀ s, IsUnit (deepBlkA_s)` and the L=2
>   boundary vanishing `hY : deepBlkY_0 = 0`, `hZ : deepBlkZ_last = 0`, the conjugated joint move
>   `psiL2Conj = split⁻¹ ∘ (q ↦ q + χc(q)•(psiSplitRawL2CoreConj q − q)) ∘ split` is `ContDiff ⊤`,
>   fixes `wstar`, and has strict derivative `id` there. Hence `rlctAtOn Φscore wstar = rlctAtOn
>   Φcore_conj wstar`, where `Φcore_conj x = ∑(regStraighten(split x)).1² + deepestCoreF (conjAbsorb
>   (split x)).2.1`. The conjugated pivots are `A0c = deepBlkA_0 + readX_0`, `A1c = deepBlkA_last +
>   readX_last`, off-diagonals `M̄·+read·`; the gauge re-encode writes the last-Y READ
>   `Y1'c − deepBlkY_last` (not the block `Y1'c`) and the core block `T1'c` literally.
> - **Proved (unconditional in-file).**
>   - `D(Ψ_conj)(0) = id` — the lens keystone `hasStrictFDerivAt_psiSplitDeltaL2CoreConj_zero`: the
>     conjugated joint correction has strict derivative `0` at the split origin (so `psiSplitCutL2Conj`
>     and `psiL2Conj` have strict derivative `id`). The mechanism: at `q = 0` all reads vanish and the
>     deepest off-diagonals `deepBlkY_0`, `deepBlkZ_last` vanish (`hY`/`hZ`), so `Y0c = Z1c = 0`, hence
>     `Kc = Rc = Wc−1 = 0`, `T1'c−T1c = 0`, `Y1'c−Y1c = 0` — the SAME pattern as the bare; the pivots
>     being deepest-block units (not `1`) is invisible.
>   - The full S2 ContDiff chain (entrywise + inverse ContDiffAt at origin where `hDA` enters +
>     composite + the `_at` cutoff-support chain) ⟹ `psiL2Conj_contDiff`.
>   - S3 fixpoint `psiL2Conj_fixpoint`, S4 `psiL2Conj_hasStrictFDerivAt = id`.
>   - The cutoff machinery `jointUnitSetConj` + `cutoffBumpSplitConj` (origin in the joint unit set via
>     `hDA`/`hY`; support ⊆ joint unit set).
>   - S6 `comp_identity_L2_conj` (germ): `Φcore_conj ∘ psiL2Conj =ᶠ[𝓝 wstar] Φscore`.
>   - The boundary vanishing `deepBlkY_layer0_zero` / `deepBlkZ_layerLast_zero` / `deepBlk_boundary_of_L2`.
> - **Assumed (parametric inputs, the bare's contract).**
>   - `hsub3reg` — the `deepestEFull²`-sum reg-energy invariance under the conjugated move
>     `psiSplitRawL2CoreConj` (germ-local). The module-level reg-INPUTS are banked
>     (`readX/Y/Z_psiSplitRawL2CoreConj_eq`, `framedParamsPivot_psiSplitRawL2CoreConj_of_ne`); the wire
>     assembles them via `e2_regPreserve` (with the conjugated `l2A0c`, needs only hDA0) +
>     `reindex_prod_regBlocks_eq_of_e2`. **The bare's `hm11/hm12/hm21` wire-tie DISSOLVES** for the
>     conjugated (frame-correct) move (genm-l2thread, defs + 4 numerics) — the conjugated route removes
>     the bare's OTHER blocker.
>   - `hsub4core` — the core = Score (germ-local). The keystones are PROVEN
>     (`absorbedCoreConj_psiSplitRawL2CoreConj_last = (1−Kc)·S1c`, `_of_ne`,
>     `l2T1pConj_sub_Z1A1invY1pConj_eq`); the in-file discharge
>     `deepestCoreF_coreAbsorbConj_psiSplitRawL2CoreConj_eq_score` is PROVEN modulo the single conjugated
>     readback-tie `hLDUtieConj` (`frobSq(prod(deepestM) C) = Score`), which is TRUE here (vs the bare's
>     permanent W-a-FALSE sorry at `DeepestL2Wiring:679`) — the conjugated route closes what the bare
>     never could. The `hLDUtieConj` full discharge (via `prod_deepestM_eq_schur_ldu_readback` +
>     `absorbedCoreConj_eq_schurCore`, with the chart-point block-alignment + the `subst hL2eq`
>     late+local Fin-3 application) is the remaining follow-on.
>   - `hDA : ∀ s, IsUnit (deepBlkA_s)`. Layer-0 = `deepestPoint_leadingBlock_isUnit`/htop at the wire;
>     layer-(L−1) = the row-WLOG dual, the staged #154 seam (controller coordinates the ⨅-discharge).
> - **Cited.** none new (reuses banked Step Θ keystones `absorbedCoreConj_eq_schurCore`,
>   `prod_deepestM_eq_schur_ldu_readback`, `deepBlkT_{layer0,layerLast}_zero`,
>   `deepestCoreF_coreAbsorbConj_eq_prodSchur`, and the abstract `rlctAtOn_diffeo_bridge_of`).
> - **Deferred.** The wire rewire `hstep2 = Step Θ ∘ Step Ψ_conj` (single-writer `DeepestL2Wiring.lean`,
>   the controller's). The `hLDUtieConj` full discharge (chart-alignment + Fin-3 subst, follow-on).
> - **Correctness catch (banked).** The gauge re-encode read↔block OFFSET: the conjugated last-Y tag
>   stores the READ `Y1'c − deepBlkY_last`, NOT the block `Y1'c` (literal `Y1'c` breaks the basepoint —
>   `deepBlkY_last ≠ 0` at the L=2 boundary). genm-l2thread verified (defs + 2 numeric tests). The CORE
>   is `T1'c` literal (`deepBlkT_last = 0`). Asymmetry: Y-tag offset, core literal.
> - **Status.** sorry-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`) — fidelity review pending.
