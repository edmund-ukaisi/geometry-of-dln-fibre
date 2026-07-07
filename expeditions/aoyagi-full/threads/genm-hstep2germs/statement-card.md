# Statement card — `genm-hstep2germs` (#120 `hstep2`, the germ coupled-bulk)

Thread goal: supply the four germ hypotheses (`hbdy`/`hDA`, the Ψ_conj joint move + diffeo triple,
`hsub3reg`, `hsub4core`) that the banked LINK-1 reduction `deepest_diffeo_bridge_gen_assembled`
(`DeepestDiffeoBridgeGenConj`, `genm-hstep2psiconj` @ `43b67bef`) consumes, then compose to close the
general-`L` (`L ≥ 3`) `hstep2` sorry at `DeepestL2Wiring.lean:1060`.

**Branch:** `genm-hstep2germs` (off `origin/genm-hstep2psiconj`) @ `56cd9f0c`.
**hstep2 status:** NOT yet closed — `DeepestL2Wiring.lean:1060` sorry LEFT UNTOUCHED (not laundered);
`deepest_gauge_construction` still carries `sorryAx`. Two of the four germ families banked; the coupled
geometric bulk (the general joint-move DEFINITION + `hsub3reg`/`hsub4core`) remains.

---

## Banked (this thread, sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`)

### Item 4 — general-`L` `hbdy`/`hDA` (the Θ-side block hypotheses)

> **Claim.** At the deepest point every interior layer (`0 < s`, `s+1 < L`) is the block-normal corner
> `diag(I_r, 0)`, so `deepBlkY_s = 0` and `deepBlkA_s = I_r`; with the two boundary layers this gives
> the general `hbdy : ∀ s, deepBlkY_s = 0 ∨ deepBlkZ_s = 0` and `hDA : ∀ s, IsUnit (deepBlkA_s)`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.deepBlk_boundary_gen`, `deepBlkA_isUnit_gen` (+ interior lemmas
>   `deepestPoint_interior_cols_vanish`, `deepBlkY_interior_zero`, `deepBlkA_interior_eq_one`,
>   `deepBlkA_interior_isUnit`) — `lean/DLNFibre/DLN/RLCT/Validate/DeepestDeepBlkBoundaryGen.lean`
>   @ `56cd9f0c`.
> - **Gloss.** `deepBlk_boundary_gen H r B hB hr hL hL2 : ∀ s : Fin L, deepBlkY … s = 0 ∨ deepBlkZ … s = 0`;
>   `deepBlkA_isUnit_gen … htop J hJfront' Qf hcorner hQUpper : ∀ s : Fin L, IsUnit (deepBlkA … s)`.
>   Interior via `deepestPoint_interior_eq_corM` (interior deepest layer = corner); layer 0 via
>   `deepBlkY_layer0_zero` / `deepBlkA0_isUnit_of_htop`; layer `L−1` via `deepBlkZ_layerLast_zero` /
>   `deepBlkA_last_isUnit_of_bundle`.
> - **Proved.** Both `hbdy` and `hDA` at general `L` (`2 ≤ L`), from the corner structure + the two
>   landed boundary-layer lemmas. The general lift of the `L = 2` `deepBlk_boundary_of_L2` /
>   `deepBlkA_isUnit_of_L2`.
> - **Assumed.** `htop` (row-WLOG), the block-triangular pivot-bundle facts `hcorner`/`hQUpper`
>   (`J = frontEmbed`) — the same data the `L = 2` wire already supplies (and the `L ≥ 3` arm has in
>   scope as `hcorner'`/`hQUpper`).
> - **Cited / Deferred.** none.
> - **Status.** sorry-free.

### Item 1 (analytic half) — general cutoff→flat-diffeo plumbing (the abstract `psi` triple)

> **Claim.** For ANY raw split-side move `psiSplitRaw : DeepestSplit → DeepestSplit` fixing the split
> origin, `ContDiffAt` on a bump support, with vanishing strict derivative of the deviation
> `psiSplitRaw − id` at `0`, the concrete flat move `psi = split⁻¹ ∘ (q + χ·(psiSplitRaw − id)) ∘ split`
> satisfies the diffeo triple (`ContDiff ⊤` / `HasStrictFDerivAt psi id wstar` / `psi wstar = wstar`)
> and the split-compat germ `∀ᶠ x near wstar, split (psi x) = psiSplitRaw (split x)`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.deepestPsiFlatCut` + `contDiff_deepestPsiFlatCut`,
>   `hasStrictFDerivAt_deepestPsiFlatCut`, `deepestPsiFlatCut_fixpoint`, `deepestPsiFlatCut_split_germ`
>   (+ `deepestPsiCutRaw`, `deepestPsiCutRaw_zero`, `contDiff_deepestPsiCutRaw`,
>   `hasStrictFDerivAt_deepestPsiCutRaw_zero`) —
>   `lean/DLNFibre/DLN/RLCT/Validate/DeepestPsiFlatCutGen.lean` @ `56cd9f0c`.
> - **Gloss.** Given `hraw0 : psiSplitRaw 0 = 0`, `hderiv0 : HasStrictFDerivAt (psiSplitRaw − id) 0 0`,
>   `hcd : ContDiffAt (psiSplitRaw − id)` on `tsupport χ`, and `hbase : split wstar = 0` (concrete
>   `split = deepestSplit … wstar`), the four theorems produce exactly the abstract-`psi` hypotheses of
>   `deepest_diffeo_bridge_gen_assembled` (`hcontdiff`, `hderiv`, `hfix`, `hsplitPsi`).
> - **Proved.** The full analytic plumbing (cutoff bump smoothing, the strict-derivative-`id` chain, the
>   origin fixpoint, the `χ = 1` split germ), abstracting the `L = 2` `psiL2Conj`/`psiSplitCutL2Conj`
>   apparatus away from the concrete `psiSplitRawL2CoreConj`.
> - **Assumed.** The abstract hypotheses on `psiSplitRaw`/`χ` above — discharged only once the
>   geometric joint move + its bump support are supplied (the deferred bulk).
> - **Cited / Deferred.** none proved-here; the joint-move `psiSplitRaw` is the input, not produced here.
> - **Status.** sorry-free.

---

## Deferred — the coupled geometric BULK (the remaining item; a genuine multi-tide)

Closing `hstep2` needs, plugged into `deepest_diffeo_bridge_gen_assembled`:

1. **The concrete general joint move `psiSplitRawGen`** (item 1 geometric half). The `L = 2`
   `psiSplitRawL2CoreConj` touches ONLY the last layer (core `T1'c` + `Y`-tag `Y1'c`) because
   `deepestEFull` reads the full framed product `∏C = C_0·C_1` and only the last-layer coupling is
   non-trivial. For general `L` the core shear acts at ALL layers `s ≥ 1` (the `coreProd C L =
   ∏_s (1−K_s)·S_s` factors, `K_0 = 0` by `Kcoup_zero`), so `psiSplitRawGen` must carry a per-layer
   core update PLUS a per-layer reg/gauge correction keeping `deepestEFull` (`= (P00−1, P01, P10)` of
   `∏C`) invariant. No closed form for the per-layer payload without the block derivation — this is the
   crux DESIGN decision, tightly coupled to items 2–3 (a wrong definition walls them). Its `D(0) = id`
   (`hderiv0`) + `psiSplitRawGen 0 = 0` + `ContDiffAt` on the joint-unit set then feed the banked
   `DeepestPsiFlatCutGen` plumbing to get the diffeo triple.
2. **`hsub4core` — the honest chain** `deepestCoreF (deepestCoreAbsorbConj (psiSplitRawGen (split x))).2.1
   = Score x`. Backbone LANDED and general: `schur_product_ldu_rec` / `Kcoup_zero` / `blockSchur` /
   `partProd` / `coreProd` (`DeepestSchurRecursion.lean`). Remaining: the DLN-specific bridge
   `Ĉ_s = reindex(decode s)` + `partProd Ĉ L = reindex(prod decode)` (the `Fin L ↔ ℕ` product-reindex
   cast, cf. the `prodAux` front-peel kernel in `lean/CLAUDE.md`) + frame-strip to the framed `Score`.
   Numerically VERIFIED (genm-hstep2chain) → labor, not a satisfiability risk.
3. **`hsub3reg` — reg preservation** `∑ deepestEFull(psiSplitRawGen (split x))² = ∑ deepestEFull(split x)²`
   (general lift of `hsub3reg_conj_germ`, `DeepestL2ConjReg`; residual-block algebra via `hra_regval`).

Items 2–3 are STATABLE only once `psiSplitRawGen` (item 1 geometric) is DEFINED; all three mirror the
`L = 2` `…Conj` block apparatus (`DeepestDiffeoBridgeL2Conj`, ~2700 lines) uniformly over the `L`
layers — bounded per-layer but genuinely multi-tide-scale. Then compose:
`rw [deepest_diffeo_bridge_gen_assembled …]` (discharging `hbdy`/`hDA` via item 4, the diffeo triple +
`hsplitPsi` via `DeepestPsiFlatCutGen`, and `hsub3reg`/`hsub4core`) → close `DeepestL2Wiring.lean:1060`.

**Controller wiring:** import `DeepestDiffeoBridgeGenConj`, `DeepestDeepBlkBoundaryGen`,
`DeepestPsiFlatCutGen` into `DLNFibre.lean` (done in this worktree's aggregator; single-writer at
integration).
