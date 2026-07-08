# Statement card — genm-hstep2hsub4 (#120 `hstep2`, item 3 = the `hsub4core` germ)

**Status:** the general-`L` `hsub4core` per-`x` **KEYSTONE** delivered, **sorry-free, axiom-clean**
`[propext, Classical.choice, Quot.sound]` (forced `#print axioms
deepestCoreF_coreAbsorbConj_psiSplitRawGen_eq_score_at_chart`; 0 sorries; no name clash — `rg`-unique;
force-recompiled clean via `scripts/lb`, no lint warnings). **NOT reviewed yet** (fidelity check pending —
leaf executor does not self-review).

**WATCH TRIGGERED — the full germ is NOT parallel.** The mission premised item 3 as "independent of
Producer-1 smoothness." That holds for the *reg* germ (`hsub3reg_gen_germ`, cutoff-free, pointwise-
algebraic) but **NOT** for the *core* germ: `deepestCoreAbsorbConj` carries a **cutoff**, and stripping it
(`deepestCoreF_coreAbsorbConj_eq_prodSchur`) needs the moved point inside the cutoff inner ball (`hq`).
Peeling `hq` over a neighbourhood needs `Tendsto (fun x ↦ psiSplitRawGen (split x)) (𝓝 base) (𝓝 0)`
(equivalently `psiSplitRawGen 0 = 0` + continuity at base) — **Producer 1**, un-built (grepped: no
continuity / `psiSplitRawGen 0 = 0` theorem banked; only building blocks in `DeepestPsiTripleGen`). So the
**FULL germ sequences after Producer 1**. Verdict decorrelated with **Codex xhigh** (V1/V2/V3 all agree):
`expeditions/aoyagi-full/threads/genm-hstep2hsub4/codex/dep-verdict-{prompt,answer}.md`.

Branch: `genm-hstep2hsub4` (pushed). Base: `origin/expedition/aoyagi-full` @ `a717cfe1`.

## File delivered

- `lean/DLNFibre/DLN/RLCT/Validate/DeepestHsub4coreGen.lean` (new, ~135 L, 0 sorry) — STANDALONE
  (force-recompiled green; `rg`-checked, unique new name). **NOT yet imported into `DLNFibre.lean`** — the
  controller wires it (single-writer): add
  `import DLNFibre.DLN.RLCT.Validate.DeepestHsub4coreGen`, and add
  `deepestCoreF_coreAbsorbConj_psiSplitRawGen_eq_score_at_chart` to `AxCheck.lean` so it does not silently
  rot.

## The headline

> **Claim.** General-`L` analog of the landed L=2 per-`x` keystone
> `deepestCoreF_coreAbsorbConj_psiSplitRawL2CoreConj_eq_score_at_chart`. At a chart point, the conjugated
> absorbed-core energy of the moved point `psiSplitRawGen … q` equals the wire's bare `Score x`, GIVEN the
> cutoff-ball membership `hq`, the core-side move readback `hC`, the chain-invertibility `hLayer`/`hPart`,
> the product-pivot `hMid11inv`, and the frame hypotheses.
>
> - **Lean:** `DLNFibre.DLN.RLCT.deepestCoreF_coreAbsorbConj_psiSplitRawGen_eq_score_at_chart`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestHsub4coreGen.lean`).
> - **Gloss.** `deepestCoreF H r (deepestCoreAbsorbConj H r B … hDA (psiSplitRawGen H r hr hL J Pf Qf
>   q)).2.1 = Score x`, where `Score x = frobSqMat (<framed (1,1)-Schur integrand over reindex(endpointP0 ·
>   (prod(decode x) − B) · endpointQL)>)` (the exact wire `Score`, matching the telescope RHS).
> - **Proved.** the per-`x` identity, on the stated hypotheses, over `ℝ` at every `L ≥ 1`.
> - **Route.** `rw [deepestCoreF_coreAbsorbConj_eq_prodSchur … hq, hScoreDef]` then `congrArg frobSqMat
>   (prod_deepestM_eq_schur_ldu_readback_gen …)`. Two banked general-`L` bricks, wired; the `Score`-integrand
>   shape is verified to match the telescope output exactly (a real fidelity check the composition performs).

## Hypotheses carried (the honest remaining inputs — NOT laundered)

- **`hq`** — `psiSplitRawGen … q ∈ closedBall 0 (cutoffBumpConj …).rIn`. **Producer-1** to peel over a
  neighbourhood (needs `Tendsto`/eventual-ball; the sequencing blocker above).
- **`hC`** — the general **core-side move readback**: `reindex (C s) = blockSchur (movedC (deepestChain
  (decode x)) (Z0edit0 …) s)` for `C s = decode((psiSplitRawGen q).2.1) s + schurCorrectionConj(gauge
  reads) s`. **New math, ~300-600 L** (Codex V3): NOT the banked `absorbedCoreConj_eq_schurCore` (unmoved +
  boundary-only), NOT directly `psiSplitRawGen_deepestChain_hmove` (framedParamsPivot chain, not raw
  `decode x`). Cheapest route (Codex, unverified lemma names): rewrite `coreRead`/`gaugeRead` of
  `psiSplitRawGen` to `psiReadBlk`/`psiGhat`, split first/interior/last, land the raw `movedC (deepestChain
  (decode x))` form.
- **`hLayer`/`hPart`/`hMid11inv`** — invertibility of the DECODE chain layers / partProds / product pivot
  near base. Producer-1-FREE (continuous in `x` via decode); bankable as new eventual-unit germs (the banked
  `DeepestChainUnitGerm` bricks are for the FRAMED chain, so not directly reusable — a parallel sub-item).
- **frame hyps** (`hPtri`/`hQtri`/`hP22`/`hQ22`/`hS3b`/`hP11inv`/`hQ11inv`) — the telescope's frame-
  triangular/pivot facts, threaded straight through (hold at the constructed `deepestPoint` frames).

## The precise remaining path to the full germ

1. **`hC`** — the general core-side move readback (new math, ~300-600 L). Parallel-buildable now.
2. **decode-chain invertibility germs** — `hLayer`/`hPart`/`hMid11inv` over a nbhd of base. Parallel now.
3. **`hq` germ** — `∀ᶠ x, psiSplitRawGen (split x) ∈ ball`, from **Producer 1**'s `Tendsto`/`psiSplitRawGen
   0 = 0`. **Sequences after Producer 1.**
4. **Assembly** — `filter_upwards` (2)+(3), `rw hsplit`, apply the keystone with (1). Small, once 1-3 land.

`hstep2` LEFT UNTOUCHED (item 3 is the germ; the compose is separate and needs Producer 1 too).
