# Statement card — genm-hstep2tel (#120 `hstep2`, Producer 3 = the `hsub4core` Schur→Score telescope)

**Status:** Producer 3 (the general-`L` Schur→Score telescope) **COMPLETE, sorry-free, axiom-clean**
`[propext, Classical.choice, Quot.sound]` (forced `#print axioms
prod_deepestM_eq_schur_ldu_readback_gen` loses `sorryAx`; the other three delivered results are equally
clean). Independent of Producer 1 (the diffeo triple) — no `psiSplitRawGen` differentiability, no
`deepestSplit` analysis. `hstep2` (`DeepestL2Wiring:1060`, L ≥ 3 arm) **LEFT UNTOUCHED** (the compose is a
separate step needing Producer 1 too).

Branch: `genm-hstep2tel` (pushed, @ `a30f2a13`). Base: `origin/expedition/aoyagi-full` @ `51a3dbdb`.

## File delivered

- `lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurScoreTelescopeGen.lean` (new, 321 L, 0 sorry) —
  STANDALONE (force-recompiled green via `scripts/lb`; no name clashes with siblings, `rg`-checked). **NOT
  yet imported into `DLNFibre.lean`** — the controller wires it (single-writer): add
  `import DLNFibre.DLN.RLCT.Validate.DeepestSchurScoreTelescopeGen`, and add
  `prod_deepestM_eq_schur_ldu_readback_gen` to `AxCheck.lean` so it does not silently rot (nothing imports
  it yet, so the aggregate build does not re-check it).

## The headline

> **Claim.** General-`L` analog of the banked L=2 `prod_deepestM_eq_schur_ldu_readback`. For a reduced-core
> tuple `C : Params (deepestM H r)` whose reindexed layers read back as the **moved Schur cores**
> `blockSchur (movedC (deepestChain … (decode x)) (Z0edit0 …) s)` (`hC`), and the frame-triangular /
> pivot / chain-invertibility facts (which hold near the deepest point), the reduced-core product
> `prod (deepestM H r) C` equals the Score `(1,1)`-Schur integrand over the framed `prod(decode x) − B`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.prod_deepestM_eq_schur_ldu_readback_gen`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurScoreTelescopeGen.lean` @ `a30f2a13`).
> - **Gloss.** `prod (deepestM H r) C = ScoreIntegrand x`, where `ScoreIntegrand x =
>   (reindex (rThr 0) (pivotThr J) (endpointP0 · (prod(decode x) − B) · endpointQL)).toBlocks₂₂
>   − (·).toBlocks₂₁ · ((·).toBlocks₁₁ + 1)⁻¹ · (·).toBlocks₁₂` and `decode x = (paramsEquivFlat H).symm x`.
>   This is exactly the RHS-matrix of the L=2 template `prod_deepestM_eq_schur_ldu_readback`; the compose
>   `frobSqMat`-wraps both sides to reach `hsub4core`'s `deepestCoreF … = Score x`.
> - **Proved.** the matrix identity, unconditionally on the stated hypotheses, over `ℝ` at every `L ≥ 1`.
> - **Assumed (hypotheses carried).** `hC` (the per-layer moved-Schur-core readback — supplied by the
>   compose via the general readback dictionary + `hmove`, the coupled bulk); `hLayer`/`hPart` (chain
>   layer/partial-pivot invertibility); `hPtri`/`hQtri`/`hP22`/`hQ22` (endpoint-frame triangularity + `₂₂=1`);
>   `hS3b` (`−B` corner-split); `hP11inv`/`hQ11inv`/`hMid11inv` (frame + product pivots); `hJfront`
>   (`J = frontEmbed`). Same hypothesis shape as the L=2 template.
> - **Cited.** none.
> - **Deferred.** the discharge of `hC`/`hLayer`/`hPart` at the concrete `psiSplitRawGen`-moved point (the
>   general readback dictionary — `absorbedCoreConj_eq_schurCore` generalized — and the near-deepest-point
>   unit germs) belongs to the compose / Producer 1, not here.
> - **Status.** sorry-free (pending reviewer fidelity check).

## Supporting results delivered (one line each, all sorry-free, axiom-clean)

- `score_eq_unframedSchur_prodDecode_gen` — the general-`L` copy of the banked L=2
  `score_eq_unframedSchur_prodDecode` (whose body never used its `hL2 : L = 2`): the Score integrand
  (framed `−B`, pivot `(M₁₁+1)⁻¹`) equals the unframed `(1,1)`-Schur of `reindex(prod(decode x))`. Proof =
  `rcore_eq_schur_of_corner_split` (corner) + `framedSchur_eq_unframedSchur_L2` (frame-strip, itself
  general-`L`).
- `pivotFront_toBlocks₂₂_eq_chainCol` — the missing `₂₂` block of the pivot-front / `deepestChainCol L`
  column reconciliation (mirror of the banked `pivotFront_toBlocks₁₂_eq_chainCol`).
- `reindex_prodAux_deepestM_eq_prodSchurCore` — the **reduced-core fold bridge**: for every prefix `k ≤ L`,
  the reindexed reduced-core product `prodAux (deepestM H r) C k` equals `prodSchurCore (deepestChain …
  (decode x)) Z0 k`, given `hC`. Mirror of `reindex_prodAux_eq_partProd` on UNBLOCKED matrices (a `finCongr`
  width relabel). This is the new `Fin↔ℕ` cast piece.
- `prodSchurCore_deepestChain_eq_blockSchur_reindex` — the **chain-lock**: the product of moved Schur cores
  equals the unframed Schur of `reindex (rThr 0)(deepestChainCol L)(prod (decode x))`, via the banked
  Invariant B `prodSchurCore_eq_blockSchur_partProd` + `reindex_prod_eq_partProd`.
- `deepestM_eq_chainWidth_sub`, `deepestM_zero_eq_chainWidth_sub`, `ring_inverse_eq_nonsing_inv` — thin
  width-cast + `Ring.inverse → ⁻¹` helpers.

## Route (all banked except the four bridges above)

`prod (deepestM H r) C` →(fold bridge `reindex_prodAux_deepestM_eq_prodSchurCore` + chain-lock)→
`(blockSchur (reindex (rThr 0)(deepestChainCol L)(prod (decode x)))).submatrix …` →(pivot-front column
reconciliation `pivotFront_toBlocks·_eq_chainCol` at `J = frontEmbed` via `pivotThresholdSplit_frontEmbed`
+ `Ring.inverse → ⁻¹`)→ the unframed Schur over `pivotThr J` →(`score_eq_unframedSchur_prodDecode_gen`,
frame-strip + `−B` corner)→ `ScoreIntegrand x`.

## Notes for the controller

- Wire: `import DLNFibre.DLN.RLCT.Validate.DeepestSchurScoreTelescopeGen` (end of `DLNFibre.lean`); add
  `prod_deepestM_eq_schur_ldu_readback_gen` to `AxCheck.lean`.
- The `hsub4core` germ of `deepest_diffeo_bridge_gen_assembled` is reached from this telescope the way the
  L=2 `hsub4core_conj_germ` reaches it from `prod_deepestM_eq_schur_ldu_readback`: via a per-`x` keystone
  (`deepestCoreF_coreAbsorbConj_eq_prodSchur` → `frobSqMat`(this telescope) → `Score x`) + a neighbourhood
  peel. Those two (keystone + peel) are the compose, and they DO touch Producer-1-adjacent continuity
  (`psiSplitRawGen` `ContinuousAt` + the near-deepest-point unit germs) + the general readback dictionary.
- Build discipline: force-recompiled green (`touch` + `scripts/lb`); forced `#print axioms` clean-three; no
  sibling name clashes (`rg`-checked). `hstep2:1060` left UNTOUCHED (not laundered).
- The verbose 12+-hypothesis signatures carry some long lines (`linter.style.longLine`, inherent to
  mirroring the L=2 template's signature; non-blocking). No errors / unused-variable warnings from the module.
