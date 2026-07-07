# Statement cards — genm-hstep2chain

## `Kcoup_zero` (delivered, sorry-free)

> **Claim.** For the abstract framed chain `C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s+1)) α`, the zeroth
> off-pivot coupling vanishes: `Kcoup C 0 = 0`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.Kcoup_zero`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurRecursion.lean` @ branch `genm-hstep2chain`, SHA
>   pending push) — with helper `DLNFibre.DLN.RLCT.toBlocks₁₂_one`.
> - **Gloss.** `Kcoup C k = (C k).toBlocks₂₁ * Ring.inverse (partProd C (k+1)).toBlocks₁₁ *
>   (partProd C k).toBlocks₁₂`; at `k = 0`, `partProd C 0 = 1` and `(1).toBlocks₁₂ = 0`, so the right
>   factor is `0`, hence `Kcoup C 0 = 0`.
> - **Proved.** `Kcoup C 0 = 0` for every `C` (no invertibility, no chain hypotheses); over any `CommRing α`.
> - **Assumed.** none (beyond the ambient `[Fintype r] [DecidableEq r]`, `[∀ i, DecidableEq (m i)]`).
> - **Cited.** none.
> - **Deferred.** none for this lemma.
> - **Consequence (why it matters).** Makes the `coreProd` front factor `1 − Kcoup C 0 = 1`, so
>   `coreProd C L = S_0·(1−K_1)·S_1·…·(1−K_{L-1})·S_{L-1}` and the per-layer product
>   `∏_s (1−K_s)·S_s` telescopes to `coreProd C L`. Reusable by any chain-based route (naive OR conjugate).
> - **Status.** sorry-free.

## `blockSchur (partProd C L) = ScoreSchur` — the LOCKED chain (characterised, NOT yet in Lean)

> **Claim.** The general-`L` Schur-product identity: for the HONEST reindexed-decode chain
> `Ĉ_s = reindex_{rThresholdSplit r (H s.castSucc), rThresholdSplit r (H s.succ)} (decode layer s)`
> (`(1,1)`-pivot `deepBlkA_s + gaugeReadX_s`, NOT the naive `1 + gaugeReadX_s`),
> `blockSchur (partProd Ĉ L) = ScoreSchur x` where `ScoreSchur x = blockSchur(reindex(prod(decode x)))`
> (the unframed Schur of the reindexed network product).
>
> - **Lean:** NOT built (deferred — see Deferred). The building blocks are all banked:
>   `schur_product_ldu_rec`, `reindex_mul_split`/`reindex_mul_fromBlocks`, `blockSchur_partProd_succ`
>   (`DeepestSchurRecursion`/`DeepestBlockDecomp`).
> - **Gloss.** The abstract chain product `partProd Ĉ L` telescopes to `reindex(prod(decode x))` (each
>   `Ĉ_s = reindex(decode_s)`; `reindex_mul_split`), so `blockSchur(partProd Ĉ L) =
>   blockSchur(reindex(prod decode)) = coreProd Ĉ L` (`schur_product_ldu_rec`) `= ScoreSchur`.
> - **Proved.** numerically (`codex/chain_lock_check.py`, check #1: `coreProd == ScoreSchur`, True).
> - **Cited.** none.
> - **Deferred.** (i) the `Fin L ↔ ℕ`/`castSucc`/`succ` cast resolution of the ℕ-indexed chain `Ĉ` +
>   `partProd Ĉ L = reindex(prod decode)`; (ii) the frame-strip/corner to the FRAMED `Score` via banked
>   `schur_frame_transform` + `rcore_eq_schur_of_corner_split`. **Deferred deliberately** because its
>   direct consumer — a Step-Ψ_conj (conjugate-core) bridge — does not exist and needs a controller
>   re-architecture decision (see thread.md). Building it now would sit on an unbuilt consumer.
> - **Status.** characterised + numerically certified; not in Lean.

## `huntwist` (the germ) — FALSE as stated (STOP finding)

> **Finding.** `huntwist : deepestCoreF (deepestPsiCoreShear K (deepestCoreAbsorb (split x))).2.1 =
> Score x` — the germ the banked `deepest_diffeo_bridge_gen_impl` reduces `hstep2` to — is UNSATISFIABLE
> for every admissible coupling `K` (`K_s 0 = 0`, continuous). The reduction huntwist+hreginv ⟹ hstep2
> is a *faithful implication* (reviewer-verified), but a *sufficient* condition that cannot be met.
>
> - **Reason.** `deepestCoreAbsorb` is NAIVE (cores `S^naive = T−Z(1+X)⁻¹Y`, banked
>   `deepestCoreF_coreAbsorb_eq_prodSchur`); `Score` needs HONEST cores `S^conj` (pivot `deepBlkA+X`);
>   the per-layer left-shear `Ψ: S ↦ (1−K)S` with `K(0)=0` (`(1−K)=1+o(1)`) cannot change the leading
>   germ, and `S^naive ≠ S^conj` at first order (`deepBlkA ≠ 1`).
> - **Evidence.** numerical (0.1816, 0.2119 ≠ Score 0.0651), repo L2 docstring (`DeepestSchurShiftConj:33`),
>   Codex xhigh (0.9 confidence). See thread.md.
> - **Status.** finding — do NOT build the germ on this bridge.
