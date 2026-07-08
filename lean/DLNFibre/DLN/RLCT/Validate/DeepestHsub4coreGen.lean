import DLNFibre.DLN.RLCT.Validate.DeepestSchurScoreTelescopeGen
import DLNFibre.DLN.RLCT.Validate.DeepestSchurShiftConj
import DLNFibre.DLN.RLCT.Validate.DeepestChainUnitGerm

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestHsub4coreGen` — the general-`L` `hsub4core` per-`x` keystone

(#120 `hstep2`, item 3.) The general-`L` analog of the L=2 per-`x` keystone
`deepestCoreF_coreAbsorbConj_psiSplitRawL2CoreConj_eq_score_at_chart` (`DeepestDiffeoBridgeL2Conj`):
at a chart point the conjugated absorbed-core energy of the moved point `psiSplitRawGen (split x)`
equals the wire's bare Score (the framed `(1,1)`-Schur frobenius of
`endpointP0·(prod(decode x)−B)·endpointQL`).

## The keystone (the Producer-1-FREE composition, sorry-free here)

`deepestCoreF_coreAbsorbConj_psiSplitRawGen_eq_score_at_chart` chains two banked general-`L` bricks:

* `deepestCoreF_coreAbsorbConj_eq_prodSchur` (`DeepestSchurShiftConj`) — GIVEN `hq` (the moved point
  in the cutoff inner ball), strips the cutoff to the raw Schur correction: `deepestCoreF
  (coreAbsorbConj q').2.1 = frobSqMat (prod (deepestM) (fun s => decode(q'.2.1) s + corr s))`;
* `prod_deepestM_eq_schur_ldu_readback_gen` (`DeepestSchurScoreTelescopeGen`, Producer 3, BANKED) —
  GIVEN the per-layer readback `hC` (each reduced-core layer reads as a moved Schur core `blockSchur
  (movedC …)`), the chain-invertibility `hLayer`/`hPart`, and the frames, `prod (deepestM) C =
  <Score integrand>`.

Stated at the specificity the L=2 template used, with the readback `hC` and the chain/frame
invertibility carried as EXPLICIT hypotheses (the coupled algebraic bulk — the general core-side
move readback dictionary — is a separate reduction, not laundered here). It uses only the
already-defined concrete `psiSplitRawGen`/`schurCorrectionConj` algebra: no `psiSplitRawGen`
continuity, no `psiSplitRawGen 0 = 0`, no diffeo triple.

## What is NOT here — the Producer-1 sequencing (`HONEST-PARTIAL`, WATCH-flagged)

The FULL germ `∀ᶠ x, deepestCoreF (coreAbsorbConj (psiSplitRawGen (split x))).2.1 = Score x` (the
`hsub4core` hypothesis of `deepest_diffeo_bridge_gen_assembled`) additionally needs the cutoff-ball
`hq` peeled over a NEIGHBOURHOOD of the basepoint — i.e. `∀ᶠ x, psiSplitRawGen (split x) ∈
closedBall 0 (cutoffBumpConj …).rIn`. That germ needs `Tendsto (fun x => psiSplitRawGen (split x))
(𝓝 base) (𝓝 0)` (equivalently `psiSplitRawGen 0 = 0` + continuity at the basepoint). The value part
`psiSplitRawGen 0 = 0` IS now banked (`psiSplitRawGen_zero`, `DeepestPsiHraw0Gen`); the remaining
**Producer-1** blocker is CONTINUITY of `psiSplitRawGen` at the basepoint. So the full germ
**sequences after Producer 1's continuity**, unlike the cutoff-free reg germ `hsub3reg_gen_germ` (whose
identity is pointwise-algebraic). This asymmetry (the core side carries the cutoff, the reg side does
not) is the WATCH finding of this thread; Codex-corroborated (xhigh). The germ closes as a small
assembly once Producer 1 supplies the eventual-ball (continuity) and `hC` is discharged (the general
core-side move readback, new math); the decode-chain invertibility germs have LANDED
(`DeepestHsub4coreInvGerm`: `eventually_isUnit_deepestChain_decode_toBlocks₁₁` etc.).
-/

open MeasureTheory Topology Matrix
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The general-`L` `hsub4core` per-`x` keystone.** At a chart point, the conjugated absorbed-core
energy of the moved point `psiSplitRawGen … q` equals the wire's bare `Score x` (the framed
`(1,1)`-Schur frobenius of `endpointP0·(prod(decode x)−B)·endpointQL`). Chains
`deepestCoreF_coreAbsorbConj_eq_prodSchur` (cutoff-strip, GIVEN `hq`) with the banked Producer-3
telescope `prod_deepestM_eq_schur_ldu_readback_gen` (GIVEN the readback `hC`, the
chain-invertibility `hLayer`/`hPart`, and the frames). Mirrors the landed L=2
`..._eq_score_at_chart`. The
coupled core-side move readback dictionary (`hC`) and the invertibility are carried as explicit
hypotheses (the honest reduction, NOT laundered). Producer-1-free. -/
theorem deepestCoreF_coreAbsorbConj_psiSplitRawGen_eq_score_at_chart (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r))
    (x : Fin (flatDim H) → ℝ)
    (hq : psiSplitRawGen H r hr hL J Pf Qf q
      ∈ Metric.closedBall (0 : DeepestSplit H r (deepestNGauge H r))
        ((cutoffBumpConj H r B hB hr hL hDA).rIn))
    (hPtri : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
        (endpointP0 H hL Pf)).toBlocks₁₂ = 0)
    (hQtri : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointQL H hL Qf)).toBlocks₂₁ = 0)
    (hP22 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
        (endpointP0 H hL Pf)).toBlocks₂₂ = 1)
    (hQ22 : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointQL H hL Qf)).toBlocks₂₂ = 1)
    (hS3b : Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointP0 H hL Pf * B * endpointQL H hL Qf)
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (hP11inv : Invertible (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (rThresholdSplit r (H 0) (hr 0)) (endpointP0 H hL Pf)).toBlocks₁₁)
    (hQ11inv : Invertible (Matrix.reindex
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointQL H hL Qf)).toBlocks₁₁)
    (hMid11inv : Invertible (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (prod H ((paramsEquivFlat H).symm x))).toBlocks₁₁)
    (hC : ∀ s : Fin L,
      Matrix.reindex (finCongr (chainWidth_castSucc_sub H r s))
          (finCongr (chainWidth_succ_sub H r s))
          ((paramsEquivFlat (deepestM H r)).symm (psiSplitRawGen H r hr hL J Pf Qf q).2.1 s
            + schurCorrectionConj H r B hB hr hL
                ((psiSplitRawGen H r hr hL J Pf Qf q).1,
                  (psiSplitRawGen H r hr hL J Pf Qf q).2.2) s)
        = blockSchur (movedC (deepestChain H r hr ((paramsEquivFlat H).symm x))
            (Z0edit0 (deepestChain H r hr ((paramsEquivFlat H).symm x)) L) (s : ℕ)))
    (hLayer : ∀ k, k < L →
      Invertible (deepestChain H r hr ((paramsEquivFlat H).symm x) k).toBlocks₁₁)
    (hPart : ∀ k, k ≤ L →
      Invertible (partProd (deepestChain H r hr ((paramsEquivFlat H).symm x)) k).toBlocks₁₁)
    (Score : (Fin (flatDim H) → ℝ) → ℝ)
    (hScoreDef : Score = fun w => frobSqMat ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm w) - B)
            * endpointQL H hL Qf)).toBlocks₂₂
        - (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm w) - B)
              * endpointQL H hL Qf)).toBlocks₂₁
          * ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm w) - B)
                * endpointQL H hL Qf)).toBlocks₁₁ + 1)⁻¹
          * (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm w) - B)
                * endpointQL H hL Qf)).toBlocks₁₂)) :
    deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA
        (psiSplitRawGen H r hr hL J Pf Qf q)).2.1 = Score x := by
  rw [deepestCoreF_coreAbsorbConj_eq_prodSchur H r B hB hr hL hDA
      (psiSplitRawGen H r hr hL J Pf Qf q) hq, hScoreDef]
  exact congrArg frobSqMat (prod_deepestM_eq_schur_ldu_readback_gen H r B hB hr hL J hJfront Pf Qf
    hPtri hQtri hP22 hQ22 x hS3b hP11inv hQ11inv hMid11inv _ hC hLayer hPart)

end DLNFibre.DLN.RLCT
