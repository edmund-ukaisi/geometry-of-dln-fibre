import DLNFibre.DLN.RLCT.Validate.DeepestGaugeConstruction
import DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeL2

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestL2Wiring` — the L=2 final-wiring top file (R-A home)

**Why this file exists (the import-cycle resolution, R-A).** The L=2 diffeo-bridge ASSEMBLY
`deepest_diffeo_bridge_L2_impl` lives in `DeepestDiffeoBridgeL2.lean`, which *imports*
`DeepestGaugeConstruction.lean` (it needs `endpointP0`/`deepestEFull`/`endpoint_telescoping_eq`/…). So the
public bridge `deepest_diffeo_bridge_L2` (the one the gauge construction consumes) and `_impl` cannot live
in the same file as each other in dependency order — the public bridge must sit ABOVE both. This file is
that top home: it imports BOTH and provides the thin public bridge as `exact _impl …` plus the producer-side
discharge of the four extra hypotheses `_impl` needs (`hPtri`/`hQtri` block-triangularity + `hsub3reg`/
`hsub4core`).

**STATUS: SPEC-FIRST SCAFFOLD.** This step (#149) wires `deepest_diffeo_bridge_L2_wired` = a thin
forward to `deepest_diffeo_bridge_L2_impl`, taking the four extra hypotheses as INPUTS. The forwarding
typechecks, pinning the obligation shape. The discharge of those four inputs — and the relocation of the
consumers (`deepest_gauge_construction` etc.) here — follows once the upstream producer-frame
triangularization lands (`deepestPoint_frame_pivot_exists` emitting block-LOWER layer-0 / block-UPPER
layer-(L−1) frames, the constructed-frame route (b); the producer Score never enters, so no
gauge-invariance lemma is needed — Codex-confirmed,
`threads/31-pin2-comparability/codex/l2wire-gauge-invariance-answer.md`).

**Scope: L = 2** (`hL2eq : L = 2`). The L ≥ 3 interior/grouped-diffeo gaps stay in `DeepestGaugeConstruction`.

**Aggregator note (R-A discipline):** this file is added to the WORKING-branch aggregator copy only; the
canonical `DLNFibre.lean` is reconciled at operator promotion. `deepest_regular_core_normal_form_of` (the
Skeleton-facing piece) stays importable.
-/

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The L=2 public diffeo bridge, WIRED** (R-A). Thin forward to the sorry-free assembly
`deepest_diffeo_bridge_L2_impl`. Same conclusion as the gauge file's `deepest_diffeo_bridge_L2`
(DeepestGaugeConstruction:2853), but with the soundness-amendment hypotheses `hPtri`/`hQtri` (endpoint
block-triangularity) and the two per-`x` discharges `hsub3reg`/`hsub4core` exposed as inputs — supplied
by the caller (`deepest_gauge_construction`) from the triangular producer frames. Supersedes the gauge
file's 2853 `sorry`; the consumer call-site re-points here under R-A. -/
theorem deepest_diffeo_bridge_L2_wired (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPtri : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
        (endpointP0 H hL Pf)).toBlocks₁₂ = 0)
    (hQtri : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointQL H hL Qf)).toBlocks₂₁ = 0)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsub3reg : ∀ x : Fin (flatDim H) → ℝ,
      (∑ i, (deepestEFull H r hr hL J Pf Qf (psiSplitRawL2 H r hr hL (split x)) i) ^ 2)
        = ∑ i, (deepestEFull H r hr hL J Pf Qf (split x) i) ^ 2)
    (coreAbsorb : DeepestSplit H r (deepestNGauge H r) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (hregval : ∀ q : DeepestSplit H r (deepestNGauge H r),
      (regStraighten q).1 = deepestEFull H r hr hL J Pf Qf q)
    (hcoreabs : coreAbsorb = deepestCoreAbsorb H r hr hL)
    (Score : (Fin (flatDim H) → ℝ) → ℝ)
    (hScoreDef : Score = fun w => ∑ i, ∑ j, (((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
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
                * endpointQL H hL Qf)).toBlocks₁₂) i j) ^ 2)
    (hsub4core : ∀ x : Fin (flatDim H) → ℝ,
      deepestCoreF H r (deepestCoreAbsorb H r hr hL (psiSplitRawL2 H r hr hL (split x))).2.1 = Score x)
    (Φscore : (Fin (flatDim H) → ℝ) → ℝ)
    (hΦscore : Φscore = fun x => (∑ i, (regStraighten (split x)).1 i ^ 2) + Score x)
    (wstar : Fin (flatDim H) → ℝ)
    (hwstar : wstar = (paramsEquivFlat H) (deepestPoint H r B hB hr hL))
    (hL2eq : L = 2) :
    rlctAtOn Φscore wstar
      = rlctAtOn
          (fun x : Fin (flatDim H) → ℝ =>
            (∑ i, (regStraighten (split x)).1 i ^ 2)
              + deepestCoreF H r (coreAbsorb (split x)).2.1)
          ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) :=
  deepest_diffeo_bridge_L2_impl H r B hB hr hL hL2 hpos J hJfront Pf Qf hPtri hQtri split hsub3reg
    coreAbsorb regStraighten hsplit hregval hcoreabs Score hScoreDef hsub4core Φscore hΦscore wstar
    hwstar hL2eq

end DLNFibre.DLN.RLCT
