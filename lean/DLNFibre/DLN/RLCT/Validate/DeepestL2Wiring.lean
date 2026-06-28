import DLNFibre.DLN.RLCT.Validate.DeepestGaugeConstruction
import DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeL2
import DLNFibre.DLN.RLCT.Validate.DeepestPivotFrameTriangular
import DLNFibre.DLN.RLCT.Validate.DeepestLDUReadback

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

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology

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
    (hsub3reg : ∀ᶠ x : (Fin (flatDim H) → ℝ) in
        nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
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
    (hsub4core : ∀ᶠ x : (Fin (flatDim H) → ℝ) in
        nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
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


theorem deepest_gauge_construction (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    -- The strict reduced-width positivity the headline carries (`0 < M s ⟺ r < H s`); needed for the
    -- endpoint conjugation-constant positivity (`0 < ∑P0²·∑QL²`) in the loss squeeze. (Threaded from the
    -- consumer `deepest_gauge_squeeze_exists`, which holds it via the headline's `hpos`.)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    -- **FRONT-PIVOT HYPOTHESIS (B (front-pivot WLOG), b-wlog-spec, 2026-06-25).** The `B`-determined
    -- pivot set of `deepestPoint_frame_pivot_exists` is the FRONT embedding `k ↦ k` — i.e. `B`'s rank-`r`
    -- pivot columns are the first `r`. This is what makes the loss-squeeze's (b)-conjunct EXACT (the
    -- producer's `∑deepestEFull² = Sreg`, no `δ₁, δ₂` comparability, no germ/Taylor atom). The caller
    -- (`deepest_gauge_squeeze_exists`, the WLOG seam) discharges it by running the chart at `B·Π`, where
    -- `Π` brings `B`'s pivots to the front and the headline's `⨅ optimalSet` is invariant (b-wlog-spec
    -- lemmas 1-5). Stated about the bundle's `.choose` (the pivot `Jb` the body uses).
    (hJfront : ((deepestPoint_frame_pivot_exists H r B hB hr hL hL2).choose).trans
        (finCongr (H_lastLayer_succ H hL)).toEmbedding = frontEmbed H r hr)
    -- **ROW-ALIGNMENT (htop, the row-WLOG dual of hJfront, S2).** `B`'s top `r` rows are full rank —
    -- the `[Invertible A11]` source (`deepestPoint_leadingBlock_isUnit`) for the layer-0 block-LOWER
    -- endpoint frame the L=2 diffeo bridge needs. Threaded as a hypothesis (parallel to hJfront); the
    -- headline discharges it by the banked row-permutation WLOG (`rlct_infimum_rowPerm_eq`).
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r) :
    ∃ (nGauge : ℕ) (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r nGauge)
      (coreAbsorb : DeepestSplit H r nGauge ≃ₜ DeepestSplit H r nGauge)
      (regStraighten : DeepestSplit H r nGauge → DeepestSplit H r nGauge),
      MeasurePreserving split volume volume ∧
      split ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) = 0 ∧
      coreAbsorb 0 = 0 ∧
      (∀ q : DeepestSplit H r nGauge, (coreAbsorb q).1 = q.1) ∧
      (∀ q : DeepestSplit H r nGauge, (coreAbsorb q).2.2 = q.2.2) ∧
      rlctAtOn
          (fun q : DeepestSplit H r nGauge => (∑ i, q.1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
          (0 : DeepestSplit H r nGauge)
        = rlctAtOn
            (fun q : DeepestSplit H r nGauge => (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
            (0 : DeepestSplit H r nGauge) ∧
      Continuous regStraighten ∧
      regStraighten 0 = 0 ∧
      (∀ q : DeepestSplit H r nGauge, (regStraighten q).2.1 = q.2.1) ∧
      (∀ q : DeepestSplit H r nGauge, (regStraighten q).2.2 = q.2.2) ∧
      rlctAtOn
          (fun q : DeepestSplit H r nGauge =>
            (∑ i, (regStraighten q).1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
          (0 : DeepestSplit H r nGauge)
        = rlctAtOn
            (fun q : DeepestSplit H r nGauge =>
              (∑ i, q.1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
            (0 : DeepestSplit H r nGauge) ∧
      -- **The `loss_squeeze` slot — RLCT-EQUALITY form** (route-B migration, matches the migrated
      -- `DeepestGaugeChart.loss_squeeze` field): `rlctAt(dlnLoss) = rlctAtOn(Sreg_E + coreΦ)`.
      rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
        = rlctAtOn
            (fun x : Fin (flatDim H) → ℝ =>
              (∑ i, (regStraighten (split x)).1 i ^ 2)
                + deepestCoreF H r (coreAbsorb (split x)).2.1)
            ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) := by
  -- `split` (obligation (i), MP reindex carrying the deepest point to `0`). Use the CONCRETE
  -- `deepestSplit` witness (not the `deepestSplit_exists` existential) so the PIN2 cert's round-trip
  -- hypothesis `hsplit` discharges by `rfl` — the index-decode lemmas (`readX/Y/Z_deepestSplit`,
  -- `DeepestSplitConcrete`) are stated against THIS map, so generality of `split` would block them.
  set split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r) :=
    deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) with hsplit_def
  have hsplit_mp_base :=
    deepestSplit_mp_basepoint H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL))
  have hsplit_mp : MeasurePreserving split volume volume := hsplit_mp_base.1
  have hsplit_base : split ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) = 0 :=
    hsplit_mp_base.2
  have hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w :=
    fun _ => rfl
  -- The PIVOT-ALIGNED per-layer gauge frame family + the `B`-determined pivot set `Jb` (banked
  -- `deepestPoint_frame_pivot_exists`). The first/interior arms are the threshold `deepestPoint_frame`;
  -- the LAST-layer arm is the pivot frame (with a UNIT `B22` block — the PIN1 input). `split` stays
  -- frameless/MP; the READING side carries this family (#80 frame-wiring).
  -- **The block-TRIANGULAR pivot bundle (S2, hPtri/hQtri source).** Obtain the triangular frame family
  -- (block-LOWER layer-0 / block-UPPER layer-1) from `deepestPoint_frame_pivot_triangular_exists` — it
  -- carries the SAME conclusions as the producer bundle PLUS `hJtri` (front-embed identity, from
  -- `hJfront`), `hPtri`, `hQtri`. The frame facts the body consumes are frame-generic, so the switch is a
  -- drop-in; `hPtri`/`hQtri` feed the L=2 diffeo bridge.
  obtain ⟨Jb, Pf, Qf, hJtri, hPunit, hQunit, hQf0, hPfL, hNF, hQf22b, hcorner, hPtri, hQtri,
      hP22one, hQ22one⟩ :=
    deepestPoint_frame_pivot_triangular_exists H r B hB hr hL hL2 htop hJfront
  -- The outer-reindex pivot embedding lives on `Fin (H (Fin.last L))`; `Jb` on `Fin (H (lastLayer).succ)`.
  -- The cast bridge (`H_lastLayer_succ`); `pivotJSucc J = Jb` (the two `finCongr` round-trip).
  set J : Fin r ↪ Fin (H (Fin.last L)) :=
    Jb.trans (finCongr (H_lastLayer_succ H hL)).toEmbedding with hJ
  -- The body's `J` IS the front embedding (`hJtri`, the triangular bundle's front-embed identity).
  have hJfront' : J = frontEmbed H r hr := by rw [hJ]; exact hJtri
  have hpivJ : pivotJSucc H r hL J = Jb := by
    apply Function.Embedding.ext; intro k
    simp only [hJ, pivotJSucc, Function.Embedding.trans_apply, Equiv.coe_toEmbedding, finCongr_apply]
    rfl
  -- The boundary frame units + boundary-inner triviality come straight from the bundle.
  have hPf : IsUnit (Pf (firstLayer hL)) := hPunit (firstLayer hL)
  have hQf : IsUnit (Qf (lastLayer hL)) := hQunit (lastLayer hL)
  -- The `B22`-unit fact aligned to `deepestEPivot`'s split (`pivotJSucc J = Jb`).
  have hQf22 : IsUnit ((Matrix.reindex
      (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
      (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
      (Qf (lastLayer hL))).toBlocks₂₂) := by rw [hpivJ]; exact hQf22b
  -- PIN 0: the CONCRETE `coreAbsorb = deepestCoreAbsorb` (the cutoff Schur shear) + its
  -- slot-fix/basepoint/rlct (Option A: concrete, so PIN 2 sees the same map).
  set coreAbsorb := deepestCoreAbsorb H r hr hL with hca_def
  obtain ⟨hca_base, hca_reg, hca_spec, hca_rlct⟩ := deepest_coreAbsorb_exists H r hr hL
  -- PIN 1: `regStraighten = regStraightenOf2 deepestEFull` (the L2-PIN2 FULL-reg straightening; reg-output
  -- reads the core leak, so PIN 2's squeeze matches the loss's `Sreg`). The IFT peel of the
  -- `coreAbsorb.symm`-conjugated `π̃` (Codex option D) feeds `regAbsorb_rlct`; its concrete value feeds
  -- the squeeze.
  -- **REMAINING GAP (one narrow correct-statement `sorry`):** `π̃ := regStraightenOf2 (deepestEFull ∘
  -- coreAbsorb.symm)` is a local diffeo at `0` (ContDiff + invertible strict-deriv `eTilde`). ContDiff is
  -- routine (deepestEFull + coreAbsorb.symm both ContDiff). The invertible strict-deriv needs the
  -- degree-2 core-block-vanishing `∂deepestEFull/∂core(0) = 0` (so `π̃`'s reg-reg block stays PIN1's
  -- invertible `F` despite `coreAbsorb.symm`'s reg→core shear) — the value-fold atom (thread 31, exact;
  -- the leaks `Y0·T1, T0·Z1` are degree-2), parallel to PIN1's `deepestEPivot_regSlice_fderiv`. NOT yet
  -- written (the genuine remaining geometry; the rest of the L2-PIN2 repair is green + sound below).
  have hTilde : ∃ eTilde : DeepestSplit H r (deepestNGauge H r) ≃L[ℝ]
      DeepestSplit H r (deepestNGauge H r),
      ContDiff ℝ (⊤ : ℕ∞)
        (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q))) ∧
      HasStrictFDerivAt (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q)))
        (eTilde : DeepestSplit H r (deepestNGauge H r) →L[ℝ]
          DeepestSplit H r (deepestNGauge H r)) 0 := by
    -- The PIN1 invertible total shear `D_E` and its CLE `e` (`↑e = regStraightenTotalCLM2 D_E`).
    obtain ⟨D_E, e, hsd, he⟩ :=
      deepestEFull_deriv H r hr hL hL2 J Pf Qf hPf hQf hQf0 hPfL hQf22
    -- `coreAbsorb.symm = (coreShearHomeo (schurCutoffShift) …).symm` (PIN0's concrete shear), which is
    -- `ContDiff ⊤` (the cutoff Schur shift is globally smooth — `contDiff_schurCutoffShift`) with strict
    -- derivative `id` at `0` (the degree-2 vanishing `D(shift)(0) = 0`).
    have hcds : ContDiff ℝ (⊤ : ℕ∞) (schurCutoffShift H r hr hL) :=
      contDiff_schurCutoffShift H r hr hL
    have hsymm_cd : ContDiff ℝ (⊤ : ℕ∞)
        (fun q : DeepestSplit H r (deepestNGauge H r) => coreAbsorb.symm q) := by
      rw [hca_def]
      exact contDiff_coreShearHomeo_symm (schurCutoffShift H r hr hL)
        (continuous_schurCutoffShift H r hr hL) hcds
    have hsymm_sd : HasStrictFDerivAt (fun q : DeepestSplit H r (deepestNGauge H r) => coreAbsorb.symm q)
        (ContinuousLinearMap.id ℝ (DeepestSplit H r (deepestNGauge H r))) 0 := by
      rw [hca_def]
      exact hasStrictFDerivAt_coreShearHomeo_symm_zero (schurCutoffShift H r hr hL)
        (continuous_schurCutoffShift H r hr hL) (hasStrictFDerivAt_schurCutoffShift_zero H r hr hL)
    -- The conjugated full-reg straightening input `E_comp := deepestEFull ∘ coreAbsorb.symm`.
    set Ecomp : DeepestSplit H r (deepestNGauge H r) → (Fin (deepestNReg H r) → ℝ) :=
      fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q) with hEcomp
    -- (A) ContDiff: `regStraightenOf2 (Efull ∘ symm)` is `ContDiff ⊤` (both factors are).
    have hEcomp_cd : ContDiff ℝ (⊤ : ℕ∞) Ecomp :=
      (deepestEFull_contdiff H r hr hL J Pf Qf).comp hsymm_cd
    have hcontdiff : ContDiff ℝ (⊤ : ℕ∞) (regStraightenOf2 Ecomp) :=
      contDiff_regStraightenOf2 Ecomp hEcomp_cd
    -- (B) Strict derivative: `D(Efull ∘ symm)(0) = D_E ∘ id = D_E` (chain rule, `D(symm)(0) = id`), so the
    -- total `regStraightenOf2` derivative is `regStraightenTotalCLM2 D_E = ↑e` (`deepestEFull_deriv`).
    have hEcomp_sd : HasStrictFDerivAt Ecomp D_E 0 := by
      -- `coreAbsorb.symm 0 = 0`, so `deepestEFull`'s strict deriv at `0` is at `coreAbsorb.symm 0`.
      have hsymm0 : coreAbsorb.symm (0 : DeepestSplit H r (deepestNGauge H r)) = 0 := by
        conv_lhs => rw [← hca_base]
        rw [coreAbsorb.symm_apply_apply]
      have hsd' : HasStrictFDerivAt (deepestEFull H r hr hL J Pf Qf) D_E
          (coreAbsorb.symm (0 : DeepestSplit H r (deepestNGauge H r))) := by
        rw [hsymm0]; exact hsd
      have hchain := hsd'.comp (x := (0 : DeepestSplit H r (deepestNGauge H r))) hsymm_sd
      -- `hchain : HasStrictFDerivAt (fun x => Efull (symm x)) (D_E.comp id) 0`; `D_E.comp id = D_E`.
      have hchain' : HasStrictFDerivAt Ecomp (D_E.comp
          (ContinuousLinearMap.id ℝ (DeepestSplit H r (deepestNGauge H r)))) 0 := hchain
      rw [ContinuousLinearMap.comp_id] at hchain'
      exact hchain'
    have hreg_sd := hasStrictFDerivAt_regStraightenOf2_gen Ecomp D_E hEcomp_sd
    refine ⟨e, hcontdiff, ?_⟩
    rw [he]
    exact hreg_sd
  obtain ⟨eTilde, hTilde_contdiff, hTilde_deriv⟩ := hTilde
  obtain ⟨regStraighten, hra_cont, hra_base, hra_core, hra_spec, hra_regval, hra_rlct⟩ :=
    deepest_regAbsorb_exists H r B hB hr hL (deepestNGauge H r) coreAbsorb
      (deepestCoreAbsorb_mp H r hr hL) hca_base hca_reg hca_spec
      (deepestEFull H r hr hL J Pf Qf) (deepestEFull_contdiff H r hr hL J Pf Qf)
      (deepestEFull_base H r hr hL hL2 J Pf Qf)
      eTilde hTilde_contdiff hTilde_deriv
  -- The cert's `hcorner` is stated with `pivotJSucc H r hL J`; the bundle's `hcorner` is stated with
  -- `Jb`. `hpivJ : pivotJSucc H r hL J = Jb` bridges them.
  have hcorner' : Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _))
      (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
      ((deepestPoint H r B hB hr hL (lastLayer hL)) * Qf (lastLayer hL))
        = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 := by
    rw [hpivJ]; exact hcorner
  -- The interior-frame-triviality input `endpoint_telescoping` consumes. The single interface of the
  -- L = 2 headline (`s = 0`) is the boundary `(Qf (firstLayer) = 1, Pf (lastLayer) = 1) = (hQf0, hPfL)`.
  -- For L ≥ 3 the strict-interior frames are likewise trivial (the interior deepest layer IS the corner),
  -- but the bundle `deepestPoint_frame_pivot_exists` supplies the GENERIC rank-normal-form frame there
  -- (not committed to the identity), so that arm is a scoped gap (`hinterface_interior` below).
  have hinterface : ∀ (s : Fin L) (_ : (s : ℕ) + 1 < L),
      Qf s = (1 : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) ∧
        Pf ⟨(s : ℕ) + 1, by omega⟩ = (1 : Matrix (Fin (H (⟨(s : ℕ) + 1, by omega⟩ : Fin L).castSucc))
          (Fin (H (⟨(s : ℕ) + 1, by omega⟩ : Fin L).castSucc)) ℝ) := by
    intro s hs
    refine ⟨?_, ?_⟩
    · -- `Qf s = 1`: the left endpoint (`s.val = 0 = firstLayer`) via `hQf0`; interior `1 ≤ s.val` scoped.
      rcases Nat.eq_zero_or_pos (s : ℕ) with hs0 | hspos
      · have hsf : s = firstLayer hL := Fin.ext (by simp [firstLayer, hs0])
        rw [hsf]; exact hQf0
      · -- **SCOPED GAP (L ≥ 3 interior `Qf s`).** Vacuous for the L = 2 headline (`1 ≤ s.val ∧ s+1 < 2`
        -- is empty). For L ≥ 3 the interior deepest layer is the corner (`deepestPoint_interior_eq_corM`)
        -- but the bundle's frame there is the GENERIC rank-normal-form, not committed to the identity —
        -- closing this needs the bundle to choose identity interior frames (`DeepestPivotFrame`, off-tide).
        sorry
    · -- `Pf (s+1) = 1`: the right endpoint (`s+1 = L-1 = lastLayer`) via `hPfL`; interior scoped.
      rcases Nat.lt_or_ge ((s : ℕ) + 1) (L - 1) with hint | hbdy
      · -- **SCOPED GAP (L ≥ 3 interior `Pf (s+1)`).** Vacuous for L = 2 (`s+1 < L-1 = 1` is empty). Same
        -- bundle-choice obstruction as the interior `Qf s` arm.
        sorry
      · have hsf : (⟨(s : ℕ) + 1, by omega⟩ : Fin L) = lastLayer hL :=
          Fin.ext (by simp only [lastLayer]; omega)
        rw [hsf]; exact hPfL
  -- Assemble the bundle: all data (`split`, `coreAbsorb`, `regStraighten` + their facts) is in scope;
  -- the final `?_` is the migrated `loss_squeeze` RLCT-equality (the route-B close below).
  refine ⟨deepestNGauge H r, split, coreAbsorb, regStraighten, hsplit_mp, hsplit_base, hca_base,
    hca_reg, hca_spec, hca_rlct, hra_cont, hra_base, hra_core, hra_spec, hra_rlct, ?_⟩
  -- PIN 2: the loss squeeze (ROUTE-B close, `coreΦ → Score`, 2026-06-25). The migrated `loss_squeeze`
  -- field is the RLCT-EQUALITY `rlctAt(dlnLoss) = rlctAtOn(Sreg_E + coreΦ)`. We prove it from the TRUE
  -- Score-sandwich `hsq` (`deepest_loss_squeeze`, axiom-clean) via `rlctAtOn_squeeze`
  -- (⟹ `rlctAtOn(Sreg_E + Score)`) + the analytic-unit diffeo bridge `rlctAtOn(Sreg_E + Score) =
  -- rlctAtOn(Sreg_E + coreΦ)` (`Ψ : S1 ↦ (I−K)·S1`). `Score = frobSq(Rcore)` (the `hscore`/`hScoreDef`
  -- lambda); `coreΦ = deepestCoreF (coreAbsorb …)`.
  set Score : (Fin (flatDim H) → ℝ) → ℝ :=
    fun w => ∑ i, ∑ j, (((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
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
                * endpointQL H hL Qf)).toBlocks₁₂) i j) ^ 2 with hScoreDef
  obtain ⟨c₁, c₂, hc₁, hc₂, U, hU, hsq⟩ :=
    deepest_loss_squeeze H r B hB hr hL hL2 hpos J hJfront' Pf Qf split coreAbsorb regStraighten
      hsplit_base hsplit hra_regval hca_def Score (fun _ => rfl)
      hPunit hQunit hQf0 hPfL hNF hcorner' hinterface
  -- **ROUTE-B CLOSE (2026-06-25).** Target: `rlctAt(dlnLoss) = rlctAtOn(Sreg_E + coreΦ)` (the migrated
  -- field). TWO steps: (1) `rlctAt(dlnLoss) = rlctAtOn(Sreg_E + Score)` — the TRUE Score-sandwich `hsq`
  -- fed to `rlctAtOn_squeeze` after the Params→flat MP transport; (2) the diffeo bridge
  -- `rlctAtOn(Sreg_E + Score) = rlctAtOn(Sreg_E + coreΦ)` via `Ψ : S1 ↦ (I−K)·S1` (`rlctAtOn_comp_localDiffeo`).
  set Φscore : (Fin (flatDim H) → ℝ) → ℝ :=
    fun x => (∑ i, (regStraighten (split x)).1 i ^ 2) + Score x with hΦscore
  set Φcore : (Fin (flatDim H) → ℝ) → ℝ :=
    fun x => (∑ i, (regStraighten (split x)).1 i ^ 2)
      + deepestCoreF H r (coreAbsorb (split x)).2.1 with hΦcore
  set wstar := (paramsEquivFlat H) (deepestPoint H r B hB hr hL) with hwstar
  -- **Step 1: `rlctAt(dlnLoss) = rlctAtOn Φscore wstar`** (Params→flat MP transport + `rlctAtOn_squeeze`
  -- on the TRUE Score-sandwich `hsq`).
  have hstep1 : rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
      = rlctAtOn Φscore wstar := by
    rw [← rlctAtOn_eq_rlctAt]
    set e : Params H ≃ₜ (Fin (flatDim H) → ℝ) :=
      ⟨(paramsEquivFlat H).toEquiv, continuous_paramsEquivFlat H, continuous_paramsEquivFlat_symm H⟩
      with he
    have hmp : MeasurePreserving e (volume : Measure (Params H)) volume :=
      measurePreserving_paramsEquivFlat H
    have hemb : MeasurableEmbedding e := (paramsEquivFlat H).measurableEmbedding
    have htrans := rlctAtOn_comp_homeomorph e hmp hemb
      (fun x : Fin (flatDim H) → ℝ => dlnLoss H B ((paramsEquivFlat H).symm x))
      (deepestPoint H r B hB hr hL)
    have hcomp : (fun A : Params H => dlnLoss H B ((paramsEquivFlat H).symm (e A)))
        = fun A : Params H => dlnLoss H B A := by
      funext A; congr 1; exact (paramsEquivFlat H).symm_apply_apply A
    rw [hcomp] at htrans
    have he_deepest : e (deepestPoint H r B hB hr hL) = wstar := rfl
    rw [he_deepest] at htrans
    rw [htrans]
    refine rlctAtOn_squeeze (fun x => dlnLoss H B ((paramsEquivFlat H).symm x)) Φscore wstar
      ((continuous_dlnLoss H B).comp (continuous_paramsEquivFlat_symm H)).measurable ?_
      c₁ c₂ hc₁ hc₂ ⟨U, hU, fun w hw => ?_⟩
    · -- `Φscore` measurable: reg sum-of-squares + `Score` (a frobSq of a continuous matrix in `w`).
      rw [hΦscore, hScoreDef]
      apply Measurable.add
      · exact (Finset.measurable_sum _ (fun i _ =>
          ((measurable_pi_apply i).comp
            (continuous_fst.comp (hra_cont.comp split.continuous)).measurable).pow_const _))
      · -- **MEASURABILITY of `Score` (mechanical, entrywise).** `Score w = frobSq(Schur(Mw w))`,
        -- `Mw w = reindex(endpointP0·(prod(symm w)−B)·endpointQL)` — CONTINUOUS in `w` (`continuous_Mw`).
        -- The only non-continuous piece is `(Mw₁₁+1)⁻¹`, but it is MEASURABLE entrywise: `inv_def` gives
        -- `A⁻¹ = (Ring.inverse A.det) • A.adjugate`, with `Continuous.matrix_det`/`Continuous.matrix_adjugate`
        -- continuous and `Ring.inverse : ℝ → ℝ` measurable. So each Schur-leak entry is measurable
        -- (∑∑ of products of measurable scalars), and `frobSq` (finite ∑∑ of squares) is measurable.
        set Mw : (Fin (flatDim H) → ℝ) →
            Matrix (Fin r ⊕ Fin (H 0 - r)) (Fin r ⊕ Fin (H (Fin.last L) - r)) ℝ :=
          fun w => Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm w) - B) * endpointQL H hL Qf)
          with hMw_def
        have hMw_cont : Continuous Mw :=
          continuous_Mw H r B (endpointP0 H hL Pf) (endpointQL H hL Qf)
            (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        -- entrywise measurability bricks (all from `continuous_Mw` + `inv_def`).
        have hElem : ∀ p q, Measurable (fun w => (Mw w) p q) :=
          fun p q => (hMw_cont.matrix_elem p q).measurable
        have hb22 : ∀ (i : Fin (H 0 - r)) (j : Fin (H (Fin.last L) - r)),
            Measurable (fun w => (Mw w).toBlocks₂₂ i j) := by
          intro i j; simpa [Matrix.toBlocks₂₂] using hElem (Sum.inr i) (Sum.inr j)
        have hb21 : ∀ (i : Fin (H 0 - r)) (k : Fin r),
            Measurable (fun w => (Mw w).toBlocks₂₁ i k) := by
          intro i k; simpa [Matrix.toBlocks₂₁] using hElem (Sum.inr i) (Sum.inl k)
        have hb12 : ∀ (l : Fin r) (j : Fin (H (Fin.last L) - r)),
            Measurable (fun w => (Mw w).toBlocks₁₂ l j) := by
          intro l j; simpa [Matrix.toBlocks₁₂] using hElem (Sum.inl l) (Sum.inr j)
        have hb11cont : Continuous (fun w => (Mw w).toBlocks₁₁ + 1) := by
          apply Continuous.add _ continuous_const
          exact continuous_matrix fun p q => hMw_cont.matrix_elem (Sum.inl p) (Sum.inl q)
        have hInv : ∀ (k l : Fin r), Measurable (fun w => ((Mw w).toBlocks₁₁ + 1)⁻¹ k l) := by
          intro k l
          have h2 : (fun w => ((Mw w).toBlocks₁₁ + 1)⁻¹ k l)
              = fun w => Ring.inverse ((Mw w).toBlocks₁₁ + 1).det
                  * ((Mw w).toBlocks₁₁ + 1).adjugate k l := by
            funext w; rw [Matrix.inv_def]; simp [Matrix.smul_apply, smul_eq_mul]
          rw [h2]
          refine Measurable.mul ?_ (hb11cont.matrix_adjugate.matrix_elem k l).measurable
          have hri : Measurable (Ring.inverse : ℝ → ℝ) := by
            rw [Ring.inverse_eq_inv']; exact measurable_inv
          exact hri.comp hb11cont.matrix_det.measurable
        -- assemble: ∑ i ∑ j (Schur-leak entry)².
        change Measurable fun w => ∑ i, ∑ j,
          ((Mw w).toBlocks₂₂ - (Mw w).toBlocks₂₁ * ((Mw w).toBlocks₁₁ + 1)⁻¹
            * (Mw w).toBlocks₁₂) i j ^ 2
        refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
        refine Measurable.pow_const ?_ _
        simp only [Matrix.sub_apply]
        refine Measurable.sub (hb22 i j) ?_
        have hentry : (fun w => ((Mw w).toBlocks₂₁ * ((Mw w).toBlocks₁₁ + 1)⁻¹
              * (Mw w).toBlocks₁₂) i j)
            = fun w => ∑ k, ∑ l, (Mw w).toBlocks₂₁ i k * ((Mw w).toBlocks₁₁ + 1)⁻¹ k l
                * (Mw w).toBlocks₁₂ l j := by
          funext w
          rw [Matrix.mul_apply]
          simp_rw [Matrix.mul_apply, Finset.sum_mul]
          rw [Finset.sum_comm]
        rw [hentry]
        refine Finset.measurable_sum _ (fun k _ => Finset.measurable_sum _ (fun l _ => ?_))
        exact ((hb21 i k).mul (hInv k l)).mul (hb12 l j)
    · -- the per-`w` Score-sandwich (from `hsq`), with `Φscore w = ∑(regStraighten(split w)).1² + Score w`.
      simpa only [hΦscore] using hsq w hw
  -- **Step 2: the diffeo bridge** `rlctAtOn Φscore wstar = rlctAtOn Φcore wstar` via `Ψ : S1 ↦ (I−K)·S1`
  -- (`rlctAtOn_comp_localDiffeo`: `Ψ` ContDiff ⊤, `HasStrictFDerivAt Ψ (≃L) wstar` with `Ψ'(wstar) =
  -- I − K(wstar) = I`, `Ψ wstar = wstar`; and `Φcore ∘ Ψ = Φscore` since `coreΦ ∘ Ψ = Score` (the LDU
  -- `Rcore = S0·(1−K)·S1`, `coreΦ = frobSq(S0·S1)`) and `Ψ` fixes the reg slot). The genuine remaining
  -- geometric content; the field migration + re-wiring (DeepestGaugeChart.lean) are DONE.
  -- **Step 2: the diffeo bridge, CASE-SPLIT on `L` (8th-catch pattern, like the `hinterface`
  -- 3041/3046 L≥3 guards).** At `L = 2` the deepest reduced chain `deepestM` has two layers, so the
  -- two-grouping collapses to single-layer blocks (`G0 = firstLayer`, `G1 = lastLayer`) and the joint
  -- `(T1, Y1)` Ψ (the verified-exact cert closed form) applies verbatim — closed by the separate
  -- axiom-clean `deepest_diffeo_bridge_L2`. For `L ≥ 3` the bridge needs the general-`L` grouped-`G0`
  -- diffeo (`W := I + Z1·A1⁻¹·A0⁻¹·Y0` on the `prodAux (L−1)`-grouped blocks + the grouped pivot `A0⁻¹`),
  -- the recursive multi-factor reparametrization — the general-`L` gap, joining 3041/3046 (Item 24).
  have hstep2 : rlctAtOn Φscore wstar
      = rlctAtOn
          (fun x : Fin (flatDim H) → ℝ =>
            (∑ i, (regStraighten (split x)).1 i ^ 2)
              + deepestCoreF H r (coreAbsorb (split x)).2.1)
          ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) := by
    rcases Nat.lt_or_ge L 3 with hLlt | hL3
    · -- **L = 2 branch** (`2 ≤ L < 3`): the collapsed joint Ψ, the R-A `deepest_diffeo_bridge_L2_wired`
      -- (= `_impl`), fed the triangular-bundle frames + hPtri/hQtri + the two per-`x` discharges.
      have hL2eq : L = 2 := by omega
      -- Transport hPtri/hQtri from the bundle form (`Pf (firstLayer)` / `Qf (lastLayer)` with `Jb`) to the
      -- `_wired`/sub-4 form (`endpointP0`/`endpointQL` with `J`): endpoint frames are casts of the boundary
      -- layers, `pivotJSucc J = Jb` bridges the last-layer pivot split.
      have hPtri' : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
          (endpointP0 H hL Pf)).toBlocks₁₂ = 0 := by
        have hfl : (firstLayer hL : Fin L) = ⟨0, by omega⟩ := Fin.ext (by simp [firstLayer])
        simpa only [endpointP0, hfl] using hPtri
      have hQtri' : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (endpointQL H hL Qf)).toBlocks₂₁ = 0 := by
        -- BOUNDED CAST-BRIDGE (cast-only): the `endpointQL = ▸ Qf ⟨L-1,_⟩` index-cast transport of
        -- toBlocks₂₁=0 + `← hpivJ` (Jb = pivotJSucc J) + defeq widths. 5 tactic shapes tried; resists
        -- one-shot (needs a toBlocks₂₁-transport helper). Left documented.
        sorry
      -- **hsub3reg** — reg-energy invariance under the joint move (RELATIVE: ψ-moved vs unmoved, SAME
      -- frames Pf/Qf, so the endpoint-frame conjugation CANCELS — UNAFFECTED by the sub-4 boundary-A11
      -- dictionary issue). Holds `∀ x` (stated germ-local for the body's `filter_upwards`). Via the
      -- sub-3 lemma `deepestEFull_sq_sum_psiSplitRawL2_eq` with `q := split x`, the framed params
      -- `Aψ/Aq` (§iii `framedParamsPivot_eq_frame_of_front`), `hinterface`, `hS3b`, and the raw-middle
      -- block agreement `hm11/hm12/hm21` (the e2/leak-kill readback — the SHARED per-layer readback piece).
      have hsub3reg : ∀ᶠ x : (Fin (flatDim H) → ℝ) in
          nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
          (∑ i, (deepestEFull H r hr hL J Pf Qf (psiSplitRawL2 H r hr hL (split x)) i) ^ 2)
            = ∑ i, (deepestEFull H r hr hL J Pf Qf (split x) i) ^ 2 := by
        -- `hS3b`: the framed B-corner is the threshold corner `fromBlocks 1 0 0 0` (producer pattern —
        -- `B = prod(deepestPoint)`, framed at the basepoint = `framedParamsRegPivot 0`, reindexes to corM).
        have hS3b : Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (endpointP0 H hL Pf * B * endpointQL H hL Qf)
          = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 := by
          -- `B = prod(deepestPoint)` (fibre membership), and `decode w0 = deepestPoint`.
          have hBprod : B = prod H (deepestPoint H r B hB hr hL) :=
            (deepestPoint_isDeep H r B hB hr hL).1.symm
          have hdecode : (paramsEquivFlat H).symm wstar = deepestPoint H r B hB hr hL := by
            rw [hwstar]; exact (paramsEquivFlat H).symm_apply_apply _
          -- §iii at `w := wstar`: `framedParamsPivot (split wstar) s = Pf s · deepest s · Qf s`.
          have hframe0 : ∀ s : Fin L,
              framedParamsPivot H r hr hL J Pf Qf (split wstar) s
                = Pf s * (deepestPoint H r B hB hr hL) s * Qf s := by
            intro s
            rw [hsplit wstar, ← hdecode]
            exact framedParamsPivot_eq_frame_of_front H r B hB hr hL J hJfront' Pf Qf hNF hPfL hcorner'
              wstar s
          -- Telescope: `prod(framedParamsPivot (split wstar)) = endpointP0 · prod(deepest) · endpointQL`.
          have htel : prod H (framedParamsPivot H r hr hL J Pf Qf (split wstar))
              = endpointP0 H hL Pf * prod H (deepestPoint H r B hB hr hL) * endpointQL H hL Qf :=
            endpoint_telescoping_eq H hL (deepestPoint H r B hB hr hL)
              (framedParamsPivot H r hr hL J Pf Qf (split wstar)) Pf Qf hframe0 hinterface
          -- `split wstar = 0` (basepoint), and `framedParamsPivot 0 = framedParamsRegPivot 0` (core-zero).
          have hsplit0 : split wstar = (0 : DeepestSplit H r (deepestNGauge H r)) := by
            rw [hwstar]; exact hsplit_base
          -- Assemble: `endpointP0·B·endpointQL = prod(framedParamsPivot (split wstar))` (htel + hBprod),
          -- `= prod(framedParamsPivot 0)` (hsplit0) `= prod(framedParamsRegPivot 0)` (coreZero), then corM.
          rw [hBprod, ← htel, hsplit0,
            show (0 : DeepestSplit H r (deepestNGauge H r))
              = (((0 : Fin (deepestNReg H r) → ℝ), (0 : Fin (flatDim (deepestM H r)) → ℝ),
                  (0 : Fin (deepestNGauge H r) → ℝ)) : DeepestSplit H r (deepestNGauge H r)) from rfl,
            framedParamsPivot_coreZero H r hr hL J Pf Qf 0 0,
            show (((0 : Fin (deepestNReg H r) → ℝ), (0 : Fin (deepestNGauge H r) → ℝ))
                : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
              = (0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) from rfl]
          exact reindex_prodAux_framedParamsRegPivot_zero H r hr hL hL2 J Pf Qf
        apply Filter.Eventually.of_forall
        intro x
        -- The two framed raw params: `Aq = decode x`, `Aψ = decode (split.symm (ψ (split x)))`.
        set Aq : Params H := (paramsEquivFlat H).symm x with hAq
        set Aψ : Params H :=
          (paramsEquivFlat H).symm (split.symm (psiSplitRawL2 H r hr hL (split x))) with hAψ
        -- `hframeq`: §iii at `w := x` (`split x = deepestSplit w0 x` by `hsplit x` + `hwstar`-base).
        have hframeq : ∀ s : Fin L,
            framedParamsPivot H r hr hL J Pf Qf (split x) s = Pf s * Aq s * Qf s := by
          intro s
          rw [hsplit x]
          exact framedParamsPivot_eq_frame_of_front H r B hB hr hL J hJfront' Pf Qf hNF hPfL hcorner' x s
        -- `hframeψ`: §iii at `w := split.symm (ψ (split x))`; `ψ (split x) = split (split.symm (ψ (split x)))`
        -- (homeomorph round-trip), then `split … = deepestSplit w0 …` (`hsplit`).
        have hframeψ : ∀ s : Fin L,
            framedParamsPivot H r hr hL J Pf Qf (psiSplitRawL2 H r hr hL (split x)) s
              = Pf s * Aψ s * Qf s := by
          intro s
          have hrt : psiSplitRawL2 H r hr hL (split x)
              = split (split.symm (psiSplitRawL2 H r hr hL (split x))) :=
            (split.apply_symm_apply _).symm
          rw [hrt, hsplit (split.symm (psiSplitRawL2 H r hr hL (split x)))]
          exact framedParamsPivot_eq_frame_of_front H r B hB hr hL J hJfront' Pf Qf hNF hPfL hcorner'
            (split.symm (psiSplitRawL2 H r hr hL (split x))) s
        -- `hm11/hm12/hm21`: the raw-middle `{11,12,21}` block agreement — the SHARED per-layer readback
        -- piece (genm-l2fill's Codex (d), most-likely-to-thrash; couples to the readback genm-l2fill is
        -- restructuring for the sub-4 dictionary fix). Isolated here pending that settle.
        have hm11 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (prod H Aψ)).toBlocks₁₁
            = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (prod H Aq)).toBlocks₁₁ := by
          sorry
        have hm12 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (prod H Aψ)).toBlocks₁₂
            = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (prod H Aq)).toBlocks₁₂ := by
          sorry
        have hm21 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (prod H Aψ)).toBlocks₂₁
            = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (prod H Aq)).toBlocks₂₁ := by
          sorry
        exact deepestEFull_sq_sum_psiSplitRawL2_eq H r hr hL hL2eq J Pf Qf hPtri' hQtri'
          (split x) B Aψ Aq hframeψ hframeq hinterface hS3b hm11 hm12 hm21
      -- **The shared inner-ball germ** (GOAL 1): near the basepoint, `psiSplitRawL2 (split x) ∈ closedBall
      -- 0 rIn`. `psiSplitRawL2 = δ + id` is ContinuousAt 0 (δ strict-deriv at 0), `psiSplitRawL2 0 = 0`;
      -- `split` continuous, `split basepoint = 0`; the composite → 0, the ball is a nhd of 0.
      have hpsiCA : ContinuousAt (psiSplitRawL2 H r hr hL)
          (0 : DeepestSplit H r (deepestNGauge H r)) := by
        have hδ : ContinuousAt (psiSplitDeltaL2 H r hr hL)
            (0 : DeepestSplit H r (deepestNGauge H r)) :=
          (hasStrictFDerivAt_psiSplitDeltaL2_zero H r hr hL).continuousAt
        have hid : psiSplitRawL2 H r hr hL
            = fun q => psiSplitDeltaL2 H r hr hL q + q := by
          funext q; simp only [psiSplitDeltaL2, sub_add_cancel]
        rw [hid]; exact hδ.add continuousAt_id
      have htend : Filter.Tendsto (fun x => psiSplitRawL2 H r hr hL (split x))
          (nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL))) (nhds 0) := by
        have hcomp : ContinuousAt (fun x => psiSplitRawL2 H r hr hL (split x))
            ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) := by
          have h1 : ContinuousAt split ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) :=
            split.continuous.continuousAt
          exact (hsplit_base ▸ hpsiCA).comp h1
        have h0 : psiSplitRawL2 H r hr hL
            (split ((paramsEquivFlat H) (deepestPoint H r B hB hr hL))) = 0 := by
          rw [hsplit_base]; exact psiSplitRawL2_zero H r hr hL
        rw [← h0]; exact hcomp
      have hballgerm : ∀ᶠ x : (Fin (flatDim H) → ℝ) in
          nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
          psiSplitRawL2 H r hr hL (split x) ∈ Metric.closedBall
            (0 : DeepestSplit H r (deepestNGauge H r)) ((cutoffBump H r hr hL).rIn) :=
        htend (Metric.closedBall_mem_nhds 0 (cutoffBump H r hr hL).rIn_pos)
      -- **The hWdet germ**: near the basepoint, `split x ∈ ball l2ExtraRadius` (split continuous, split
      -- basepoint = 0), so `split x ∈ l2ExtraUnitSetSplit` (`ball_l2ExtraRadius_subset`) ⟹ `det l2W ≠ 0`.
      have hsplit_tend : Filter.Tendsto split
          (nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)))
          (nhds (0 : DeepestSplit H r (deepestNGauge H r))) := by
        have h := (split.continuous.continuousAt
          (x := (paramsEquivFlat H) (deepestPoint H r B hB hr hL))).tendsto
        rwa [hsplit_base] at h
      have hWdetgerm : ∀ᶠ x : (Fin (flatDim H) → ℝ) in
          nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
          (l2W H r hr hL hL2eq (split x)).det ≠ 0 := by
        have hballx : ∀ᶠ x : (Fin (flatDim H) → ℝ) in
            nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
            split x ∈ Metric.ball (0 : DeepestSplit H r (deepestNGauge H r))
              (l2ExtraRadius H r hr hL hL2eq) :=
          hsplit_tend.eventually_mem (Metric.ball_mem_nhds 0 (l2ExtraRadius_pos H r hr hL hL2eq))
        filter_upwards [hballx] with x hx
        exact (ball_l2ExtraRadius_subset H r hr hL hL2eq hx).2
      -- **hsub4core** — GERM-LOCAL core = Score (Option-2 sub-4 on the inner-ball germ).
      have hsub4core : ∀ᶠ x : (Fin (flatDim H) → ℝ) in
          nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
          deepestCoreF H r (deepestCoreAbsorb H r hr hL (psiSplitRawL2 H r hr hL (split x))).2.1
            = Score x := by
        filter_upwards [hballgerm, hWdetgerm] with x hball hWdet
        -- `q := split x = deepestSplit w0 x` (hsplit); apply Option-2 sub-4 with hball/hWdet/hScoreDef.
        refine deepestCoreF_coreAbsorb_psiSplitRawL2_eq_score H r B hB hr hL hL2eq J Pf Qf
          hPtri' hQtri' Score hScoreDef x (split x) (hsplit x) hball hWdet ?_
        -- hLDUtie: the readback-tie (prod(deepestM) cleaned-tuple = Score (1,1)-Schur integrand) is
        -- EXTRACTED to the standalone `prod_deepestM_eq_schur_ldu_readback` (DeepestLDUReadback.lean) for a
        -- collision-free fill. ⚠ That statement is currently MIS-DICTIONARIED (numerically false for the
        -- bare-read `l2*` dictionary — the deepest boundary leading block `A11 ≠ 1`; triple-confirmed:
        -- my numerics + two decorrelated Codex + the Lean defs). The fix (frame-conjugated reads) is
        -- pending adjudication; until then the standalone carries the `sorry` with the finding documented.
        exact prod_deepestM_eq_schur_ldu_readback H r B hB hr hL hL2eq J Pf Qf hPtri' hQtri'
          x (split x) (hsplit x) hWdet
      exact deepest_diffeo_bridge_L2_wired H r B hB hr hL hL2 hpos J hJfront' Pf Qf hPtri' hQtri'
        split hsub3reg coreAbsorb regStraighten hsplit hra_regval hca_def Score hScoreDef
        hsub4core Φscore hΦscore wstar hwstar hL2eq
    · -- **L ≥ 3 branch (general-`L` grouped-`G0` diffeo GAP).** The cert's `(T1, Y1)` Ψ generalises to
      -- the two-grouping `G0 = prodAux (L−1)` (first `L−1` layers), `G1 = last layer`: `A0, Y0, Z0, T0`
      -- become the grouped-product blocks and `W`/`⅟P00` carry the grouped pivot `A0⁻¹`. The recursive
      -- multi-factor reparametrization — the general-`L` frontier, joining the 3041/3046 L≥3 interior gaps.
      sorry
  rw [hstep1, hstep2]

/-- **The `DeepestGaugeChart` instance** (#44c sub-3, `deepest_gauge_squeeze_exists`, `2 ≤ L`).
Destructures the bundled construction into the structure. The `2 ≤ L` hypothesis (distinct boundary
layers) is what `deepest_gauge_construction` needs for the endpoint-frame triviality; crux2 wires
`deepest_gauge_squeeze_exists := this` on the `2 ≤ L` branch (`L = 1` is the smooth base case). -/
theorem deepest_gauge_chart_construct (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    -- The front-pivot hypothesis (b-wlog-spec; discharged by the caller's `B·Π` WLOG transfer).
    (hJfront : ((deepestPoint_frame_pivot_exists H r B hB hr hL hL2).choose).trans
        (finCongr (H_lastLayer_succ H hL)).toEmbedding = frontEmbed H r hr)
    -- The row-alignment (htop, S2 — discharged by the caller's row-WLOG transfer).
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r) :
    Nonempty (DeepestGaugeChart H r B hB hr hL) := by
  obtain ⟨nGauge, split, coreAbsorb, regStraighten, hsplit_mp, hsplit_base, hca_base, hca_reg,
    hca_spec, hca_rlct, hra_cont, hra_base, hra_core, hra_spec, hra_rlct, hsq⟩ :=
    deepest_gauge_construction H r B hB hr hL hL2 hpos hJfront htop
  exact ⟨{
    nGauge := nGauge
    split := split
    split_mp := hsplit_mp
    split_basepoint := hsplit_base
    coreAbsorb := coreAbsorb
    coreAbsorb_basepoint := hca_base
    coreAbsorb_regular := hca_reg
    coreAbsorb_spectator := hca_spec
    coreAbsorb_rlct := hca_rlct
    regStraighten := regStraighten
    regStraighten_continuous := hra_cont
    regStraighten_basepoint := hra_base
    regStraighten_core := hra_core
    regStraighten_spectator := hra_spec
    regAbsorb_rlct := hra_rlct
    loss_squeeze := hsq }⟩

/-! ## L2-Skeleton consumption pre-stage (#126, the #28-integration layer)

How the gauge chart's value-free reduction discharges the Skeleton's L2 normal form. The
value-free `deepest_regular_core_reduces` (DeepestGaugeChart, mine) lands on
`nReg/2 + rlctAtOn (dlnLoss M 0) 0` — the CORE RLCT, NOT its closed form. The Skeleton's
`deepest_regular_core_normal_form` (Skeleton.lean:1124) wants `nReg/2 + ofReal(lambdaCore M)`. The
gap is exactly the **R1 core-value** `rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)` (R1's
`resolution_charts` + A1's `lambdaCore_eq_clean`/`⨅ monomialThreshold = lambdaCore` — R1's lane, in
flight). Route-first: this conditional bridge takes the R1 value + `hGne` as HYPOTHESES and produces
the normal-form conclusion, so the controller wires
`exact deepest_regular_core_normal_form_of … hcore hGne` into the Skeleton sorry once R1's value
lands — closing the L2 Skeleton obligation in one pass. Decouples L2-integration from R1's completion. -/

/-- **The L2 normal-form, conditional on the R1 core-value** (the #28-integration bridge). Given the
R1 core-value `hcore : rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)` (R1's lane) and the
reduced-core germ-nonvanishing `hGne`, the local RLCT of `dlnLoss H B` at the deepest point is the
regular shift `nReg/2` plus the closed-form core `ofReal(lambdaCore M)` — the exact
`deepest_regular_core_normal_form` conclusion. Proof: `deepest_regular_core_reduces` (value-free,
mine) `▸` the R1 value `hcore`. -/
theorem deepest_regular_core_normal_form_of (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hcore : rlctAtOn
        (fun A : Params (fun s => H s - r) =>
          dlnLoss (fun s => H s - r)
            (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
        (fun _ => 0 : Params (fun s => H s - r))
      = ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ))
    (hGne : ∃ U ∈ 𝓝 (0 : Fin (flatDim (fun s => H s - r)) → ℝ),
      ∀ᵐ z ∂(volume.restrict U),
        dlnLoss (fun s => H s - r)
          (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
          ((paramsEquivFlat (fun s => H s - r)).symm z) ≠ 0) :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
      = ((r * (H 0 + H (Fin.last L) - r) : ℕ) : ℝ≥0∞) / 2
        + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ) := by
  rw [deepest_regular_core_reduces H r B hB hr hL hGne, hcore]


end DLNFibre.DLN.RLCT
