import DLNFibre.DLN.RLCT.Validate.DeepestGaugeConstruction
import DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeL2
import DLNFibre.DLN.RLCT.Validate.DeepestPivotFrameTriangular
import DLNFibre.DLN.RLCT.Validate.DeepestLDUReadback
import DLNFibre.DLN.RLCT.Validate.DeepestL2ConjSub4
import DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeGenConj
import DLNFibre.DLN.RLCT.Validate.DeepestChainUnitGerm
import DLNFibre.DLN.RLCT.Validate.DeepestHsub4coreGen
import DLNFibre.DLN.RLCT.Validate.DeepestHsub4coreHCGen
import DLNFibre.DLN.RLCT.Validate.DeepestHsub4coreInvGerm
import DLNFibre.DLN.RLCT.Validate.DeepestPsiFlatCutGen
import DLNFibre.DLN.RLCT.Validate.DeepestPsiHraw0Gen
import DLNFibre.DLN.RLCT.Validate.DeepestPsiHderiv0Gen
import DLNFibre.DLN.RLCT.Validate.DeepestPsiHcdGen
import DLNFibre.DLN.RLCT.Validate.DeepestDeepBlkBoundaryGen

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

/-- **Width-cast transport of `toBlocks₂₁ = 0` for an `rThresholdSplit`-reindexed square matrix.**
For a `Fin (L+1)`-index equality `e : a = b`, the `(2,1)`-block of `reindex (rThr (H b)) (rThr (H b))
(e ▸ M)` vanishes iff that of `reindex (rThr (H a)) (rThr (H a)) M` does — `subst e` collapses the `▸`
cast (the widths `H a`, `H b` and the two threshold splits coincide). This is the cast-only residual in
`hQtri'` (the `(lastLayer).succ = Fin.last L` width transport from the bundle's `Qf (lastLayer)` to
`endpointQL`); no matrix math. Stated as `∀`-quantified over the cast proof so the goal-side `▸` matches
syntactically (avoids the `rewrite` "motive not type correct" wall). -/
private theorem reindex_rThr_toBlocks21_zero_cast (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) {a b : Fin (L + 1)} (e : a = b)
    (M : Matrix (Fin (H a)) (Fin (H a)) ℝ)
    (hM : (Matrix.reindex (rThresholdSplit r (H a) (hr a)) (rThresholdSplit r (H a) (hr a)) M).toBlocks₂₁
      = 0) :
    (Matrix.reindex (rThresholdSplit r (H b) (hr b)) (rThresholdSplit r (H b) (hr b))
        (e ▸ M)).toBlocks₂₁ = 0 := by
  subst e; exact hM

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


/-- **The L=2 gauge construction, PARAMETERIZED by the triangular frame bundle** (genm-44l2, Route X
bedrock). The body of `deepest_gauge_construction_L2` with the triangular boundary-frame bundle
(`Jb, Pf, Qf` + its 12 conclusions, incl. `hJtri : Jb.trans finCongr = frontEmbed`) taken as EXPLICIT
ARGS rather than obtained from a specific existence lemma. So BOTH the arbitrary bundle
(`deepestPoint_frame_pivot_triangular_exists`, via the thin wrapper `deepest_gauge_construction_L2`
below) AND the FRONT bundle (`deepestPoint_frame_pivot_triangular_front_exists`, via the front feeder)
feed the SAME body — no duplication. Body byte-verbatim from the original `_L2` (only the `obtain` line
became these parameters). -/
theorem deepest_gauge_construction_L2_ofBundle (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r)
    (hLlt : L < 3)
    -- The triangular boundary-frame bundle (the 15 destructured items of
    -- `deepestPoint_frame_pivot_triangular_exists` / `…_front_exists`):
    (Jb : Fin r ↪ Fin (H ((lastLayer hL).succ)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hJtri : Jb.trans (finCongr (H_lastLayer_succ H hL)).toEmbedding = frontEmbed H r hr)
    (hPunit : ∀ s : Fin L, IsUnit (Pf s)) (hQunit : ∀ s : Fin L, IsUnit (Qf s))
    (hQf0 : Qf (firstLayer hL)
        = (1 : Matrix (Fin (H (firstLayer hL).succ)) (Fin (H (firstLayer hL).succ)) ℝ))
    (hPfL : Pf (lastLayer hL)
        = (1 : Matrix (Fin (H (lastLayer hL).castSucc)) (Fin (H (lastLayer hL).castSucc)) ℝ))
    (hNF : ∀ s : Fin L, (s : ℕ) + 1 ≠ L →
        Pf s * (deepestPoint H r B hB hr hL s) * Qf s
          = Matrix.of (fun (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) =>
              if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0))
    (hQf22b : IsUnit ((Matrix.reindex (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) Jb)
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) Jb)
        (Qf (lastLayer hL))).toBlocks₂₂))
    (hcorner : Matrix.reindex (rThresholdSplit r (H ((lastLayer hL).castSucc)) (hr _))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) Jb)
        ((deepestPoint H r B hB hr hL (lastLayer hL)) * Qf (lastLayer hL))
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (hPtri : (Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
        (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
        (Pf (firstLayer hL))).toBlocks₁₂ = 0)
    (hQtri : (Matrix.reindex (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) Jb)
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) Jb)
        (Qf (lastLayer hL))).toBlocks₂₁ = 0)
    (hP22one : (Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
        (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
        (Pf (firstLayer hL))).toBlocks₂₂
        = (1 : Matrix (Fin (H (firstLayer hL).castSucc - r)) (Fin (H (firstLayer hL).castSucc - r)) ℝ))
    (hQ22one : (Matrix.reindex (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) Jb)
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) Jb)
        (Qf (lastLayer hL))).toBlocks₂₂
        = (1 : Matrix (Fin (H ((lastLayer hL).succ) - r)) (Fin (H ((lastLayer hL).succ) - r)) ℝ)) :
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
  -- hypothesis `hsplit` discharges by `rfl` — the index-decode lemmas (`gaugeReadX/Y/Z_deepestSplit`,
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
  -- **`hTilde` (CLOSED, #120):** `π̃ := regStraightenOf2 (deepestEFull ∘ coreAbsorb.symm)` is a local
  -- diffeo at `0` (ContDiff + invertible strict-deriv `eTilde`). ContDiff is routine (deepestEFull +
  -- coreAbsorb.symm both ContDiff); the invertible strict-deriv uses the degree-2 core-block-vanishing
  -- `∂deepestEFull/∂core(0) = 0` (so `π̃`'s reg-reg block stays PIN1's invertible `F` despite
  -- `coreAbsorb.symm`'s reg→core shear) — the value-fold atom (thread 31), parallel to PIN1's
  -- `deepestEPivot_regSlice_fderiv`. Discharged below (no sorry).
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
  -- Assemble the bundle: all data (`split`, `coreAbsorb`, `regStraighten` + their facts) is in scope;
  -- the final `?_` is the migrated `loss_squeeze` RLCT-equality (the route-B close below).
  refine ⟨deepestNGauge H r, split, coreAbsorb, regStraighten, hsplit_mp, hsplit_base, hca_base,
    hca_reg, hca_spec, hca_rlct, hra_cont, hra_base, hra_core, hra_spec, hra_rlct, ?_⟩
  -- ===== L = 2 ARM (sorry-free) — hoisted from deepest_gauge_construction =====
  -- **hinterface (L = 2, SORRY-FREE).** Interior branches are vacuous: `(s:ℕ)+1 < L` with `L = 2`
  -- forces `s = 0`, so the `hspos` (`1 ≤ s`) and `hint` (`s+1 < L-1 = 1`) arms close by `omega`.
  have hinterface : ∀ (s : Fin L) (_ : (s : ℕ) + 1 < L),
      Qf s = (1 : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) ∧
        Pf ⟨(s : ℕ) + 1, by omega⟩ = (1 : Matrix (Fin (H (⟨(s : ℕ) + 1, by omega⟩ : Fin L).castSucc))
          (Fin (H (⟨(s : ℕ) + 1, by omega⟩ : Fin L).castSucc)) ℝ) := by
    intro s hs
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos (s : ℕ) with hs0 | hspos
      · have hsf : s = firstLayer hL := Fin.ext (by simp [firstLayer, hs0])
        rw [hsf]; exact hQf0
      · exfalso; omega
    · rcases Nat.lt_or_ge ((s : ℕ) + 1) (L - 1) with hint | hbdy
      · exfalso; omega
      · have hsf : (⟨(s : ℕ) + 1, by omega⟩ : Fin L) = lastLayer hL :=
          Fin.ext (by simp only [lastLayer]; omega)
        rw [hsf]; exact hPfL
  -- PIN 2: the loss squeeze (ROUTE-B close, `coreΦ → Score`, 2026-06-25). The migrated `loss_squeeze`
  -- field is the RLCT-EQUALITY `rlctAt(dlnLoss) = rlctAtOn(Sreg_E + coreΦ)`. We prove it from the TRUE
  -- Score-sandwich `hsq` (`deepest_loss_squeeze`, axiom-clean) via `rlctAtOn_squeeze`
  -- (⟹ `rlctAtOn(Sreg_E + Score)`) + the analytic-unit diffeo bridge `rlctAtOn(Sreg_E + Score) =
  -- rlctAtOn(Sreg_E + coreΦ)` (`Ψ : S1 ↦ (I−K)·S1`). `Score = frobSqMat(Rcore)` (the `hscore`/`hScoreDef`
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
    · -- `Φscore` measurable: reg sum-of-squares + `Score` (a frobSqMat of a continuous matrix in `w`).
      rw [hΦscore, hScoreDef]
      apply Measurable.add
      · exact (Finset.measurable_sum _ (fun i _ =>
          ((measurable_pi_apply i).comp
            (continuous_fst.comp (hra_cont.comp split.continuous)).measurable).pow_const _))
      · -- **MEASURABILITY of `Score` (mechanical, entrywise).** `Score w = frobSqMat(Schur(Mw w))`,
        -- `Mw w = reindex(endpointP0·(prod(symm w)−B)·endpointQL)` — CONTINUOUS in `w` (`continuous_Mw`).
        -- The only non-continuous piece is `(Mw₁₁+1)⁻¹`, but it is MEASURABLE entrywise: `inv_def` gives
        -- `A⁻¹ = (Ring.inverse A.det) • A.adjugate`, with `Continuous.matrix_det`/`Continuous.matrix_adjugate`
        -- continuous and `Ring.inverse : ℝ → ℝ` measurable. So each Schur-leak entry is measurable
        -- (∑∑ of products of measurable scalars), and `frobSqMat` (finite ∑∑ of squares) is measurable.
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
  -- **Step 2 (L = 2): the diffeo bridge** via the banked `deepest_diffeo_bridge_L2_assembled`
  -- (route-b, atom-free). `subst hL2eq` aligns `H : Fin 3`.
  have hstep2 : rlctAtOn Φscore wstar
      = rlctAtOn
          (fun x : Fin (flatDim H) → ℝ =>
            (∑ i, (regStraighten (split x)).1 i ^ 2)
              + deepestCoreF H r (coreAbsorb (split x)).2.1)
          ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) := by
    have hL2eq : L = 2 := by omega
    subst hL2eq
    -- **Boundary block facts** (`hDA`/`hY`/`hZ`/`hbdy`) from the banked L=2 helpers + the bundle units.
    have hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin 2)) :=
      deepBlkA0_isUnit_of_htop H r B hB hr hL hL2 htop
    -- `hDAlast`: the last-layer pivot base is a unit (corner identity + `Qf₂₁ = 0`). `hQtri` (bundle) is
    -- the block-upper `Qf (lastLayer)` in `Jb`-split form; `hpivJ` bridges to `pivotJSucc J`.
    have hQUpper : (Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₁ = 0 := by rw [hpivJ]; exact hQtri
    have hDAlast : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)) :=
      deepBlkA_last_isUnit_of_bundle H r B hB hr hL J hJfront' Qf hcorner' hQUpper
    have hDA : ∀ s : Fin 2, IsUnit (deepBlkA H r B hB hr hL s) :=
      deepBlkA_isUnit_of_L2 H r B hB hr hL rfl hDA0 hDAlast
    have hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin 2) = 0 :=
      deepBlkY_layer0_zero H r B hB hr hL (by omega) (⟨0, by omega⟩ : Fin 2) rfl
    have hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0 :=
      deepBlkZ_layerLast_zero H r B hB hr hL (by omega) (lastLayer hL) (by simp [lastLayer])
    have hbdy : ∀ s : Fin 2, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0 :=
      deepBlk_boundary_of_L2 H r B hB hr hL rfl
    -- **The endpoint-frame `(1,2)/(2,1)/(2,2)` block facts** (`hPtri'`/`hQtri'`/`hP22'`/`hQ22'`): transport
    -- the bundle's `Pf (firstLayer)` / `Qf (lastLayer)` block-triangularity to the `endpointP0`/`endpointQL`
    -- form. `firstLayer = ⟨0,_⟩`; `endpointQL = ▸ Qf (lastLayer)`; `J = frontEmbed` collapses pivot↦rThr.
    have hfl : (firstLayer hL : Fin 2) = ⟨0, by omega⟩ := Fin.ext (by simp [firstLayer])
    have hPtri' : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
        (endpointP0 H hL Pf)).toBlocks₁₂ = 0 := by
      simpa only [endpointP0, hfl] using hPtri
    have hQtri' : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
        (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
        (endpointQL H hL Qf)).toBlocks₂₁ = 0 := by
      rw [hJfront', pivotThresholdSplit_frontEmbed H r hr]
      have hcast0 : ((lastLayer hL).succ) = Fin.last 2 :=
        Fin.ext (by simp [lastLayer, Fin.succ, Fin.last])
      have hQtriR : (Matrix.reindex (rThresholdSplit r (H ((lastLayer hL).succ)) (hr _))
          (rThresholdSplit r (H ((lastLayer hL).succ)) (hr _))
          (Qf (lastLayer hL))).toBlocks₂₁ = 0 := by
        have h := hQtri
        rw [← hpivJ, hJfront', pivotThresholdSplit_pivotJSucc_frontEmbed H r hr hL] at h
        exact h
      show (Matrix.reindex (rThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)))
          (rThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)))
          (hcast0 ▸ Qf (lastLayer hL))).toBlocks₂₁ = 0
      exact reindex_rThr_toBlocks21_zero_cast H r hr hcast0 (Qf (lastLayer hL)) hQtriR
    -- **`hS3b`**: the framed B-corner is the threshold corner `fromBlocks 1 0 0 0` (`B = prod(deepest)`,
    -- framed at the basepoint = `framedParamsRegPivot 0`, reindexes to corM).
    have hS3b : Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
        (endpointP0 H hL Pf * B * endpointQL H hL Qf)
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 := by
      have hBprod : B = prod H (deepestPoint H r B hB hr hL) :=
        (deepestPoint_isDeep H r B hB hr hL).1.symm
      have hframe0 : ∀ s : Fin 2,
          framedParamsPivot H r hr hL J Pf Qf (split wstar) s
            = Pf s * (deepestPoint H r B hB hr hL) s * Qf s := by
        intro s
        have hdecode : (paramsEquivFlat H).symm wstar = deepestPoint H r B hB hr hL := by
          rw [hwstar]; exact (paramsEquivFlat H).symm_apply_apply _
        rw [hsplit wstar, ← hdecode]
        exact framedParamsPivot_eq_frame_of_front H r B hB hr hL J hJfront' Pf Qf hNF hPfL hcorner'
          wstar s
      have htel : prod H (framedParamsPivot H r hr hL J Pf Qf (split wstar))
          = endpointP0 H hL Pf * prod H (deepestPoint H r B hB hr hL) * endpointQL H hL Qf :=
        endpoint_telescoping_eq H hL (deepestPoint H r B hB hr hL)
          (framedParamsPivot H r hr hL J Pf Qf (split wstar)) Pf Qf hframe0 hinterface
      have hsplit0 : split wstar = (0 : DeepestSplit H r (deepestNGauge H r)) := by
        rw [hwstar]; exact hsplit_base
      rw [hBprod, ← htel, hsplit0,
        show (0 : DeepestSplit H r (deepestNGauge H r))
          = (((0 : Fin (deepestNReg H r) → ℝ), (0 : Fin (flatDim (deepestM H r)) → ℝ),
              (0 : Fin (deepestNGauge H r) → ℝ)) : DeepestSplit H r (deepestNGauge H r)) from rfl,
        framedParamsPivot_coreZero H r hr hL J Pf Qf 0 0,
        show (((0 : Fin (deepestNReg H r) → ℝ), (0 : Fin (deepestNGauge H r) → ℝ))
            : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
          = (0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) from rfl]
      exact reindex_prodAux_framedParamsRegPivot_zero H r hr hL hL2 J Pf Qf
    -- **The endpoint `(2,2)`-blocks `= 1`** (`hP22one`/`hQ22one`, transported to endpoint form), and
    -- the endpoint `(1,1)` invertibles `hP11inv`/`hQ11inv` (the pivot-base units — `hP22/hQ22` ⟹ the
    -- endpoint frames are block-triangular with identity ₂₂, so `det = det(₁₁); the ₁₁ are units).
    have hP22' : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
        (endpointP0 H hL Pf)).toBlocks₂₂ = 1 := by
      simpa only [endpointP0, hfl] using hP22one
    have hQ22' : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
        (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
        (endpointQL H hL Qf)).toBlocks₂₂ = 1 := by
      rw [hJfront', pivotThresholdSplit_frontEmbed H r hr]
      have hcast0 : ((lastLayer hL).succ) = Fin.last 2 :=
        Fin.ext (by simp [lastLayer, Fin.succ, Fin.last])
      have hQ22R : (Matrix.reindex (rThresholdSplit r (H ((lastLayer hL).succ)) (hr _))
          (rThresholdSplit r (H ((lastLayer hL).succ)) (hr _))
          (Qf (lastLayer hL))).toBlocks₂₂ = 1 := by
        have h := hQ22one
        rw [← hpivJ, hJfront', pivotThresholdSplit_pivotJSucc_frontEmbed H r hr hL] at h
        exact h
      show (Matrix.reindex (rThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)))
          (rThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)))
          (hcast0 ▸ Qf (lastLayer hL))).toBlocks₂₂ = 1
      exact reindex_rThr_toBlocks22_one_cast H r hr hcast0 (Qf (lastLayer hL)) hQ22R
    -- The endpoint `(1,1)` invertibles: the endpoint frames are units (`hPf`/`hQf`), block-triangular
    -- (`hPtri'`/`hQtri'`) with identity `(2,2)` (`hP22'`/`hQ22'`), so the `(1,1)` block is a unit.
    have hP11inv : Invertible (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (rThresholdSplit r (H 0) (hr 0)) (endpointP0 H hL Pf)).toBlocks₁₁ :=
      endpoint_toBlocks₁₁_invertible_of_blockTri (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (rThresholdSplit r (H 0) (hr 0)) (endpointP0 H hL Pf))
        ((Matrix.isUnit_submatrix_equiv _ _).mpr (isUnit_endpointP0 H hL Pf hPf)) hP22' (Or.inl hPtri')
    have hQ11inv : Invertible (Matrix.reindex
        (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
        (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
        (endpointQL H hL Qf)).toBlocks₁₁ :=
      endpoint_toBlocks₁₁_invertible_of_blockTri (Matrix.reindex
        (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
        (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (endpointQL H hL Qf))
        ((Matrix.isUnit_submatrix_equiv _ _).mpr (isUnit_endpointQL H hL Qf hQf)) hQ22'
        (Or.inr hQtri')
    -- **The per-layer `hPtri2`/`hQtri2` (∀ s : Fin 2)** the assembled bridge consumes: `s = 0`
    -- (firstLayer) gives `P`-block-lower (bundle `hPtri`) + `Q = 1` (`hQf0`); `s = 1` (lastLayer) gives
    -- `P = 1` (`hPfL`) + `Q`-block-upper (bundle `hQtri`, pivot↦rThr via `hJfront'`).
    have hPtri2 : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0 := by
      intro s
      rcases Nat.eq_zero_or_pos (s : ℕ) with hs0 | hspos
      · have hsf : s = firstLayer hL := Fin.ext (by simp [firstLayer, hs0])
        rw [hsf]; exact hPtri
      · have hsf : s = lastLayer hL := by
          apply Fin.ext; simp only [lastLayer]; have := s.isLt; omega
        rw [hsf, hPfL]; exact reindex_one_toBlocks₁₂_zero _
    have hQtri2 : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0 := by
      intro s
      rcases Nat.eq_zero_or_pos (s : ℕ) with hs0 | hspos
      · have hsf : s = firstLayer hL := Fin.ext (by simp [firstLayer, hs0])
        rw [hsf, hQf0]; exact reindex_one_toBlocks₂₁_zero _
      · have hsf : s = lastLayer hL := by
          apply Fin.ext; simp only [lastLayer]; have := s.isLt; omega
        rw [hsf]
        have h := hQtri
        rw [← hpivJ, hJfront', pivotThresholdSplit_pivotJSucc_frontEmbed H r hr hL] at h
        -- `(lastLayer).succ = Fin.last 2`, and `Qf (lastLayer)` reindexed at `rThr (H (lastLayer).succ)`.
        exact h
    -- **CONJ hsub3reg** (the reg-energy germ) via `hsub3reg_conj_germ`.
    have hsub3reg : ∀ᶠ x : (Fin (flatDim H) → ℝ) in
        nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
        (∑ i, (deepestEFull H r hr hL J Pf Qf
            (psiSplitRawL2CoreConj H r B hB hr hL rfl (split x)) i) ^ 2)
          = ∑ i, (deepestEFull H r hr hL J Pf Qf (split x) i) ^ 2 :=
      hsub3reg_conj_germ H r B hB hr hL rfl (hDA (⟨0, by omega⟩ : Fin 2)) J hJfront' Pf Qf
        hPtri' hQtri' hNF hPfL hcorner' split hsplit hsplit_base hinterface hS3b
    -- **CONJ hsub4core** (the core = Score germ) via `hsub4core_conj_germ`.
    have hsub4core : ∀ᶠ x : (Fin (flatDim H) → ℝ) in
        nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
        deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA
            (psiSplitRawL2CoreConj H r B hB hr hL rfl (split x))).2.1 = Score x :=
      hsub4core_conj_germ H r B hB hr hL rfl hDA hY hZ J hJfront' Pf Qf hPtri' hQtri' hP22' hQ22'
        hS3b hP11inv hQ11inv split hsplit Score hScoreDef
    -- **Apply the BANKED assembled bridge** (route-b, BARE canonical target, sorry-free). `coreAbsorb`
    -- collapses to `deepestCoreAbsorb` (`hca_def`); the RHS basepoint IS `wstar` (`hwstar`).
    rw [show coreAbsorb = deepestCoreAbsorb H r hr hL from hca_def,
      show (paramsEquivFlat H) (deepestPoint H r B hB hr hL) = wstar from hwstar.symm]
    exact deepest_diffeo_bridge_L2_assembled H r B hB hr hL hDA hY hZ hbdy J hJfront' Pf Qf
      hPf hQf hQf0 hPfL hQf22 hPtri2 hQtri2 split hsplit_mp hsub3reg regStraighten hsplit
      hra_regval Score hsub4core Φscore hΦscore wstar hwstar
  rw [hstep1, hstep2]

/-- **The L=2 gauge construction** (thin wrapper, Route X). Obtains the ARBITRARY triangular
boundary-frame bundle from `deepestPoint_frame_pivot_triangular_exists` (threading `hJfront`) and
applies the parameterized core `deepest_gauge_construction_L2_ofBundle`. STATEMENT UNCHANGED from the
original (consumers + AxCheck unaffected); the body is now a 2-line delegation. The front route feeds
the SAME core with the FRONT bundle (`deepestPoint_frame_pivot_triangular_front_exists`,
`DeepestFrontGauge`), discharging `hJfront` via the provable `hcolfront`. -/
theorem deepest_gauge_construction_L2 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (hJfront : ((deepestPoint_frame_pivot_exists H r B hB hr hL hL2).choose).trans
        (finCongr (H_lastLayer_succ H hL)).toEmbedding = frontEmbed H r hr)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r)
    (hLlt : L < 3) :
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
      rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
        = rlctAtOn
            (fun x : Fin (flatDim H) → ℝ =>
              (∑ i, (regStraighten (split x)).1 i ^ 2)
                + deepestCoreF H r (coreAbsorb (split x)).2.1)
            ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) := by
  obtain ⟨Jb, Pf, Qf, hJtri, hPunit, hQunit, hQf0, hPfL, hNF, hQf22b, hcorner, hPtri, hQtri,
      hP22one, hQ22one, _⟩ :=
    deepestPoint_frame_pivot_triangular_exists H r B hB hr hL hL2 htop hJfront
  exact deepest_gauge_construction_L2_ofBundle H r B hB hr hL hL2 hpos htop hLlt
    Jb Pf Qf hJtri hPunit hQunit hQf0 hPfL hNF hQf22b hcorner hPtri hQtri hP22one hQ22one

theorem deepest_gauge_construction_ofBundle (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r)
    -- The block-triangular boundary-frame bundle (the 16 destructured items of
    -- `deepestPoint_frame_pivot_triangular_exists` in the arbitrary route, or `…_front_exists` in the
    -- hJfront-free FRONT route). The body is frame-generic: it consumes only these bundle facts (`hJtri`
    -- gives `J = frontEmbed` internally), NEVER `hJfront`. So ONE factoring serves BOTH routes.
    (Jb : Fin r ↪ Fin (H ((lastLayer hL).succ)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hJtri : Jb.trans (finCongr (H_lastLayer_succ H hL)).toEmbedding = frontEmbed H r hr)
    (hPunit : ∀ s : Fin L, IsUnit (Pf s)) (hQunit : ∀ s : Fin L, IsUnit (Qf s))
    (hQf0 : Qf (firstLayer hL)
        = (1 : Matrix (Fin (H (firstLayer hL).succ)) (Fin (H (firstLayer hL).succ)) ℝ))
    (hPfL : Pf (lastLayer hL)
        = (1 : Matrix (Fin (H (lastLayer hL).castSucc)) (Fin (H (lastLayer hL).castSucc)) ℝ))
    (hNF : ∀ s : Fin L, (s : ℕ) + 1 ≠ L →
        Pf s * (deepestPoint H r B hB hr hL s) * Qf s
          = Matrix.of (fun (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) =>
              if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0))
    (hQf22b : IsUnit ((Matrix.reindex (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) Jb)
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) Jb)
        (Qf (lastLayer hL))).toBlocks₂₂))
    (hcorner : Matrix.reindex (rThresholdSplit r (H ((lastLayer hL).castSucc)) (hr _))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) Jb)
        ((deepestPoint H r B hB hr hL (lastLayer hL)) * Qf (lastLayer hL))
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (hPtri : (Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
        (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
        (Pf (firstLayer hL))).toBlocks₁₂ = 0)
    (hQtri : (Matrix.reindex (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) Jb)
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) Jb)
        (Qf (lastLayer hL))).toBlocks₂₁ = 0)
    (hP22one : (Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
        (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
        (Pf (firstLayer hL))).toBlocks₂₂
        = (1 : Matrix (Fin (H (firstLayer hL).castSucc - r)) (Fin (H (firstLayer hL).castSucc - r)) ℝ))
    (hQ22one : (Matrix.reindex (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) Jb)
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) Jb)
        (Qf (lastLayer hL))).toBlocks₂₂
        = (1 : Matrix (Fin (H ((lastLayer hL).succ) - r)) (Fin (H ((lastLayer hL).succ) - r)) ℝ))
    (hInterior : ∀ s : Fin L, 0 < (s : ℕ) → (s : ℕ) + 1 < L →
        Pf s = (1 : Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ) ∧
          Qf s = (1 : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)) :
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
    -- Frame-generic gauge construction from an ARBITRARY block-triangular boundary-frame bundle
    -- (`Jb, Pf, Qf` + facts). Formerly the `L ≥ 3` arm of `deepest_gauge_construction`, factored out so
    -- BOTH the arbitrary (`triangular_exists`, from `hJfront`) and the hJfront-free FRONT
    -- (`triangular_front_exists`, from `hcolfront`) routes reuse the identical body. #120 CLOSED.
    -- `split` (obligation (i), MP reindex carrying the deepest point to `0`). Use the CONCRETE
    -- `deepestSplit` witness (not the `deepestSplit_exists` existential) so the PIN2 cert's round-trip
    -- hypothesis `hsplit` discharges by `rfl` — the index-decode lemmas (`gaugeReadX/Y/Z_deepestSplit`,
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
    -- The bundle `Jb, Pf, Qf` + its facts are PARAMETERS (frame-generic body). The outer-reindex pivot
    -- embedding lives on `Fin (H (Fin.last L))`; `Jb` on `Fin (H (lastLayer).succ)`.
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
    -- **`hTilde` (CLOSED, #120):** `π̃ := regStraightenOf2 (deepestEFull ∘ coreAbsorb.symm)` is a local
    -- diffeo at `0` (ContDiff + invertible strict-deriv `eTilde`). ContDiff is routine (deepestEFull +
    -- coreAbsorb.symm both ContDiff); the invertible strict-deriv uses the degree-2 core-block-vanishing
    -- `∂deepestEFull/∂core(0) = 0` (so `π̃`'s reg-reg block stays PIN1's invertible `F` despite
    -- `coreAbsorb.symm`'s reg→core shear) — the value-fold atom (thread 31), parallel to PIN1's
    -- `deepestEPivot_regSlice_fderiv`. Discharged below (no sorry).
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
    -- Assemble the bundle: all data (`split`, `coreAbsorb`, `regStraighten` + their facts) is in scope;
    -- the final `?_` is the migrated `loss_squeeze` RLCT-equality (the route-B close below).
    refine ⟨deepestNGauge H r, split, coreAbsorb, regStraighten, hsplit_mp, hsplit_base, hca_base,
      hca_reg, hca_spec, hca_rlct, hra_cont, hra_base, hra_core, hra_spec, hra_rlct, ?_⟩
    -- **hinterface (L ≥ 3, CLOSED #120).** Interior frames ARE the identity — supplied by the bundle's
    -- `hInterior` (endpoint override is boundary-only); the two interior branches discharge below.
    have hinterface : ∀ (s : Fin L) (_ : (s : ℕ) + 1 < L),
        Qf s = (1 : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) ∧
          Pf ⟨(s : ℕ) + 1, by omega⟩ = (1 : Matrix (Fin (H (⟨(s : ℕ) + 1, by omega⟩ : Fin L).castSucc))
            (Fin (H (⟨(s : ℕ) + 1, by omega⟩ : Fin L).castSucc)) ℝ) := by
      intro s hs
      refine ⟨?_, ?_⟩
      · rcases Nat.eq_zero_or_pos (s : ℕ) with hs0 | hspos
        · have hsf : s = firstLayer hL := Fin.ext (by simp [firstLayer, hs0])
          rw [hsf]; exact hQf0
        · -- Strict-interior layer `s` (`0 < s`, `s+1 < L`): the chosen frame is the identity.
          exact (hInterior s hspos hs).2
      · rcases Nat.lt_or_ge ((s : ℕ) + 1) (L - 1) with hint | hbdy
        · -- Strict-interior layer `s+1` (`0 < s+1`, `s+2 < L` from `hint`): the frame is the identity.
          have h1 : 0 < (s : ℕ) + 1 := by omega
          have h2 : (s : ℕ) + 1 + 1 < L := by omega
          exact (hInterior ⟨(s : ℕ) + 1, by omega⟩ h1 h2).1
        · have hsf : (⟨(s : ℕ) + 1, by omega⟩ : Fin L) = lastLayer hL :=
            Fin.ext (by simp only [lastLayer]; omega)
          rw [hsf]; exact hPfL
    -- PIN 2: the loss squeeze (ROUTE-B close, `coreΦ → Score`, 2026-06-25). The migrated `loss_squeeze`
    -- field is the RLCT-EQUALITY `rlctAt(dlnLoss) = rlctAtOn(Sreg_E + coreΦ)`. We prove it from the TRUE
    -- Score-sandwich `hsq` (`deepest_loss_squeeze`, axiom-clean) via `rlctAtOn_squeeze`
    -- (⟹ `rlctAtOn(Sreg_E + Score)`) + the analytic-unit diffeo bridge `rlctAtOn(Sreg_E + Score) =
    -- rlctAtOn(Sreg_E + coreΦ)` (`Ψ : S1 ↦ (I−K)·S1`). `Score = frobSqMat(Rcore)` (the `hscore`/`hScoreDef`
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
      · -- `Φscore` measurable: reg sum-of-squares + `Score` (a frobSqMat of a continuous matrix in `w`).
        rw [hΦscore, hScoreDef]
        apply Measurable.add
        · exact (Finset.measurable_sum _ (fun i _ =>
            ((measurable_pi_apply i).comp
              (continuous_fst.comp (hra_cont.comp split.continuous)).measurable).pow_const _))
        · -- **MEASURABILITY of `Score` (mechanical, entrywise).** `Score w = frobSqMat(Schur(Mw w))`,
          -- `Mw w = reindex(endpointP0·(prod(symm w)−B)·endpointQL)` — CONTINUOUS in `w` (`continuous_Mw`).
          -- The only non-continuous piece is `(Mw₁₁+1)⁻¹`, but it is MEASURABLE entrywise: `inv_def` gives
          -- `A⁻¹ = (Ring.inverse A.det) • A.adjugate`, with `Continuous.matrix_det`/`Continuous.matrix_adjugate`
          -- continuous and `Ring.inverse : ℝ → ℝ` measurable. So each Schur-leak entry is measurable
          -- (∑∑ of products of measurable scalars), and `frobSqMat` (finite ∑∑ of squares) is measurable.
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
    -- **Step 2 (L ≥ 3): grouped-`G0` diffeo (CLOSED #120).** The cert's `(T1, Y1)` Ψ generalises to the
    -- two-grouping `G0 = prodAux (L−1)`, `G1 = last layer`; the recursive multi-factor reparam, below.
    have hstep2 : rlctAtOn Φscore wstar
        = rlctAtOn
            (fun x : Fin (flatDim H) → ℝ =>
              (∑ i, (regStraighten (split x)).1 i ^ 2)
                + deepestCoreF H r (coreAbsorb (split x)).2.1)
            ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) := by
      -- ===== L ≥ 3 diffeo bridge (general Ψ_conj joint move), banked-leaf assembly =====
      -- (0) hDA / hbdy (general-`L` pivot-unit + boundary), and `hQUpper` feeding `hDA`.
      have hQUpper : (Matrix.reindex
          (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
          (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
          (Qf (lastLayer hL))).toBlocks₂₁ = 0 := by rw [hpivJ]; exact hQtri
      have hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s) :=
        deepBlkA_isUnit_gen H r B hB hr hL hL2 htop J hJfront' Qf hcorner' hQUpper
      have hbdy : ∀ s : Fin L, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0 :=
        deepBlk_boundary_gen H r B hB hr hL hL2
      -- (1) per-layer block-triangularity (∀ s : Fin L) the assembled bridge / Step Θ consume.
      have hPtri2 : ∀ s : Fin L, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
          (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0 := by
        intro s
        rcases Nat.eq_zero_or_pos (s : ℕ) with hs0 | hspos
        · have hsf : s = firstLayer hL := Fin.ext (by simp [firstLayer, hs0])
          rw [hsf]; exact hPtri
        · rcases Nat.lt_or_ge ((s : ℕ) + 1) L with hlt | hge
          · rw [(hInterior s hspos hlt).1]; exact reindex_one_toBlocks₁₂_zero _
          · have hsf : s = lastLayer hL := by
              apply Fin.ext; simp only [lastLayer]; have := s.isLt; omega
            rw [hsf, hPfL]; exact reindex_one_toBlocks₁₂_zero _
      have hQtri2 : ∀ s : Fin L, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
          (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0 := by
        intro s
        rcases Nat.eq_zero_or_pos (s : ℕ) with hs0 | hspos
        · have hsf : s = firstLayer hL := Fin.ext (by simp [firstLayer, hs0])
          rw [hsf, hQf0]; exact reindex_one_toBlocks₂₁_zero _
        · rcases Nat.lt_or_ge ((s : ℕ) + 1) L with hlt | hge
          · rw [(hInterior s hspos hlt).2]; exact reindex_one_toBlocks₂₁_zero _
          · have hsf : s = lastLayer hL := by
              apply Fin.ext; simp only [lastLayer]; have := s.isLt; omega
            rw [hsf]
            have h := hQtri
            rw [← hpivJ, hJfront', pivotThresholdSplit_pivotJSucc_frontEmbed H r hr hL] at h
            exact h
      -- (2) the `rThr`-form last-layer facts (bundle `Jb`-pivot → `rThr` via front-embed) and the
      -- endpoint (`endpointP0` / `endpointQL`) block facts the keystone consumes.
      have hQtriR : (Matrix.reindex (rThresholdSplit r (H ((lastLayer hL).succ)) (hr _))
          (rThresholdSplit r (H ((lastLayer hL).succ)) (hr _))
          (Qf (lastLayer hL))).toBlocks₂₁ = 0 := by
        have h := hQtri
        rw [← hpivJ, hJfront', pivotThresholdSplit_pivotJSucc_frontEmbed H r hr hL] at h
        exact h
      have hQ22R : (Matrix.reindex (rThresholdSplit r (H ((lastLayer hL).succ)) (hr _))
          (rThresholdSplit r (H ((lastLayer hL).succ)) (hr _))
          (Qf (lastLayer hL))).toBlocks₂₂ = 1 := by
        have h := hQ22one
        rw [← hpivJ, hJfront', pivotThresholdSplit_pivotJSucc_frontEmbed H r hr hL] at h
        exact h
      have hfl : (firstLayer hL : Fin L) = ⟨0, by omega⟩ := Fin.ext (by simp [firstLayer])
      have hcastQ : ((lastLayer hL).succ) = Fin.last L :=
        Fin.ext (by simp only [lastLayer, Fin.succ, Fin.last]; omega)
      have hPtri' : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (rThresholdSplit r (H 0) (hr 0)) (endpointP0 H hL Pf)).toBlocks₁₂ = 0 := by
        simpa only [endpointP0, hfl] using hPtri
      have hP22' : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
          (endpointP0 H hL Pf)).toBlocks₂₂ = 1 := by
        simpa only [endpointP0, hfl] using hP22one
      have hQtri' : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (endpointQL H hL Qf)).toBlocks₂₁ = 0 := by
        rw [hJfront', pivotThresholdSplit_frontEmbed H r hr]
        show (Matrix.reindex (rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)))
            (rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)))
            (hcastQ ▸ Qf (lastLayer hL))).toBlocks₂₁ = 0
        exact reindex_rThr_toBlocks21_zero_cast H r hr hcastQ (Qf (lastLayer hL)) hQtriR
      have hQ22' : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (endpointQL H hL Qf)).toBlocks₂₂ = 1 := by
        rw [hJfront', pivotThresholdSplit_frontEmbed H r hr]
        show (Matrix.reindex (rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)))
            (rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)))
            (hcastQ ▸ Qf (lastLayer hL))).toBlocks₂₂ = 1
        exact reindex_rThr_toBlocks22_one_cast H r hr hcastQ (Qf (lastLayer hL)) hQ22R
      have hS3b : Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (endpointP0 H hL Pf * B * endpointQL H hL Qf)
        = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 := by
        have hBprod : B = prod H (deepestPoint H r B hB hr hL) :=
          (deepestPoint_isDeep H r B hB hr hL).1.symm
        have hframe0 : ∀ s : Fin L,
            framedParamsPivot H r hr hL J Pf Qf (split wstar) s
              = Pf s * (deepestPoint H r B hB hr hL) s * Qf s := by
          intro s
          have hdecode : (paramsEquivFlat H).symm wstar = deepestPoint H r B hB hr hL := by
            rw [hwstar]; exact (paramsEquivFlat H).symm_apply_apply _
          rw [hsplit wstar, ← hdecode]
          exact framedParamsPivot_eq_frame_of_front H r B hB hr hL J hJfront' Pf Qf hNF hPfL
            hcorner' wstar s
        have htel : prod H (framedParamsPivot H r hr hL J Pf Qf (split wstar))
            = endpointP0 H hL Pf * prod H (deepestPoint H r B hB hr hL) * endpointQL H hL Qf :=
          endpoint_telescoping_eq H hL (deepestPoint H r B hB hr hL)
            (framedParamsPivot H r hr hL J Pf Qf (split wstar)) Pf Qf hframe0 hinterface
        have hsplit0 : split wstar = (0 : DeepestSplit H r (deepestNGauge H r)) := hsplit_base
        rw [hBprod, ← htel, hsplit0,
          show (0 : DeepestSplit H r (deepestNGauge H r))
            = (((0 : Fin (deepestNReg H r) → ℝ), (0 : Fin (flatDim (deepestM H r)) → ℝ),
                (0 : Fin (deepestNGauge H r) → ℝ)) : DeepestSplit H r (deepestNGauge H r)) from rfl,
          framedParamsPivot_coreZero H r hr hL J Pf Qf 0 0,
          show (((0 : Fin (deepestNReg H r) → ℝ), (0 : Fin (deepestNGauge H r) → ℝ))
              : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
            = (0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) from rfl]
        exact reindex_prodAux_framedParamsRegPivot_zero H r hr hL hL2 J Pf Qf
      have hP11inv : Invertible (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (rThresholdSplit r (H 0) (hr 0)) (endpointP0 H hL Pf)).toBlocks₁₁ :=
        endpoint_toBlocks₁₁_invertible_of_blockTri (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (rThresholdSplit r (H 0) (hr 0)) (endpointP0 H hL Pf))
          ((Matrix.isUnit_submatrix_equiv _ _).mpr (isUnit_endpointP0 H hL Pf hPf)) hP22'
          (Or.inl hPtri')
      have hQ11inv : Invertible (Matrix.reindex
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (endpointQL H hL Qf)).toBlocks₁₁ :=
        endpoint_toBlocks₁₁_invertible_of_blockTri (Matrix.reindex
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (endpointQL H hL Qf))
          ((Matrix.isUnit_submatrix_equiv _ _).mpr (isUnit_endpointQL H hL Qf hQf)) hQ22'
          (Or.inr hQtri')
      -- (3) the flat cutoff diffeo `psi = split⁻¹ ∘ (χ-cutoff psiSplitRawGen) ∘ split`. Pick a
      -- small-radius bump χ whose support sits inside the (open) invertibility region.
      obtain ⟨ε, hεpos, hεsub⟩ :=
        Metric.mem_nhds_iff.mp (eventually_psiInvBundle H r hr hL J hJfront' Pf Qf)
      set χ : ContDiffBump (0 : DeepestSplit H r (deepestNGauge H r)) :=
        ⟨ε / 4, ε / 2, by linarith, by linarith⟩ with hχdef
      have hχsub : ∀ q ∈ tsupport (fun y => ((χ y : ℝ))),
          psiInvBundle H r hr hL J Pf Qf q := by
        have hts : tsupport (fun y => ((χ y : ℝ))) = Metric.closedBall 0 χ.rOut := χ.tsupport_eq
        intro q hq
        rw [hts] at hq
        have hlt : χ.rOut < ε := by rw [hχdef]; show ε / 2 < ε; linarith
        exact hεsub (Metric.closedBall_subset_ball hlt hq)
      have hraw0 : psiSplitRawGen H r hr hL J Pf Qf 0 = 0 :=
        psiSplitRawGen_zero H r hr hL J hJfront' Pf Qf
      have hderiv0 : HasStrictFDerivAt (fun q => psiSplitRawGen H r hr hL J Pf Qf q - q)
          (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] DeepestSplit H r (deepestNGauge H r)) 0 :=
        hasStrictFDerivAt_psiSplitDeltaGen_zero H r hr hL hL2 J hJfront' Pf Qf hQf0 hPfL hPf hQf
          hPtri hP22one hQtriR hQ22R hInterior
      have hbase : deepestSplit H r hr hL wstar wstar = 0 := hsplit_base
      have hcontdiff : ContDiff ℝ (⊤ : ℕ∞)
          (deepestPsiFlatCut H r hr hL (psiSplitRawGen H r hr hL J Pf Qf) χ wstar) :=
        contDiff_deepestPsiFlatCut H r hr hL (psiSplitRawGen H r hr hL J Pf Qf) χ
          (hcd_psiSplitRawGen H r hr hL J Pf Qf χ hχsub) wstar
      have hderiv : HasStrictFDerivAt
          (deepestPsiFlatCut H r hr hL (psiSplitRawGen H r hr hL J Pf Qf) χ wstar)
          (ContinuousLinearMap.id ℝ (Fin (flatDim H) → ℝ)) wstar :=
        hasStrictFDerivAt_deepestPsiFlatCut H r hr hL (psiSplitRawGen H r hr hL J Pf Qf) χ
          hraw0 hderiv0 wstar hbase
      have hfix : deepestPsiFlatCut H r hr hL (psiSplitRawGen H r hr hL J Pf Qf) χ wstar wstar
          = wstar :=
        deepestPsiFlatCut_fixpoint H r hr hL (psiSplitRawGen H r hr hL J Pf Qf) χ hraw0 wstar hbase
      have hsplitPsi : ∀ᶠ x : (Fin (flatDim H) → ℝ) in nhds wstar,
          split (deepestPsiFlatCut H r hr hL (psiSplitRawGen H r hr hL J Pf Qf) χ wstar x)
            = psiSplitRawGen H r hr hL J Pf Qf (split x) := by
        have hg := deepestPsiFlatCut_split_germ H r hr hL (psiSplitRawGen H r hr hL J Pf Qf) χ wstar
          hbase
        filter_upwards [hg] with x hx
        rw [hsplit, hsplit]; exact hx
      -- (4) hsub3reg (reg-energy preservation) via the banked general germ + the reg-slot value.
      have hsub3reg : ∀ᶠ x : (Fin (flatDim H) → ℝ) in nhds wstar,
          (∑ i, (regStraighten (psiSplitRawGen H r hr hL J Pf Qf (split x))).1 i ^ 2)
            = ∑ i, (regStraighten (split x)).1 i ^ 2 := by
        have hg := hsub3reg_gen_germ H r B hB hr hL hL2 J hJfront' Pf Qf hNF hQf0 hPfL hPf hQf
          hPtri hP22one hQtriR hQ22R hInterior hcorner' split hsplit
        filter_upwards [hg] with x hx
        simp only [hra_regval]; exact hx
      -- (5) hsub4core (core untwisting to `Score`) — lift the pointwise keystone to a germ over the
      -- basepoint neighbourhood (eventual corner-invertibility of chain / partProd / prod + the
      -- eventual cutoff-ball), discharging the readback `hC` per `x` via the banked decode.
      have hsub4core : ∀ᶠ x : (Fin (flatDim H) → ℝ) in nhds wstar,
          deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA
            (psiSplitRawGen H r hr hL J Pf Qf (split x))).2.1 = Score x := by
        have hqgerm : ∀ᶠ x : (Fin (flatDim H) → ℝ) in nhds wstar,
            psiSplitRawGen H r hr hL J Pf Qf (split x)
              ∈ Metric.closedBall (0 : DeepestSplit H r (deepestNGauge H r))
                ((cutoffBumpConj H r B hB hr hL hDA).rIn) := by
          have hpc : ContinuousAt (psiSplitRawGen H r hr hL J Pf Qf) (split wstar) := by
            rw [hsplit_base]
            have hd := hderiv0.hasFDerivAt.continuousAt
            have hs : ContinuousAt (fun q => (psiSplitRawGen H r hr hL J Pf Qf q - q) + q)
                (0 : DeepestSplit H r (deepestNGauge H r)) := hd.add continuousAt_id
            simpa using hs
          have hcont : ContinuousAt (fun x => psiSplitRawGen H r hr hL J Pf Qf (split x)) wstar :=
            hpc.comp split.continuous.continuousAt
          have hval : psiSplitRawGen H r hr hL J Pf Qf (split wstar) = 0 := by
            rw [hsplit_base]; exact hraw0
          have htend : Filter.Tendsto (fun x => psiSplitRawGen H r hr hL J Pf Qf (split x))
              (nhds wstar) (nhds 0) := by rw [← hval]; exact hcont
          exact htend (Metric.closedBall_mem_nhds 0 (cutoffBumpConj H r B hB hr hL hDA).rIn_pos)
        have hMidgerm :=
          eventually_isUnit_prod_decode_pivot_toBlocks₁₁ H r B hB hr hL hDA J hJfront'
        have hLayergerm := eventually_all_isUnit_deepestChain_decode_toBlocks₁₁ H r B hB hr hL hDA
        have hPartgerm :=
          eventually_all_isUnit_partProd_deepestChain_decode_toBlocks₁₁ H r B hB hr hL hDA
        filter_upwards [hqgerm, hMidgerm, hLayergerm, hPartgerm] with x hq hMid hLayerU hPartU
        have hLayerI : ∀ k, k < L →
            Invertible (deepestChain H r hr ((paramsEquivFlat H).symm x) k).toBlocks₁₁ :=
          fun k hk => (hLayerU k hk).invertible
        have hPartI : ∀ k, k ≤ L →
            Invertible (partProd (deepestChain H r hr ((paramsEquivFlat H).symm x)) k).toBlocks₁₁ :=
          fun k hk => (hPartU k hk).invertible
        have hC := coreAbsorbConj_reindex_eq_blockSchur_movedC_decode H r B hB hr hL hL2 J hJfront'
          Pf Qf hNF hPfL hcorner' hQf0 hPtri hP22one hPf hQtriR hQ22R hQf hInterior x hLayerI hPartI
        exact deepestCoreF_coreAbsorbConj_psiSplitRawGen_eq_score_at_chart H r B hB hr hL hDA J
          hJfront' Pf Qf (split x) x hq hPtri' hQtri' hP22' hQ22' hS3b hP11inv hQ11inv
          hMid.invertible hC hLayerI hPartI Score hScoreDef
      -- (6) assemble: LINK-1 (Ψ_conj analytic reduction) + LINK-2 (Step Θ) via the banked bridge.
      rw [show coreAbsorb = deepestCoreAbsorb H r hr hL from hca_def,
        show (paramsEquivFlat H) (deepestPoint H r B hB hr hL) = wstar from hwstar.symm]
      exact deepest_diffeo_bridge_gen_assembled H r B hB hr hL hL2 hDA hbdy J hJfront' Pf Qf
        hPf hQf hQf0 hPfL hQf22 hPtri2 hQtri2 split hsplit_mp regStraighten hra_regval
        (deepestPsiFlatCut H r hr hL (psiSplitRawGen H r hr hL J Pf Qf) χ wstar)
        (psiSplitRawGen H r hr hL J Pf Qf) wstar hsplit_base hcontdiff hderiv hfix hsplitPsi
        hsub3reg Score hsub4core Φscore hΦscore
    rw [hstep1, hstep2]

/-- **The general-`L` gauge construction** (statement-preserving wrapper over
`deepest_gauge_construction_ofBundle`, decision-b refactor). `L < 3` dispatches to the hoisted
clean-three `deepest_gauge_construction_L2`; `L ≥ 3` obtains the arbitrary block-triangular
boundary-frame bundle (`deepestPoint_frame_pivot_triangular_exists`, from `htop` + `hJfront`) and
feeds the frame-generic `_ofBundle`. The statement is byte-identical to the pre-refactor
`deepest_gauge_construction`; its only consumers (`deepest_gauge_chart_construct`, `AxCheck`) are
unaffected. -/
theorem deepest_gauge_construction (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (hJfront : ((deepestPoint_frame_pivot_exists H r B hB hr hL hL2).choose).trans
        (finCongr (H_lastLayer_succ H hL)).toEmbedding = frontEmbed H r hr)
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
  rcases Nat.lt_or_ge L 3 with hLlt | hL3
  · exact deepest_gauge_construction_L2 H r B hB hr hL hL2 hpos hJfront htop hLlt
  · obtain ⟨Jb, Pf, Qf, hJtri, hPunit, hQunit, hQf0, hPfL, hNF, hQf22b, hcorner, hPtri, hQtri,
        hP22one, hQ22one, hInterior⟩ :=
      deepestPoint_frame_pivot_triangular_exists H r B hB hr hL hL2 htop hJfront
    exact deepest_gauge_construction_ofBundle H r B hB hr hL hL2 hpos htop
      Jb Pf Qf hJtri hPunit hQunit hQf0 hPfL hNF hQf22b hcorner hPtri hQtri hP22one hQ22one
      hInterior

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
