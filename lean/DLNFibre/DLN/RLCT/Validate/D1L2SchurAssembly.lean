import DLNFibre.DLN.RLCT.Validate.D1IFTResidualProducer
import DLNFibre.DLN.RLCT.Validate.D1L2ExplicitCoreProducer
import DLNFibre.DLN.RLCT.Foundations.S1Spectator
import DLNFibre.DLN.RLCT.Foundations.S1Fubini
import DLNFibre.DLN.RLCT.Foundations.S1Local

/-!
# `DLNFibre.DLN.RLCT.Validate.D1L2SchurAssembly` — Route-A "everything else is banked"

The corrected D1 `≥`-leg (`genm-hAtV` / `D1L2ExplicitCoreProducer`) reduces the whole leg to ONE
crux `d1ge_L2_hAtV_explicit`, whose sole content (per the `genm-hAtV` statement card + the banked
Codex xhigh crux analysis) is the EXPLICIT Schur corner-elimination chart transfer plus the slice
factorisation. This module lands the **downstream half** of that crux — Codex's decomposition steps
6–9 — as a single sorry-free reduction theorem: given the explicit-chart data (the `C¹` residual `qₑ`
+ the chart transfer `hchart` + the slice a.e.-nonvanishing `hRne`) AND the explicit slice
factorisation (a measure-preserving reindex of the flat slice into the reduced-core flat coordinates
× the flat spectators, together with the bounded-unit Gram factor), the producer conclusion follows
mechanically. Everything here is the composition of ALREADY-BANKED bricks:

* `rlctAt_ge_nReg_add_slice_of_residual` (`D1IFTResidualProducer`) — the `nReg`-block quasi-split
  from the `C¹` chart transfer (Codex step 6, `rlct_additive_smooth_block` inside);
* `rlctAtOn_unit_invariant_aux` (`S1Local`) — peel the bounded, non-vanishing Gram/Jacobian unit
  (Codex step 8, modelidwit's Gram-sandwich verdict);
* `rlctAtOn_comp_homeomorph` (`S1Fubini`) — the essential measure-preserving reindex, twice;
* `rlctAtOn_spectator_peel` (`S1Spectator`) — the flat-direction Fubini peel (Codex step 7, the
  single load-bearing new analytic brick, already banked).

The isolated WALL this reduction leaves is EXACTLY Codex's step 5: constructing the explicit rational
corner-elimination map as a local measurable chart with Jacobian/unit control — i.e. producing an
instance of the hypotheses `qₑ`, `hchart`, `hRne`, `e`, `u`, `hfact` at the real DLN loss. That is the
general-`v` analogue of the deepest-point gauge chart (a fresh multi-file analytic build; Item 81); it
is NOT discharged here. This module makes precise "given the explicit chart, everything else is banked".
-/

open MeasureTheory
open scoped ENNReal Topology BigOperators
namespace DLNFibre.DLN.RLCT

-- The reduced-widths type ascriptions `dlnLoss (fun s => H s - r) 0` force repeated `whnf` of the
-- `Fin (flatDim …)` / `Params …` dependent types through the banked-brick defeq checks; the default
-- 200000 heartbeats is exceeded by the four-step `rw` chain assembling the slice reduction.
set_option maxHeartbeats 800000 in
/-- **Route-A producer from an explicit Schur chart (L = 2).** Given, at a general optimal `v`, the
explicit-chart data feeding the banked `nReg`-quasi-split (`qₑ` a `C¹` residual, the chart transfer
`hchart`, the slice a.e.-nonvanishing `hRne`) AND the explicit slice factorisation

    ∑ᵢ qₑ(0, t)ᵢ² = u t · dlnLoss (H − r) 0 ((paramsEquivFlat (H − r)).symm (e t).1)

(a measure-preserving reindex `e` of the flat slice `Y` onto the reduced-core flat coordinates ×
the flat spectators, with `u` a bounded non-vanishing Gram unit), the D1 `≥`-leg producer conclusion
holds, with witness `P = (paramsEquivFlat (H − r)).symm (e t0).1` (dominated by the PROVEN Theorem-4
comparison `core_zero_le_of_params` downstream). Codex steps 6–9 as one sorry-free reduction; the
hypotheses are EXACTLY the step-5 chart-certification wall. -/
theorem d1ge_L2_hAtV_of_explicit_chart
    {n specDim : ℕ} {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasureSpace Y] [BorelSpace Y]
    [FiniteDimensional ℝ Y] [ProperSpace Y] [IsFiniteMeasureOnCompacts (volume : Measure Y)]
    (H : Fin (2 + 1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (v : Params H)
    (qₑ : (Fin (nRegL2 H r) → ℝ) × Y → EuclideanSpace ℝ (Fin n)) (hq : ContDiff ℝ 1 qₑ) (t0 : Y)
    (hchart : rlctAt H (dlnLoss H B) v
        = rlctAtOn (fun p : (Fin (nRegL2 H r) → ℝ) × Y =>
            (∑ i, p.1 i ^ 2) + (∑ i, qₑ p i ^ 2)) ((0 : Fin (nRegL2 H r) → ℝ), t0))
    (hRne : ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U),
        (∑ i, qₑ ((0 : Fin (nRegL2 H r) → ℝ), z) i ^ 2) ≠ 0)
    (e : Y ≃ₜ ((Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin specDim → ℝ)))
    (he_mp : MeasurePreserving e (volume : Measure Y) volume)
    (he_emb : MeasurableEmbedding e)
    (u : Y → ℝ) (hu_meas : Measurable u) (ua ub : ℝ) (hua : 0 < ua)
    (hu_bnd : ∃ U ∈ 𝓝 t0, ∀ w ∈ U, ua ≤ |u w| ∧ |u w| ≤ ub)
    (hfact : ∀ t : Y, (∑ i, qₑ ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2)
        = u t * dlnLoss (fun s => H s - r)
            (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last 2))) ℝ)
            ((paramsEquivFlat (fun s => H s - r)).symm (e t).1)) :
    ∃ P : Params (fun s => H s - r),
      (nRegL2 H r : ℝ≥0∞) / 2
          + rlctAtOn (fun A : Params (fun s => H s - r) =>
              dlnLoss (fun s => H s - r)
                (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last 2))) ℝ) A)
              P
        ≤ rlctAt H (dlnLoss H B) v := by
  classical
  -- the flat reduced core `coreF = dlnLoss (H−r) 0 ∘ (paramsEquivFlat (H−r)).symm`.
  set coreF : (Fin (flatDim (fun s => H s - r)) → ℝ) → ℝ :=
    fun w => dlnLoss (fun s => H s - r)
      (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last 2))) ℝ)
      ((paramsEquivFlat (fun s => H s - r)).symm w) with hcoreF
  -- STEP 6: the banked `nReg`-quasi-split from the `C¹` chart transfer.
  have hbound := rlctAt_ge_nReg_add_slice_of_residual H B v qₑ hq t0 hchart hRne
  -- rewrite the slice residual by the factorisation.
  have hslicefun :
      (fun t : Y => ∑ i, qₑ ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2)
        = fun t : Y => u t * coreF (e t).1 := by
    funext t; rw [hcoreF]; exact hfact t
  -- STEP 8: peel the bounded, non-vanishing Gram unit `u`.
  have hstep8 : rlctAtOn (fun t : Y => ∑ i, qₑ ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2) t0
      = rlctAtOn (fun t : Y => coreF (e t).1) t0 := by
    rw [hslicefun]
    exact rlctAtOn_unit_invariant_aux (fun t : Y => coreF (e t).1) u t0 ua ub hua hu_meas hu_bnd
  -- STEP (7a): the essential measure-preserving reindex `e`.
  have hstep7a : rlctAtOn (fun t : Y => coreF (e t).1) t0
      = rlctAtOn (fun p : (Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin specDim → ℝ) => coreF p.1)
          (e t0) :=
    rlctAtOn_comp_homeomorph e he_mp he_emb
      (fun p : (Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin specDim → ℝ) => coreF p.1) t0
  -- STEP 7: the flat-direction Fubini spectator peel.
  have hstep7b :
      rlctAtOn (fun p : (Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin specDim → ℝ) => coreF p.1)
          (e t0)
        = rlctAtOn coreF (e t0).1 := by
    have h := rlctAtOn_spectator_peel coreF (e t0).1 (e t0).2
      ⟨Metric.ball ((e t0).2) 1, Metric.isOpen_ball, Metric.mem_ball_self (by norm_num),
        measure_ball_lt_top⟩
    rwa [Prod.mk.eta] at h
  -- STEP 9: transport the flat reduced-core RLCT back to `Params (H−r)` at `P` (forward-homeo route).
  have hstep9 : rlctAtOn coreF (e t0).1
      = rlctAtOn (fun A : Params (fun s => H s - r) =>
          dlnLoss (fun s => H s - r)
            (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last 2))) ℝ) A)
          ((paramsEquivFlat (fun s => H s - r)).symm (e t0).1) := by
    set eFwd : Params (fun s => H s - r) ≃ₜ (Fin (flatDim (fun s => H s - r)) → ℝ) :=
      ⟨(paramsEquivFlat (fun s => H s - r)).toEquiv, continuous_paramsEquivFlat (fun s => H s - r),
        continuous_paramsEquivFlat_symm (fun s => H s - r)⟩
    have hmp : MeasurePreserving eFwd (volume : Measure (Params (fun s => H s - r))) volume :=
      measurePreserving_paramsEquivFlat (fun s => H s - r)
    have hemb : MeasurableEmbedding eFwd := (paramsEquivFlat (fun s => H s - r)).measurableEmbedding
    have key := rlctAtOn_comp_homeomorph eFwd hmp hemb coreF
      ((paramsEquivFlat (fun s => H s - r)).symm (e t0).1)
    have hew : eFwd ((paramsEquivFlat (fun s => H s - r)).symm (e t0).1) = (e t0).1 := by
      change (paramsEquivFlat (fun s => H s - r))
          ((paramsEquivFlat (fun s => H s - r)).symm (e t0).1) = (e t0).1
      exact (paramsEquivFlat (fun s => H s - r)).apply_symm_apply (e t0).1
    rw [hew] at key
    have hcomp : (fun A : Params (fun s => H s - r) => coreF (eFwd A))
        = fun A : Params (fun s => H s - r) =>
          dlnLoss (fun s => H s - r)
            (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last 2))) ℝ) A := by
      funext A
      change dlnLoss (fun s => H s - r)
          (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last 2))) ℝ)
          ((paramsEquivFlat (fun s => H s - r)).symm (eFwd A)) = _
      congr 1
      change (paramsEquivFlat (fun s => H s - r)).symm ((paramsEquivFlat (fun s => H s - r)) A) = A
      exact (paramsEquivFlat (fun s => H s - r)).symm_apply_apply A
    rw [hcomp] at key
    exact key.symm
  -- assemble the slice reduction.
  have hslice : rlctAtOn (fun t : Y => ∑ i, qₑ ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2) t0
      = rlctAtOn (fun A : Params (fun s => H s - r) =>
          dlnLoss (fun s => H s - r)
            (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last 2))) ℝ) A)
          ((paramsEquivFlat (fun s => H s - r)).symm (e t0).1) := by
    rw [hstep8, hstep7a, hstep7b, hstep9]
  exact ⟨(paramsEquivFlat (fun s => H s - r)).symm (e t0).1, by rw [← hslice]; exact hbound⟩

end DLNFibre.DLN.RLCT
