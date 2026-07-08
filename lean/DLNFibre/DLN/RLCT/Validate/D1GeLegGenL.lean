import DLNFibre.DLN.RLCT.Validate.D1IFTResidualProducer
import DLNFibre.DLN.RLCT.Validate.D1L2ExplicitCoreProducer
import DLNFibre.DLN.RLCT.Foundations.S1Spectator
import DLNFibre.DLN.RLCT.Foundations.S1Fubini
import DLNFibre.DLN.RLCT.Foundations.S1Local

/-!
# `DLNFibre.DLN.RLCT.Validate.D1GeLegGenL` — the general-`L` D1 `≥`-leg interface (chart-consumer + wiring)

The general-`L` analogues of the two L = 2 assembly bricks that reduce the D1 `≥`-leg
(`rlctAt_deepest_le_of_optimal`, Skeleton) to the single explicit-Schur chart obligation. Both are
`L`-agnostic in their bodies — every measure-theoretic brick they use
(`rlctAt_ge_nReg_add_slice_of_residual`, `rlctAtOn_unit_invariant_aux`, `rlctAtOn_comp_homeomorph`,
`rlctAtOn_spectator_peel`, `core_zero_le_of_params`, `deepest_le_of_optimal_via_L2_ge`) is already
banked at general `L` (or type-generic). The L = 2-only content lives in the CHART DATA
(`qₑ`, `hchart`, `hRne`, `e`, `u`, `hfact`, `hAtV`), which stays a hypothesis here.

* `d1ge_hAtV_of_explicit_chart_genL` — the general-`L` port of `d1ge_L2_hAtV_of_explicit_chart`
  (`D1L2SchurAssembly`). Given the explicit-chart data at a general optimal `v`, the D1 `≥`-leg
  producer conclusion `∃ P, m/2 + rlctAtOn (dlnLoss (H−r) 0) P ≤ rlctAt H (dlnLoss H B) v` holds,
  with the `nReg`-count carried as a generic `m : ℕ` (`= r·(H₀+Hᴸ−r)` at the use-site). This is the
  general-`L` "given the explicit chart, everything else is banked" interface.

* `d1ge_deepestPoint_via_explicit_core_genL_wired` — the top-level wiring at general `L`, dropping
  the `hLlt : L < 3` pin the earlier `d1ge_L2_deepestPoint_via_explicit_core_genL` scaffold carried.
  Conditional on the deepest-side value `hDeepest` (= #44, general-`L` shape, carried as a hypothesis
  until it lands) and the producer `hAtV` (the explicit-Schur crux, general-`L` shape); discharges the
  core comparison `hCore` from the banked Params-domain Aoyagi Theorem 4 `core_zero_le_of_params`, and
  assembles via the banked abstract bridge `deepest_le_of_optimal_via_L2_ge`. Concludes
  `rlctAt H (dlnLoss H B) (deepestPoint …) ≤ rlctAt H (dlnLoss H B) v`.

**The isolated WALL (reported, not discharged here).** Producing the general-`L` chart data — the
iterated `L`-factor corner-elimination chart `Φ` (`ContDiff ℝ 2`, invertible derivative, fixing `0`),
the general-`L` block model (`BlockParams`/`blockFlatEquiv`), the Schur residual `qₑ` built on the
banked `schur_product_ldu_rec`, and its slice value (the LDU telescope with the gate-absorbing
reindex `e`/`u`). That is the general-`v` analogue of the ~1300-line L = 2 `D1L2PhiExpl` chart, a
fresh multi-file analytic build; it is NOT closed here.
-/

open MeasureTheory
open scoped ENNReal Topology BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

-- The reduced-widths type ascriptions `dlnLoss (fun s => H s - r) 0` force repeated `whnf` of the
-- `Fin (flatDim …)` / `Params …` dependent types through the banked-brick defeq checks; the default
-- heartbeats is exceeded by the four-step `rw` chain assembling the slice reduction (as in the L = 2
-- `D1L2SchurAssembly`).
set_option maxHeartbeats 800000 in
/-- **The general-`L` D1 `≥`-leg producer from an explicit Schur chart.** Given, at a general optimal
`v`, the explicit-chart data feeding the banked `nReg`-quasi-split (`qₑ` a `C¹` residual, the chart
transfer `hchart`, the slice a.e.-nonvanishing `hRne`) AND the explicit slice factorisation

    ∑ᵢ qₑ(0, t)ᵢ² = u t · dlnLoss (H − r) 0 ((paramsEquivFlat (H − r)).symm (e t).1)

(a measure-preserving reindex `e` of the flat slice `Y` onto the reduced-core flat coordinates ×
the flat spectators, with `u` a bounded non-vanishing Gram unit), the D1 `≥`-leg producer conclusion
holds, with witness `P = (paramsEquivFlat (H − r)).symm (e t0).1`. The general-`L` port of
`d1ge_L2_hAtV_of_explicit_chart`; the `nReg`-count is a generic `m : ℕ`. The body is `L`-agnostic —
`rlctAt_ge_nReg_add_slice_of_residual` (general `L`) + the type-generic RLCT reindex/peel bricks. -/
theorem d1ge_hAtV_of_explicit_chart_genL
    {m specDim n : ℕ} {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasureSpace Y] [BorelSpace Y]
    [FiniteDimensional ℝ Y] [ProperSpace Y] [IsFiniteMeasureOnCompacts (volume : Measure Y)]
    (H : Fin (L + 1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (v : Params H)
    (qₑ : (Fin m → ℝ) × Y → EuclideanSpace ℝ (Fin n)) (hq : ContDiff ℝ 1 qₑ) (t0 : Y)
    (hchart : rlctAt H (dlnLoss H B) v
        = rlctAtOn (fun p : (Fin m → ℝ) × Y =>
            (∑ i, p.1 i ^ 2) + (∑ i, qₑ p i ^ 2)) ((0 : Fin m → ℝ), t0))
    (hRne : ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U),
        (∑ i, qₑ ((0 : Fin m → ℝ), z) i ^ 2) ≠ 0)
    (e : Y ≃ₜ ((Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin specDim → ℝ)))
    (he_mp : MeasurePreserving e (volume : Measure Y) volume)
    (he_emb : MeasurableEmbedding e)
    (u : Y → ℝ) (hu_meas : Measurable u) (ua ub : ℝ) (hua : 0 < ua)
    (hu_bnd : ∃ U ∈ 𝓝 t0, ∀ w ∈ U, ua ≤ |u w| ∧ |u w| ≤ ub)
    (hfact : ∀ t : Y, (∑ i, qₑ ((0 : Fin m → ℝ), t) i ^ 2)
        = u t * dlnLoss (fun s => H s - r)
            (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
            ((paramsEquivFlat (fun s => H s - r)).symm (e t).1)) :
    ∃ P : Params (fun s => H s - r),
      (m : ℝ≥0∞) / 2
          + rlctAtOn (fun A : Params (fun s => H s - r) =>
              dlnLoss (fun s => H s - r)
                (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
              P
        ≤ rlctAt H (dlnLoss H B) v := by
  classical
  -- the flat reduced core `coreF = dlnLoss (H−r) 0 ∘ (paramsEquivFlat (H−r)).symm`.
  set coreF : (Fin (flatDim (fun s => H s - r)) → ℝ) → ℝ :=
    fun w => dlnLoss (fun s => H s - r)
      (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
      ((paramsEquivFlat (fun s => H s - r)).symm w) with hcoreF
  -- STEP 6: the banked `nReg`-quasi-split from the `C¹` chart transfer.
  have hbound := rlctAt_ge_nReg_add_slice_of_residual H B v qₑ hq t0 hchart hRne
  -- rewrite the slice residual by the factorisation.
  have hslicefun :
      (fun t : Y => ∑ i, qₑ ((0 : Fin m → ℝ), t) i ^ 2)
        = fun t : Y => u t * coreF (e t).1 := by
    funext t; rw [hcoreF]; exact hfact t
  -- STEP 8: peel the bounded, non-vanishing Gram unit `u`.
  have hstep8 : rlctAtOn (fun t : Y => ∑ i, qₑ ((0 : Fin m → ℝ), t) i ^ 2) t0
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
            (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
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
            (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A := by
      funext A
      change dlnLoss (fun s => H s - r)
          (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
          ((paramsEquivFlat (fun s => H s - r)).symm (eFwd A)) = _
      congr 1
      change (paramsEquivFlat (fun s => H s - r)).symm ((paramsEquivFlat (fun s => H s - r)) A) = A
      exact (paramsEquivFlat (fun s => H s - r)).symm_apply_apply A
    rw [hcomp] at key
    exact key.symm
  -- assemble the slice reduction.
  have hslice : rlctAtOn (fun t : Y => ∑ i, qₑ ((0 : Fin m → ℝ), t) i ^ 2) t0
      = rlctAtOn (fun A : Params (fun s => H s - r) =>
          dlnLoss (fun s => H s - r)
            (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
          ((paramsEquivFlat (fun s => H s - r)).symm (e t0).1) := by
    rw [hstep8, hstep7a, hstep7b, hstep9]
  exact ⟨(paramsEquivFlat (fun s => H s - r)).symm (e t0).1, by rw [← hslice]; exact hbound⟩

/-! ## The wired ≥-leg producer (general `L`, `hLlt` pin dropped) -/

/-- **The general-`L` D1 `≥`-leg, wired.** Drops the `hLlt : L < 3` pin that the earlier
`d1ge_L2_deepestPoint_via_explicit_core_genL` scaffold carried. Conditional on:

* `hDeepest` — the deepest-side value (= #44, general-`L` shape): the local RLCT at `deepestPoint`
  is `m/2` (the regular shift, `m = r·(H₀+Hᴸ−r)` at the use-site) plus the reduced-core RLCT AT THE
  ORIGIN `rlctAtOn (dlnLoss (H−r) 0) 0`. Phrased against the core RLCT at `0` (not `ofReal(lambdaCore)`)
  so the core comparison discharges WITHOUT the general-`L` R1 value (still open);
* `hAtV` — the explicit-Schur producer (general-`L` shape): `∃ P, m/2 + rlctAtOn (dlnLoss (H−r) 0) P
  ≤ rlctAt H (dlnLoss H B) v` — exactly what `d1ge_hAtV_of_explicit_chart_genL` delivers.

The core comparison `hCore : rlctAtOn (dlnLoss (H−r) 0) 0 ≤ rlctAtOn (dlnLoss (H−r) 0) P` is the
banked Params-domain Aoyagi Theorem 4 `core_zero_le_of_params` (general `L`, PROVEN); the ENNReal
assembly is the banked abstract bridge `deepest_le_of_optimal_via_L2_ge`. Concludes the D1 `≥`-leg
per-point obligation `rlctAt H (dlnLoss H B) (deepestPoint …) ≤ rlctAt H (dlnLoss H B) v`. -/
theorem d1ge_deepestPoint_via_explicit_core_genL_wired
    (H : Fin (L + 1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ)
    (hB : B.rank = r) (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (v : Params H) (m : ℕ)
    (hDeepest : rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
        = (m : ℝ≥0∞) / 2
          + rlctAtOn (fun A : Params (fun s => H s - r) =>
              dlnLoss (fun s => H s - r)
                (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
              (fun _ => 0 : Params (fun s => H s - r)))
    (hAtV : ∃ P : Params (fun s => H s - r),
        (m : ℝ≥0∞) / 2
          + rlctAtOn (fun A : Params (fun s => H s - r) =>
              dlnLoss (fun s => H s - r)
                (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
              P
        ≤ rlctAt H (dlnLoss H B) v) :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL) ≤ rlctAt H (dlnLoss H B) v := by
  obtain ⟨P, hAtV'⟩ := hAtV
  exact deepest_le_of_optimal_via_L2_ge (B := B) H r
    (rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL))
    (rlctAt H (dlnLoss H B) v) m
    (rlctAtOn (fun A : Params (fun s => H s - r) =>
      dlnLoss (fun s => H s - r)
        (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
      (fun _ => 0 : Params (fun s => H s - r)))
    (rlctAtOn (fun A : Params (fun s => H s - r) =>
      dlnLoss (fun s => H s - r)
        (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
      P)
    hDeepest hAtV' (core_zero_le_of_params (fun s => H s - r) P)

/-- **The full general-`L` drop-in from the explicit chart.** Composes the two bricks above: from the
general-`L` explicit-chart data (item `d1ge_hAtV_of_explicit_chart_genL`) plus the deepest-side value
`hDeepest`, concludes the D1 `≥`-leg per-point obligation. This is the single theorem the general-`L`
chart build (the WALL — the iterated corner-elimination chart `Φ` + block model + Schur residual +
slice value) plugs into to close `rlctAt_deepest_le_of_optimal` at general `L`. -/
theorem d1ge_deepestPoint_of_explicit_chart_genL
    {m specDim n : ℕ} {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasureSpace Y] [BorelSpace Y]
    [FiniteDimensional ℝ Y] [ProperSpace Y] [IsFiniteMeasureOnCompacts (volume : Measure Y)]
    (H : Fin (L + 1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ)
    (hB : B.rank = r) (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (v : Params H)
    (hDeepest : rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
        = (m : ℝ≥0∞) / 2
          + rlctAtOn (fun A : Params (fun s => H s - r) =>
              dlnLoss (fun s => H s - r)
                (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
              (fun _ => 0 : Params (fun s => H s - r)))
    (qₑ : (Fin m → ℝ) × Y → EuclideanSpace ℝ (Fin n)) (hq : ContDiff ℝ 1 qₑ) (t0 : Y)
    (hchart : rlctAt H (dlnLoss H B) v
        = rlctAtOn (fun p : (Fin m → ℝ) × Y =>
            (∑ i, p.1 i ^ 2) + (∑ i, qₑ p i ^ 2)) ((0 : Fin m → ℝ), t0))
    (hRne : ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U),
        (∑ i, qₑ ((0 : Fin m → ℝ), z) i ^ 2) ≠ 0)
    (e : Y ≃ₜ ((Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin specDim → ℝ)))
    (he_mp : MeasurePreserving e (volume : Measure Y) volume)
    (he_emb : MeasurableEmbedding e)
    (u : Y → ℝ) (hu_meas : Measurable u) (ua ub : ℝ) (hua : 0 < ua)
    (hu_bnd : ∃ U ∈ 𝓝 t0, ∀ w ∈ U, ua ≤ |u w| ∧ |u w| ≤ ub)
    (hfact : ∀ t : Y, (∑ i, qₑ ((0 : Fin m → ℝ), t) i ^ 2)
        = u t * dlnLoss (fun s => H s - r)
            (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
            ((paramsEquivFlat (fun s => H s - r)).symm (e t).1)) :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL) ≤ rlctAt H (dlnLoss H B) v :=
  d1ge_deepestPoint_via_explicit_core_genL_wired H r B hB hr hL v m hDeepest
    (d1ge_hAtV_of_explicit_chart_genL H r B v qₑ hq t0 hchart hRne e he_mp he_emb u hu_meas ua ub hua
      hu_bnd hfact)

end DLNFibre.DLN.RLCT
