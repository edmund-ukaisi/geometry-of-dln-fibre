import DLNFibre.DLN.RLCT.Validate.D1ChartProducer

/-!
# `DLNFibre.DLN.RLCT.Validate.D1ChartProducerL2` — D1 IFT-chart producer at general optimal `v` (L = 2)

The D1 `≥`-leg per-point obligation `rlctAt_deepest_le_of_optimal` (Skeleton:1172) at L = 2 reduces,
via the banked `deepest_le_of_optimal_chart` (`D1ChartProducer`), to producing — at a GENERAL optimal
`v ∈ optimalSet H B` (rank pattern possibly OFF the rank-exact deepest point) — the engine inputs:
quasi-split engine: an IFT chart at `v` with the post-chart sum-of-squares form `F = ∑ s² + Q`, the
slice residual `R = Q(0,·)`, the comparison `hcmp`, and the residual-core diffeo data feeding
`hCore_slice_residual_eq`.

## What this module is (the honest scope, verify-first 2026-06-29 + Codex xhigh)

The analytic heart of the producer is the **constant-rank quadratic split** (the splitting /
Morse–Bott / Gromoll–Meyer normal form): a local diffeo `φ` at `v` with
`loss ∘ φ⁻¹(u) = u₁² + … + u_m² + R(rest)`, the residual `R` genuinely independent of the `m = nReg`
split coordinates. **Mathlib v4.29 has NO such lemma** (no Morse / Morse-Bott / Gromoll-Meyer /
splitting / constant-rank quadratic decomposition — verified). The explicit deepest-point chart
(`DeepestGaugeConstruction`) does NOT transfer (it rides the rank-`r`-EXACT pivot structure, gone at a
general `v`) and is itself still open (`deepest_gauge_squeeze_exists` carries sorries). Constructing
the chart at a general `v` is "a major multi-tide build, rung-1-scale, WALL-FREE but substantial"
(expedition Item 81) — strictly harder than the still-open deepest analog. So building the full
sorry-free chart is out of scope for one bounded module.

**What this module delivers instead** (the bedrock the unbuilt chart will stand on): the producer as a
sorry-free **reduction theorem** `D1ChartProducerL2.deepest_le_of_optimal_of_chart_certificate`. It
bundles the genuinely-Mathlib-lacking analytic content into ONE named certificate
`GeneralVChartL2` (the IFT chart + the post-chart sum-of-squares form + the residual-core diffeo),
takes the existing `#44` deepest-side equality as the explicit hypothesis `hDeepest`, and proves
EVERYTHING ELSE is mechanical: it discharges `hCore` IN-MODULE from the certificate's diffeo data via
`hCore_slice_residual_eq` (it does NOT take `hCore` as a bare hypothesis — Codex soundness check), then
calls `deepest_le_of_optimal_chart` to conclude `rlctAt deepest ≤ rlctAt v`. The certificate's fields
are EXACTLY the obligations the IFT-split must satisfy; the theorem pins that interface and certifies
the reduction is wiring + the diffeo-transfer, NOT new analytic content masquerading as wiring.

`m` is tied to `nReg = r·(H⁰ + Hᴸ − r)` (the regular gauge-transversal count), so the certificate is
not semantically loose. Scope: L = 2 only (the `Fin.last 2` endpoints distinct); the general-L arm is
the named research wall #120 and is NOT touched. The deepest-side `#44`
(`deepest_regular_core_normal_form`) stays the existing tracked Skeleton sorry — consumed as a
hypothesis, never re-proved here.
-/

open MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

/-- The regular gauge-orbit-transversal dimension `nReg = r·(H⁰ + Hᴸ − r)` at L = 2 — the count of
nondegenerate-quadratic directions the IFT chart at `v` exposes (equal to the deepest-point `nReg`;
constant on `optimalSet` since the product rank is `r` everywhere on the fibre). -/
abbrev nRegL2 (H : Fin (2 + 1) → ℕ) (r : ℕ) : ℕ := r * (H 0 + H (Fin.last 2) - r)

/-- **The general-`v` IFT-chart certificate at L = 2** — the genuinely-Mathlib-lacking analytic
content of the D1 producer, bundled. At a general optimal `v ∈ optimalSet H B`, an IFT chart at `v`
brings the loss into the post-chart sum-of-squares form `F = ∑ s² + Q` over a flat product slice
`(Fin m → ℝ) × (Reduced × Gauge)` (`m = nReg`), with slice residual `R = Q(0,·)`, the quasi-split
comparison `hcmp`, and the residual-core local diffeo `Φ` realising `R = (core₀ ∘ fst) ∘ Φ`
(`core₀ = rlctAtOn`-equal to the deepest core, so `coreDeepest = rlctAtOn core₀ t0`).

The fields are the EXACT producer obligations consumed by `deepest_le_of_optimal_chart` +
`hCore_slice_residual_eq`. The diffeo data (`Φ … hRform … hG`) is the bounded-unit local-homeomorph
package the residual-core identification needs; the G1 verify-first found the explicit
`Φ : (T,g) ↦ ((T₁,(I+G(g))·T₂),g)`, `det DΦ(0) = 1`, but that construction is the unbuilt
analytic content — here it is a certificate hypothesis.

**Non-vacuity + scope caveat (Codex red-team, 2026-06-29).** The field set is jointly satisfiable in
principle (the G1 `Φ`/`R = ‖T₁(I+G)T₂‖²` form is a witness compatible with `hRform`); `hRne` is
a.e.-nonzero NEAR `(t0,g0)`, so `R (t0,g0) = 0` (the core vanishing at its deepest point) is NOT a
contradiction. The interface DOES exclude the terminal / direct-Morse case where the reduced core is
identically zero: then `hRform` forces `R ≡ 0`, contradicting `hRne` — such a `v` needs a separate
(coreless) route, not this certificate. `GeneralVChartL2.ofExactGerm` below builds the certificate from
a strictly-realizable weaker premise with the identity residual diffeo — the bedrock non-vacuity
witness (analogous to `DeepestGaugeChart.ofExactGerm`). -/
structure GeneralVChartL2 {m : ℕ}
    {Reduced Gauge : Type*}
    [NormedAddCommGroup Reduced] [NormedSpace ℝ Reduced] [MeasureSpace Reduced]
    [BorelSpace Reduced] [FiniteDimensional ℝ Reduced]
    [ProperSpace Reduced] [IsFiniteMeasureOnCompacts (volume : Measure Reduced)]
    [SFinite (volume : Measure Reduced)]
    [NormedAddCommGroup Gauge] [NormedSpace ℝ Gauge] [MeasureSpace Gauge]
    [BorelSpace Gauge] [FiniteDimensional ℝ Gauge]
    [ProperSpace Gauge] [IsFiniteMeasureOnCompacts (volume : Measure Gauge)]
    [SFinite (volume : Measure Gauge)]
    [(volume : Measure (Reduced × Gauge)).IsAddHaarMeasure]
    [Measure.IsOpenPosMeasure (volume : Measure Gauge)]
    (H : Fin (2 + 1) → ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (v : Params H)
    (coreDeepest : ℝ≥0∞) where
  /-- The post-chart loss on the flat product slice. -/
  F : (Fin m → ℝ) × (Reduced × Gauge) → ℝ
  /-- The non-square remainder of the post-chart loss. -/
  Q : (Fin m → ℝ) × (Reduced × Gauge) → ℝ
  /-- The slice residual `R = Q(0,·)`. -/
  R : Reduced × Gauge → ℝ
  /-- The chart basepoint on the slice. -/
  t0 : Reduced
  /-- The gauge basepoint. -/
  g0 : Gauge
  /-- The reduced-core function (a function of the `Reduced` factor alone). -/
  core₀ : Reduced → ℝ
  /-- The IFT chart transfer: `rlctAt (dlnLoss H B) v = rlctAtOn F (0, (t0,g0))`. -/
  hchart : rlctAt H (dlnLoss H B) v = rlctAtOn F ((0 : Fin m → ℝ), (t0, g0))
  /-- The post-chart sum-of-squares form `F = ∑ s² + Q`. -/
  hF : ∀ p, F p = (∑ i, p.1 i ^ 2) + Q p
  /-- `Q ≥ 0`. -/
  hQ0 : ∀ p, 0 ≤ Q p
  /-- `F` is measurable. -/
  hFmeas : Measurable F
  /-- `R = Q(0,·)`. -/
  hR : ∀ t, R t = Q ((0 : Fin m → ℝ), t)
  /-- `R` is measurable. -/
  hRmeas : Measurable R
  /-- `R` is a.e.-nonzero near `(t0,g0)`. -/
  hRne : ∃ U ∈ 𝓝 (t0, g0), ∀ᵐ z ∂(volume.restrict U), R z ≠ 0
  /-- The quasi-split comparison constant. -/
  C : ℝ
  /-- `0 < C`. -/
  hC : 0 < C
  /-- The quasi-split comparison `(∑ s²) + R ≤ C·F` near `(0,(t0,g0))`. -/
  hcmp : ∃ U ∈ 𝓝 ((0 : Fin m → ℝ), (t0, g0)), ∀ p ∈ U,
      (∑ i, p.1 i ^ 2) + R p.2 ≤ C * F p
  /-- `coreDeepest` is the reduced-core RLCT at the slice basepoint (the G1 tightness). -/
  hcoreDeepest : coreDeepest = rlctAtOn core₀ t0
  /-- The residual-core local diffeo. -/
  Φ : Reduced × Gauge → Reduced × Gauge
  /-- Its local inverse. -/
  Φsymm : Reduced × Gauge → Reduced × Gauge
  /-- The diffeo derivative. -/
  DΦ : Reduced × Gauge → ((Reduced × Gauge) →L[ℝ] (Reduced × Gauge))
  /-- The inverse derivative. -/
  DΦsymm : Reduced × Gauge → ((Reduced × Gauge) →L[ℝ] (Reduced × Gauge))
  /-- The diffeo domain. -/
  V : Set (Reduced × Gauge)
  /-- `V` is open. -/
  hVopen : IsOpen V
  /-- The basepoint is in `V`. -/
  hwV : (t0, g0) ∈ V
  /-- `Φ` fixes the basepoint. -/
  hfix : Φ (t0, g0) = (t0, g0)
  /-- Left inverse on `V`. -/
  hleft : ∀ w ∈ V, Φsymm (Φ w) = w
  /-- Right inverse on `V`. -/
  hright : ∀ w ∈ V, Φ (Φsymm w) = w
  /-- `Φ` continuous on `V`. -/
  hΦcont : ContinuousOn Φ V
  /-- `Φsymm` continuous on `V`. -/
  hsymmcont : ContinuousOn Φsymm V
  /-- `Φ` has derivative `DΦ` on `V`. -/
  hderiv : ∀ w ∈ V, HasFDerivAt Φ (DΦ w) w
  /-- `Φsymm` has derivative `DΦsymm` on `V`. -/
  hderivsymm : ∀ w ∈ V, HasFDerivAt Φsymm (DΦsymm w) w
  /-- `|det DΦ|` measurable. -/
  hdetmeas : Measurable fun w => |(DΦ w).det|
  /-- `|det DΦsymm|` measurable. -/
  hdetmeassymm : Measurable fun w => |(DΦsymm w).det|
  /-- `|det DΦ|` bounded-unit on `V`. -/
  hbdd : ∃ a b : ℝ, 0 < a ∧ ∀ w ∈ V, a ≤ |(DΦ w).det| ∧ |(DΦ w).det| ≤ b
  /-- `|det DΦsymm|` bounded-unit on `V`. -/
  hbddsymm : ∃ a b : ℝ, 0 < a ∧ ∀ w ∈ V, a ≤ |(DΦsymm w).det| ∧ |(DΦsymm w).det| ≤ b
  /-- The form identity `R = (core₀ ∘ fst) ∘ Φ`. -/
  hRform : ∀ w, R w = core₀ (Φ w).1
  /-- A positive-finite gauge nbhd (the spectator box). -/
  hG : ∃ W : Set Gauge, IsOpen W ∧ g0 ∈ W ∧ volume W < ⊤

/-- **Non-vacuity smart constructor (`GeneralVChartL2.ofExactGerm`).** Builds the certificate from a
strictly-realizable weaker premise: the chart/comparison data (`F`, `Q`, the chart transfer, the
sum-of-squares form, the slice residual `R`, the quasi-split comparison) PLUS the residual being the
reduced core ON THE NOSE — `R = core₀ ∘ fst` (`hRid`, the EXACT-germ special case, IDENTITY residual
diffeo). The 15 heavy diffeo facts (the bounded-unit local homeomorph) then discharge with `Φ = id`
(`det (id) = 1`, bounded by `1`), demonstrating the certificate's field set is JOINTLY SATISFIABLE
(not vacuously contradictory) and the residual-core-diffeo interface is reachable from a realizable
premise. (The actual G1 chart uses the nontrivial `Φ : (T,g) ↦ ((T₁,(I+G(g))·T₂),g)`; this `id`-diffeo
witness is the non-vacuity guard, exactly analogous to `DeepestGaugeChart.ofExactGerm`.) -/
noncomputable def GeneralVChartL2.ofExactGerm {m : ℕ}
    {Reduced Gauge : Type*}
    [NormedAddCommGroup Reduced] [NormedSpace ℝ Reduced] [MeasureSpace Reduced]
    [BorelSpace Reduced] [FiniteDimensional ℝ Reduced]
    [ProperSpace Reduced] [IsFiniteMeasureOnCompacts (volume : Measure Reduced)]
    [SFinite (volume : Measure Reduced)]
    [NormedAddCommGroup Gauge] [NormedSpace ℝ Gauge] [MeasureSpace Gauge]
    [BorelSpace Gauge] [FiniteDimensional ℝ Gauge]
    [ProperSpace Gauge] [IsFiniteMeasureOnCompacts (volume : Measure Gauge)]
    [SFinite (volume : Measure Gauge)]
    [(volume : Measure (Reduced × Gauge)).IsAddHaarMeasure]
    [Measure.IsOpenPosMeasure (volume : Measure Gauge)]
    (H : Fin (2 + 1) → ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (v : Params H)
    (coreDeepest : ℝ≥0∞)
    (F : (Fin m → ℝ) × (Reduced × Gauge) → ℝ) (Q : (Fin m → ℝ) × (Reduced × Gauge) → ℝ)
    (R : Reduced × Gauge → ℝ) (t0 : Reduced) (g0 : Gauge) (core₀ : Reduced → ℝ)
    (hchart : rlctAt H (dlnLoss H B) v = rlctAtOn F ((0 : Fin m → ℝ), (t0, g0)))
    (hF : ∀ p, F p = (∑ i, p.1 i ^ 2) + Q p) (hQ0 : ∀ p, 0 ≤ Q p) (hFmeas : Measurable F)
    (hR : ∀ t, R t = Q ((0 : Fin m → ℝ), t)) (hRmeas : Measurable R)
    (hRne : ∃ U ∈ 𝓝 (t0, g0), ∀ᵐ z ∂(volume.restrict U), R z ≠ 0)
    (C : ℝ) (hC : 0 < C)
    (hcmp : ∃ U ∈ 𝓝 ((0 : Fin m → ℝ), (t0, g0)), ∀ p ∈ U,
        (∑ i, p.1 i ^ 2) + R p.2 ≤ C * F p)
    (hcoreDeepest : coreDeepest = rlctAtOn core₀ t0)
    (hRid : ∀ w, R w = core₀ w.1)
    (hG : ∃ W : Set Gauge, IsOpen W ∧ g0 ∈ W ∧ volume W < ⊤) :
    GeneralVChartL2 (m := m) (Reduced := Reduced) (Gauge := Gauge) H B v coreDeepest where
  F := F; Q := Q; R := R; t0 := t0; g0 := g0; core₀ := core₀
  hchart := hchart; hF := hF; hQ0 := hQ0; hFmeas := hFmeas; hR := hR; hRmeas := hRmeas
  hRne := hRne; C := C; hC := hC; hcmp := hcmp; hcoreDeepest := hcoreDeepest
  -- the identity residual diffeo
  Φ := id; Φsymm := id
  DΦ := fun _ => ContinuousLinearMap.id ℝ (Reduced × Gauge)
  DΦsymm := fun _ => ContinuousLinearMap.id ℝ (Reduced × Gauge)
  V := Set.univ
  hVopen := isOpen_univ
  hwV := Set.mem_univ _
  hfix := rfl
  hleft := fun _ _ => rfl
  hright := fun _ _ => rfl
  hΦcont := continuousOn_id
  hsymmcont := continuousOn_id
  hderiv := fun w _ => hasFDerivAt_id w
  hderivsymm := fun w _ => hasFDerivAt_id w
  hdetmeas := by simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_id,
    LinearMap.det_id]; exact measurable_const
  hdetmeassymm := by simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_id,
    LinearMap.det_id]; exact measurable_const
  hbdd := ⟨1, 1, one_pos, fun w _ => by
    simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id, abs_one]
    exact ⟨le_refl _, le_refl _⟩⟩
  hbddsymm := ⟨1, 1, one_pos, fun w _ => by
    simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id, abs_one]
    exact ⟨le_refl _, le_refl _⟩⟩
  hRform := fun w => by rw [hRid]; rfl
  hG := hG

/-- **Concrete non-vacuity witness.** The `GeneralVChartL2` field set is inhabited from a SINGLE
genuinely-loss-tied input — the chart transfer `hchart` — with every other field discharged
concretely (`m = 0`: no regular block; `core₀ = R = Q ≡ 1`, so `hRne` is the trivial `1 ≠ 0`, `hF`/`hcmp`
hold with `C = 1` by `∑∅ s² = 0`, the identity residual diffeo). This certifies the interface is NOT
vacuously contradictory: it is reachable from the chart transfer alone, and `hchart` is exactly the
one obligation the unbuilt IFT supplies. (The `m = 0`, constant-core instance is degenerate — it does
not exercise the regular split or a vanishing core — but it `show`s the witness, per the bedrock
standard; the genuine instance is `ofExactGerm` at the G1 chart.) -/
example {Reduced Gauge : Type*}
    [NormedAddCommGroup Reduced] [NormedSpace ℝ Reduced] [MeasureSpace Reduced]
    [BorelSpace Reduced] [FiniteDimensional ℝ Reduced]
    [ProperSpace Reduced] [IsFiniteMeasureOnCompacts (volume : Measure Reduced)]
    [SFinite (volume : Measure Reduced)]
    [NormedAddCommGroup Gauge] [NormedSpace ℝ Gauge] [MeasureSpace Gauge]
    [BorelSpace Gauge] [FiniteDimensional ℝ Gauge]
    [ProperSpace Gauge] [IsFiniteMeasureOnCompacts (volume : Measure Gauge)]
    [SFinite (volume : Measure Gauge)]
    [(volume : Measure (Reduced × Gauge)).IsAddHaarMeasure]
    [Measure.IsOpenPosMeasure (volume : Measure Gauge)]
    (H : Fin (2 + 1) → ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (v : Params H)
    (t0 : Reduced) (g0 : Gauge)
    (hchart : rlctAt H (dlnLoss H B) v
      = rlctAtOn (fun p : (Fin 0 → ℝ) × (Reduced × Gauge) => (∑ i, p.1 i ^ 2) + 1)
          ((0 : Fin 0 → ℝ), (t0, g0)))
    (hG : ∃ W : Set Gauge, IsOpen W ∧ g0 ∈ W ∧ volume W < ⊤) :
    Nonempty (GeneralVChartL2 (m := 0) (Reduced := Reduced) (Gauge := Gauge) H B v
      (rlctAtOn (fun _ : Reduced => (1 : ℝ)) t0)) :=
  ⟨GeneralVChartL2.ofExactGerm H B v (rlctAtOn (fun _ : Reduced => (1 : ℝ)) t0)
    (F := fun p => (∑ i, p.1 i ^ 2) + 1) (Q := fun _ => 1) (R := fun _ => 1) t0 g0
    (core₀ := fun _ => 1) hchart (fun _ => rfl) (fun _ => zero_le_one)
    (by fun_prop) (fun _ => rfl) measurable_const
    ⟨Set.univ, Filter.univ_mem, by filter_upwards with z using one_ne_zero⟩
    1 one_pos ⟨Set.univ, Filter.univ_mem, fun p _ => by rw [one_mul]⟩
    rfl (fun _ => rfl) hG⟩

/-- **The D1 producer at a general optimal `v` (L = 2), as a reduction.** Given the general-`v` IFT
chart certificate `Γ` (the genuinely-unbuilt analytic content) with `m = nReg`, and the deepest-side
`#44` equality `hDeepest : rlctAt (dlnLoss H B) deepest = nReg/2 + coreDeepest`, the deepest point has
`≤` local RLCT than `v`. The proof is mechanical: discharge `hCore` from the certificate's
residual-core diffeo via `hCore_slice_residual_eq` (NOT a bare hypothesis), then call the banked
`deepest_le_of_optimal_chart`. -/
theorem deepest_le_of_optimal_of_chart_certificate
    {Reduced Gauge : Type*}
    [NormedAddCommGroup Reduced] [NormedSpace ℝ Reduced] [MeasureSpace Reduced]
    [BorelSpace Reduced] [FiniteDimensional ℝ Reduced]
    [ProperSpace Reduced] [IsFiniteMeasureOnCompacts (volume : Measure Reduced)]
    [SFinite (volume : Measure Reduced)]
    [NormedAddCommGroup Gauge] [NormedSpace ℝ Gauge] [MeasureSpace Gauge]
    [BorelSpace Gauge] [FiniteDimensional ℝ Gauge]
    [ProperSpace Gauge] [IsFiniteMeasureOnCompacts (volume : Measure Gauge)]
    [SFinite (volume : Measure Gauge)]
    [(volume : Measure (Reduced × Gauge)).IsAddHaarMeasure]
    [Measure.IsOpenPosMeasure (volume : Measure Gauge)]
    (H : Fin (2 + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (deepest v : Params H)
    (coreDeepest : ℝ≥0∞)
    (hDeepest : rlctAt H (dlnLoss H B) deepest = (nRegL2 H r : ℝ≥0∞) / 2 + coreDeepest)
    (Γ : GeneralVChartL2 (m := nRegL2 H r) (Reduced := Reduced) (Gauge := Gauge)
      H B v coreDeepest) :
    rlctAt H (dlnLoss H B) deepest ≤ rlctAt H (dlnLoss H B) v := by
  -- The product slice `Y := Reduced × Gauge` carries the five `deepest_le_of_optimal_chart`
  -- instances (search fails on `ProperSpace`/`IsFiniteMeasureOnCompacts` for `Prod` of these
  -- spaces; supply them explicitly — they are propositionally there, only the search is stuck).
  haveI hP : ProperSpace (Reduced × Gauge) := prod_properSpace
  haveI hF' : IsFiniteMeasureOnCompacts (volume : Measure (Reduced × Gauge)) :=
    isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  -- Step 1: the residual-core diffeo identification (`hCore_slice_residual_eq`) — `R` has the same
  -- RLCT at the basepoint as the reduced core `core₀` at `t0`.
  have hCoreEq : rlctAtOn Γ.R (Γ.t0, Γ.g0) = rlctAtOn Γ.core₀ Γ.t0 :=
    hCore_slice_residual_eq Γ.core₀ Γ.R Γ.t0 Γ.g0 Γ.Φ Γ.Φsymm Γ.DΦ Γ.DΦsymm Γ.V
      Γ.hVopen Γ.hwV Γ.hfix Γ.hleft Γ.hright Γ.hΦcont Γ.hsymmcont Γ.hderiv Γ.hderivsymm
      Γ.hdetmeas Γ.hdetmeassymm Γ.hbdd Γ.hbddsymm Γ.hRform Γ.hG
  -- Step 2: `hCore : coreDeepest ≤ rlctAtOn R (t0,g0)` — equality from `hcoreDeepest` + `hCoreEq`.
  have hCore : coreDeepest ≤ rlctAtOn Γ.R (Γ.t0, Γ.g0) :=
    le_of_eq (Γ.hcoreDeepest.trans hCoreEq.symm)
  -- Step 3: the banked per-point chart producer wiring.
  exact deepest_le_of_optimal_chart H r B deepest v Γ.F Γ.Q Γ.R (Γ.t0, Γ.g0) coreDeepest
    hDeepest Γ.hchart Γ.hF Γ.hQ0 Γ.hFmeas Γ.hR Γ.hRmeas Γ.hRne Γ.C Γ.hC Γ.hcmp hCore

end DLNFibre.DLN.RLCT
