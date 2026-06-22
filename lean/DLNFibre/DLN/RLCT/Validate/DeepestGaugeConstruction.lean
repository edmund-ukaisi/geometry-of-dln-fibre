import DLNFibre.DLN.RLCT.Validate.DeepestGaugeChart
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeBlocks
import DLNFibre.DLN.RLCT.Validate.DeepestSplitReindex
import DLNFibre.DLN.RLCT.Validate.DeepestFrame

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestGaugeConstruction` — the `DeepestGaugeChart` instance (#44c)

The producer for `deepest_gauge_squeeze_exists` (sub-3, the single piece gating #44): construct a
`DeepestGaugeChart H r B` instance at the deepest point. crux2's `DeepestGaugeChart.lean`
(single-writer) carries the `sorry`; this module builds the instance and crux2 wires
`exact deepest_gauge_chart_construct …`.

## The decomposition (design D structure; #155 Part-2 cert; sub-34 g152/g153/g154)

Producing the instance splits into four named obligations (skeleton-first, `sorry` each, then fill):
- **(i) gauge-slice MP reindex** (`deepestSplit_exists`): `nGauge` + `split : flat ≃ₜ DeepestSplit`
  measure-preserving + `split_basepoint`. The per-layer `block_elimination` units `P_s,Q_s` reindex
  the flat params into `(regular residuals) × (raw reduced blocks T_s) × (gauge spectators)`. Pure
  coordinate/measure infra (the `paramsEquivFlat` / S1 idiom).
- **(ii) gauge-absorption homeomorphism** (`coreAbsorb_exists`): `coreAbsorb` turning raw `T_s` into
  the per-layer **Schur complement** `S_s = T_s − Z_s(I+X_s)⁻¹Y_s` (g156/#61: the honest core,
  NOT the unit `T_s·(I−V_sY_s)⁻¹` which is `0` at `T_s=0`); `∏S_s = R|{E=0}` (`schur_P11_decomp`'s
  full-product Schur `R`), fixing reg+spec + origin.
- **(iii) g-unit RLCT peel** (`coreAbsorb_rlct_holds`): absorbed and raw cores have the same RLCT at
  the origin, via `weightedThreshold_weight_unit_invariant` (the det-unit `det(I−VY)⁻ᴹ⁰ ≈ 1`).
- **(iv) loss-squeeze** (`deepest_loss_squeeze_holds`): the two-sided bound, via the banked
  `core_comparability_squeeze` + `frobenius_fromBlocks` (g153: leak ∈ ideal(reg) charged to `∑E²`).

## Status

ROUTE-FIRST skeleton: the four sub-lemma signatures + the assembly, all `sorry`. The matrix bedrock
(`DeepestGaugeBlocks`: `twofactor_block_product`, `schur_P11_decomp`, `frobenius_fromBlocks`,
`core_comparability_squeeze`) is GREEN and feeds (iii)+(iv). (i)+(ii) are the heavy geometric part.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The slot-grouping contract (controller precision pin, option (e))

The #64 confound (and its subtler "wrong grouping" form) recurs unless the `split` slot-semantics
are a STATED, durable contract — not a verbal agreement. The honest contract (controller): `split`
delivers semantically **role-grouped RAW slots** (a measure-preserving `det = ±1` reindex), and the
nonlinear gauge work lives in the absorptions (`regAbsorb` → `E`, `coreAbsorb` → the Schur `S_s`),
each a clean unit-Jacobian self-map of `DeepestSplit`. So the contract `split` must satisfy is: its
slots **decode** to the per-layer gauge blocks `(X_s, Y_s, Z_s, T_s)` — pinned here as the consuming
interface `PerLayerGaugeBlocks` + the `gaugeDecode` map, so the grouping survives as bedrock.
-/

/-- The per-layer gauge blocks of a rank-`r`-sliced point: for each layer `s : Fin L`, the
`(X_s, Y_s, Z_s, T_s)` decomposition of `C_s = [[I_r+X_s, Y_s],[Z_s, T_s]]` (`X_s : r×r`,
`Y_s : r×(H_{s+1}−r)`, `Z_s : (H_s−r)×r`, `T_s : (H_s−r)×(H_{s+1}−r)`). The decode target of the
split slots — `regAbsorb` reads `(X,Y,Z)` for `E`, `coreAbsorb` reads all four for `S_s`. -/
abbrev PerLayerGaugeBlocks (H : Fin (L + 1) → ℕ) (r : ℕ) : Type :=
  ∀ s : Fin L,
    (Matrix (Fin r) (Fin r) ℝ) × (Matrix (Fin r) (Fin (H s.succ - r)) ℝ)
      × (Matrix (Fin (H s.castSucc - r)) (Fin r) ℝ)
      × (Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ)

/-- **The slot-grouping contract** (controller precision pin). A `split`'s `DeepestSplit` slots
decode — via a continuous, basepoint-preserving map — to the per-layer gauge blocks. The durable
the absorptions consume: it pins WHICH slot-entry is which `(X_s,Y_s,Z_s,T_s)` block, so the #64
"wrong grouping" confound cannot recur. `split` must provide a `gaugeDecode` satisfying this;
`regAbsorb`/`coreAbsorb` read it. (Reg slot = the `X/Y/Z` gauge entries `E` reads; core = `T_s`;
split is `det = ±1`, the absorptions carry the gauge nonlinearity.) -/
structure IsGaugeSliceDecode (H : Fin (L + 1) → ℕ) (r : ℕ) (nGauge : ℕ)
    (gaugeDecode : DeepestSplit H r nGauge → PerLayerGaugeBlocks H r) : Prop where
  /-- The decode is continuous (the slots are a coordinate regrouping). -/
  continuous : Continuous gaugeDecode
  /-- At the split origin (the deepest basepoint), every gauge block is `0` (the deepest point is
  the block-normal rank-`r` chain: `X_s=Y_s=Z_s=T_s=0`, i.e. `C_s = blockdiag[I_r, 0]`). -/
  basepoint : gaugeDecode 0 = fun _ => (0, 0, 0, 0)

/-! ## The frame-free slot read (the inner half of `gaugeDecode`)

`gaugeDecode = gaugeSlotRead ∘ frame ∘ (split.symm − deepestFlat)` (g164: the constant gauge frame
composes on the inside; `split` stays MP). This section builds the FRAME-INDEPENDENT inner read
`gaugeSlotRead : DeepestSplit → PerLayerGaugeBlocks` — the X/Y/Z blocks off the reg+spectator slots
(via crux2's `regGaugeSlotEquiv`, the un-flattening of `Fintype.equivFin`), and the `T`-core block off
the core slot (`= FlatIdx (deepestM)`, type-forced). The frame (a fixed continuous linear iso, #77)
and `split.symm` compose before it; this read is independent of both. -/

/-- **The frame-free slot read.** Reads a `DeepestSplit` point into per-layer gauge blocks: the
`X_s, Y_s, Z_s` off the combined reg+spectator slot via `regGaugeSlotEquiv` (un-flattening the
opaque `Fintype.equivFin` into the legible `RegGaugeIdx` Σ-grouping), and the `T_s`-core off the core
slot via `paramsEquivFlat (deepestM)`. `gaugeDecode` is this composed AFTER the frame + `split.symm`. -/
noncomputable def gaugeSlotRead (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) : PerLayerGaugeBlocks H r :=
  fun s =>
    let g : RegGaugeIdx H r → ℝ := regGaugeSlotEquiv H r hr hL (q.1, q.2.2)
    let T : Params (deepestM H r) := (paramsEquivFlat (deepestM H r)).symm q.2.1
    ( Matrix.of (fun i j => g ⟨s, Sum.inl (Sum.inl (i, j))⟩)
    , Matrix.of (fun i j => g ⟨s, Sum.inl (Sum.inr (i, j))⟩)
    , Matrix.of (fun i j => g ⟨s, Sum.inr (i, j)⟩)
    , T s )

/-! ## The two PINNED hard sub-proofs (skeleton-first)

The bundle factors into determined wires + two SUBSTANTIAL sub-proofs, each stated as a named
obligation with its signature pinned (`sorry` body, validated by the assembly typechecking):

- `deepest_regAbsorb_exists` — the regular-slot absorption: a self-homeomorphism `regAbsorb` of
  `DeepestSplit` fixing core+spectator, with `regAbsorb 0 = 0`, whose regular slot through `regAbsorb`
  has the SAME local RLCT as the raw regular slot (`regAbsorb_rlct`, peeled by the refined `#72`
  local bounded-unit Jacobian peel). The map is `regSliceHomeo Ψ` for the IFT E-straightening `Ψ`
  (the analytic submersion `dE(w0)` rank `= nReg`); the IFT construction is the standalone
  parallelizable piece. PINNED here as the bundled existence the assembly consumes.
- `deepest_loss_squeeze` — the two-sided squeeze: near the deepest point, `dlnLoss H B` is bounded
  by `Φ = ∑ (regAbsorb (split w)).1² + deepestCoreF (coreAbsorb (split w)).2.1`. The matrix-block
  reduction (`∏C − blockNormal` → `P11 = leak + Rcore`) feeding the banked `core_comparability_squeeze`
  (#54) over the bounded boundary frame factors (g164). The geometric heart.

The `split` (`deepestSplit_exists`), `coreAbsorb` (`coreShearHomeo` + the Schur shift), and the
determined slot-fix / basepoint / `coreAbsorb_rlct` (#71, global shear det = 1) are wired directly. -/

/-- **PIN 1 — the regular absorption** (the IFT E-straightening, standalone-parallelizable). Bundles
the `regAbsorb` map + its core/spectator-fix + basepoint + the `regAbsorb_rlct` peel (against a fixed
`coreAbsorb`, sequenced reg-first per the structure). The map is `regSliceHomeo Ψ` for the IFT
straightening `Ψ` of the regular residual `E`; `regAbsorb_rlct` peels its bounded-unit Jacobian via
the refined `#72`. -/
theorem deepest_regAbsorb_exists (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (nGauge : ℕ)
    (coreAbsorb : DeepestSplit H r nGauge ≃ₜ DeepestSplit H r nGauge) :
    ∃ regAbsorb : DeepestSplit H r nGauge ≃ₜ DeepestSplit H r nGauge,
      regAbsorb 0 = 0 ∧
      (∀ q : DeepestSplit H r nGauge, (regAbsorb q).2.1 = q.2.1) ∧
      (∀ q : DeepestSplit H r nGauge, (regAbsorb q).2.2 = q.2.2) ∧
      rlctAtOn
          (fun q : DeepestSplit H r nGauge =>
            (∑ i, (regAbsorb q).1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
          (0 : DeepestSplit H r nGauge)
        = rlctAtOn
            (fun q : DeepestSplit H r nGauge =>
              (∑ i, q.1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
            (0 : DeepestSplit H r nGauge) := by
  sorry

/-- **PIN 2 — the loss squeeze** (the geometric heart). Near the deepest point (flat coords), the loss
is two-sidedly bounded by `Φ = ∑ (regAbsorb (split w)).1² + deepestCoreF (coreAbsorb (split w)).2.1`.
The matrix-block reduction `∏C − blockNormal → P11 = leak + Rcore` (g164 boundary frames) feeding the
banked `core_comparability_squeeze` (#54: leak ∈ ideal(reg), charged to `∑E²`). -/
theorem deepest_loss_squeeze (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (nGauge : ℕ)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r nGauge)
    (coreAbsorb regAbsorb : DeepestSplit H r nGauge ≃ₜ DeepestSplit H r nGauge)
    (hsplit_base : split ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) = 0) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∃ U ∈ 𝓝 ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
        ∀ w ∈ U,
          0 ≤ ((∑ i, (regAbsorb (split w)).1 i ^ 2)
              + deepestCoreF H r (coreAbsorb (split w)).2.1) ∧
          c₁ * ((∑ i, (regAbsorb (split w)).1 i ^ 2)
              + deepestCoreF H r (coreAbsorb (split w)).2.1)
            ≤ dlnLoss H B ((paramsEquivFlat H).symm w) ∧
          dlnLoss H B ((paramsEquivFlat H).symm w)
            ≤ c₂ * ((∑ i, (regAbsorb (split w)).1 i ^ 2)
              + deepestCoreF H r (coreAbsorb (split w)).2.1) := by
  sorry

/-! ## The measure-preserving core-shear peel (Route A, Codex g165)

The core-shear `coreShearHomeo shift` is MEASURE-PRESERVING (det = 1, a fiber translation), so it
peels the RLCT via `rlctAtOn_comp_homeomorph` (NO derivative bookkeeping). The MP is
`MeasurePreserving.skew_product` (the fiber-shift `(a,c) ↦ (a, c + shift a)` with per-fiber
translation invariance `measurePreserving_add_right`) sandwiched by the
`reassoc : Reg × (Core × Spec) ≃ₜ (Reg × Spec) × Core` regrouping. Shift-agnostic — holds for any
continuous `shift`; the concrete Schur shift is plugged in by `deepest_coreAbsorb_exists`. -/

/-- The product-volume reassociation `(Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ)) ≃ₜ
((Fin a → ℝ) × (Fin c → ℝ)) × (Fin b → ℝ)` is measure-preserving (product-`volume`, det `= ±1`
reindex). The carrier for the core-shear MP. -/
private theorem measurePreserving_coreReassoc (a b c : ℕ) :
    MeasurePreserving
      (fun q : (Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ)) => ((q.1, q.2.2), q.2.1))
      volume volume := by
  -- `(reg,(core,spec)) ↦ ((reg,spec),core)` = swap-inner (`core×spec → spec×core`), then
  -- `prodAssoc.symm` (`reg×(spec×core) → (reg×spec)×core`). Each MP via the product-`volume` form.
  set A := Fin a → ℝ; set Bb := Fin b → ℝ; set C := Fin c → ℝ
  -- Step 1: swap the inner `(core, spec) ↦ (spec, core)`.
  have hswap : MeasurePreserving (Prod.swap : Bb × C → C × Bb) volume volume := by
    rw [show (volume : Measure (Bb × C)) = (volume : Measure Bb).prod (volume) from
          Measure.volume_eq_prod _ _,
      show (volume : Measure (C × Bb)) = (volume : Measure C).prod (volume) from
          Measure.volume_eq_prod _ _]
    exact measurePreserving_swap
  have h1 : MeasurePreserving
      (Prod.map (id : A → A) (Prod.swap : Bb × C → C × Bb)) volume volume := by
    rw [show (volume : Measure (A × (Bb × C))) = (volume : Measure A).prod (volume) from
          Measure.volume_eq_prod _ _,
      show (volume : Measure (A × (C × Bb))) = (volume : Measure A).prod (volume) from
          Measure.volume_eq_prod _ _]
    exact (MeasurePreserving.id (volume : Measure A)).prod hswap
  -- Step 2: `prodAssoc.symm`: `reg × (spec × core) ↦ (reg × spec) × core`.
  have h2 : MeasurePreserving
      (fun q : A × (C × Bb) => ((q.1, q.2.1), q.2.2)) volume volume := by
    rw [show (volume : Measure (A × (C × Bb)))
          = (volume : Measure A).prod ((volume : Measure C).prod volume) from by
          rw [Measure.volume_eq_prod _ _, Measure.volume_eq_prod _ _],
      show (volume : Measure ((A × C) × Bb))
          = ((volume : Measure A).prod volume).prod volume from by
          rw [Measure.volume_eq_prod _ _, Measure.volume_eq_prod _ _]]
    exact MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc (volume : Measure A) volume volume)
  exact h2.comp h1

/-- **The core-shear is measure-preserving** (Route A core, Codex g165). For any continuous
`shift : (Fin a → ℝ) × (Fin c → ℝ) → (Fin b → ℝ)`, the fiber-shear
`(reg, core, spec) ↦ (reg, core + shift (reg, spec), spec)` preserves the product `volume`
(`skew_product` on the `(reg×spec) × core` regrouping, per-fiber `measurePreserving_add_right`). -/
private theorem measurePreserving_coreShear (a b c : ℕ)
    (shift : (Fin a → ℝ) × (Fin c → ℝ) → (Fin b → ℝ)) (hshift : Continuous shift) :
    MeasurePreserving
      (fun q : (Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ)) =>
        (q.1, (q.2.1 + shift (q.1, q.2.2), q.2.2)))
      volume volume := by
  set A := Fin a → ℝ; set Bb := Fin b → ℝ; set C := Fin c → ℝ
  -- On the regrouped space `(A × C) × Bb`, the skew `((reg,spec), core) ↦ ((reg,spec), core + shift)`
  -- is MP: `f = id` on the base `A × C`, per-fiber `core ↦ core + shift (reg,spec)` a translation.
  have hskew : MeasurePreserving
      (fun p : (A × C) × Bb => (p.1, p.2 + shift p.1)) volume volume := by
    rw [show (volume : Measure ((A × C) × Bb)) = (volume : Measure (A × C)).prod volume from
          Measure.volume_eq_prod _ _]
    refine MeasurePreserving.skew_product (MeasurePreserving.id (volume : Measure (A × C)))
      ?_
      (ae_of_all _ fun p => (measurePreserving_add_right (volume : Measure Bb) (shift p)).map_eq)
    -- `uncurry g (p, core) = core + shift p` is measurable (snd + shift ∘ fst, no `fun_prop`).
    have hsf : Measurable (fun x : (A × C) × Bb => shift x.1) :=
      hshift.measurable.comp measurable_fst
    have hm : Measurable (fun x : (A × C) × Bb => x.2 + shift x.1) :=
      measurable_snd.add hsf
    exact hm
  -- forward reassoc `A × (Bb × C) → (A × C) × Bb`, `(reg,(core,spec)) ↦ ((reg,spec),core)`.
  have hfwd : MeasurePreserving
      (fun q : A × (Bb × C) => ((q.1, q.2.2), q.2.1)) volume volume :=
    measurePreserving_coreReassoc a b c
  -- reverse reassoc `(A × C) × Bb → A × (Bb × C)`, `((reg,spec),core) ↦ (reg,(core,spec))`.
  have hrev : MeasurePreserving
      (fun p : (A × C) × Bb => (p.1.1, (p.2, p.1.2))) volume volume := by
    have h2 : MeasurePreserving
        (fun p : (A × C) × Bb => (p.1.1, (p.1.2, p.2))) volume volume := by
      rw [show (volume : Measure ((A × C) × Bb))
            = ((volume : Measure A).prod volume).prod volume from by
            rw [Measure.volume_eq_prod _ _, Measure.volume_eq_prod _ _],
        show (volume : Measure (A × (C × Bb)))
            = (volume : Measure A).prod ((volume : Measure C).prod volume) from by
            rw [Measure.volume_eq_prod _ _, Measure.volume_eq_prod _ _]]
      exact measurePreserving_prodAssoc (volume : Measure A) volume volume
    have hswap : MeasurePreserving
        (fun q : A × (C × Bb) => (q.1, (q.2.2, q.2.1))) volume volume := by
      have hsw : MeasurePreserving (Prod.swap : C × Bb → Bb × C) volume volume := by
        rw [show (volume : Measure (C × Bb)) = (volume : Measure C).prod volume from
              Measure.volume_eq_prod _ _,
          show (volume : Measure (Bb × C)) = (volume : Measure Bb).prod volume from
              Measure.volume_eq_prod _ _]
        exact measurePreserving_swap
      have : MeasurePreserving
          (Prod.map (id : A → A) (Prod.swap : C × Bb → Bb × C)) volume volume := by
        rw [show (volume : Measure (A × (C × Bb))) = (volume : Measure A).prod volume from
              Measure.volume_eq_prod _ _,
          show (volume : Measure (A × (Bb × C))) = (volume : Measure A).prod volume from
              Measure.volume_eq_prod _ _]
        exact (MeasurePreserving.id (volume : Measure A)).prod hsw
      exact this
    exact hswap.comp h2
  -- `coreShear = hrev ∘ hskew ∘ hfwd` (the composite reduces to the target lambda by `rfl`).
  have hcomp := hrev.comp (hskew.comp hfwd)
  have hfun : (fun q : A × (Bb × C) => (q.1, (q.2.1 + shift (q.1, q.2.2), q.2.2)))
      = (fun p : (A × C) × Bb => (p.1.1, (p.2, p.1.2)))
        ∘ ((fun p : (A × C) × Bb => (p.1, p.2 + shift p.1))
          ∘ (fun q : A × (Bb × C) => ((q.1, q.2.2), q.2.1))) := rfl
  rw [hfun]; exact hcomp

/-- **PIN 0 — the core absorption** (the Schur shear, Route A peel). `coreAbsorb` turns the raw core
slot `T_s` into the Schur complement `S_s = T_s − Z_s(I+X_s)⁻¹Y_s` via `coreShearHomeo` with the
gauge-dependent shift; fixes reg+spec+origin; `coreAbsorb_rlct` peels its unit Jacobian via the
MEASURE-PRESERVING `rlctAtOn_comp_homeomorph` (the shear is MP, `measurePreserving_coreShear`). The
shift is read off the gauge blocks (`gaugeSlotRead ∘ frame`); its exact continuous form is part of
this obligation. -/
theorem deepest_coreAbsorb_exists (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (nGauge : ℕ) :
    ∃ coreAbsorb : DeepestSplit H r nGauge ≃ₜ DeepestSplit H r nGauge,
      coreAbsorb 0 = 0 ∧
      (∀ q : DeepestSplit H r nGauge, (coreAbsorb q).1 = q.1) ∧
      (∀ q : DeepestSplit H r nGauge, (coreAbsorb q).2.2 = q.2.2) ∧
      rlctAtOn
          (fun q : DeepestSplit H r nGauge => (∑ i, q.1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
          (0 : DeepestSplit H r nGauge)
        = rlctAtOn
            (fun q : DeepestSplit H r nGauge => (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
            (0 : DeepestSplit H r nGauge) := by
  sorry

/-- **The bundled gauge-slice construction** (#44c sub-3, the COUPLED obligation). Assembles the
`split` (`deepestSplit_exists`, MP reindex), `coreAbsorb` (`deepest_coreAbsorb_exists`, PIN 0),
`regAbsorb` (`deepest_regAbsorb_exists`, PIN 1), and the `loss_squeeze` (`deepest_loss_squeeze`,
PIN 2) into the bundled existence the structure consumes. -/
theorem deepest_gauge_construction (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ∃ (nGauge : ℕ) (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r nGauge)
      (coreAbsorb regAbsorb : DeepestSplit H r nGauge ≃ₜ DeepestSplit H r nGauge),
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
      regAbsorb 0 = 0 ∧
      (∀ q : DeepestSplit H r nGauge, (regAbsorb q).2.1 = q.2.1) ∧
      (∀ q : DeepestSplit H r nGauge, (regAbsorb q).2.2 = q.2.2) ∧
      rlctAtOn
          (fun q : DeepestSplit H r nGauge =>
            (∑ i, (regAbsorb q).1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
          (0 : DeepestSplit H r nGauge)
        = rlctAtOn
            (fun q : DeepestSplit H r nGauge =>
              (∑ i, q.1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
            (0 : DeepestSplit H r nGauge) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        ∃ U ∈ 𝓝 ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
          ∀ w ∈ U,
            0 ≤ ((∑ i, (regAbsorb (split w)).1 i ^ 2)
                + deepestCoreF H r (coreAbsorb (split w)).2.1) ∧
            c₁ * ((∑ i, (regAbsorb (split w)).1 i ^ 2)
                + deepestCoreF H r (coreAbsorb (split w)).2.1)
              ≤ dlnLoss H B ((paramsEquivFlat H).symm w) ∧
            dlnLoss H B ((paramsEquivFlat H).symm w)
              ≤ c₂ * ((∑ i, (regAbsorb (split w)).1 i ^ 2)
                + deepestCoreF H r (coreAbsorb (split w)).2.1) := by
  -- `split` (obligation (i), MP reindex carrying the deepest point to `0`).
  obtain ⟨split, hsplit_mp, hsplit_base⟩ :=
    deepestSplit_exists H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL))
  -- PIN 0: `coreAbsorb` (the Schur shear) + its slot-fix/basepoint/rlct.
  obtain ⟨coreAbsorb, hca_base, hca_reg, hca_spec, hca_rlct⟩ :=
    deepest_coreAbsorb_exists H r B hB hr hL (deepestNGauge H r)
  -- PIN 1: `regAbsorb` (the IFT E-straightening) + its slot-fix/basepoint/rlct (against `coreAbsorb`).
  obtain ⟨regAbsorb, hra_base, hra_core, hra_spec, hra_rlct⟩ :=
    deepest_regAbsorb_exists H r B hB hr hL (deepestNGauge H r) coreAbsorb
  -- PIN 2: the loss squeeze.
  obtain ⟨c₁, c₂, hc₁, hc₂, U, hU, hsq⟩ :=
    deepest_loss_squeeze H r B hB hr hL (deepestNGauge H r) split coreAbsorb regAbsorb hsplit_base
  exact ⟨deepestNGauge H r, split, coreAbsorb, regAbsorb, hsplit_mp, hsplit_base,
    hca_base, hca_reg, hca_spec, hca_rlct, hra_base, hra_core, hra_spec, hra_rlct,
    c₁, c₂, hc₁, hc₂, U, hU, hsq⟩

/-- **The `DeepestGaugeChart` instance** (#44c sub-3, `deepest_gauge_squeeze_exists`). Destructures
the bundled construction into the structure. crux2 wires `deepest_gauge_squeeze_exists := this`. -/
theorem deepest_gauge_chart_construct (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Nonempty (DeepestGaugeChart H r B hB hr hL) := by
  obtain ⟨nGauge, split, coreAbsorb, regAbsorb, hsplit_mp, hsplit_base, hca_base, hca_reg, hca_spec,
    hca_rlct, hra_base, hra_core, hra_spec, hra_rlct, hsq⟩ :=
    deepest_gauge_construction H r B hB hr hL
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
    regAbsorb := regAbsorb
    regAbsorb_basepoint := hra_base
    regAbsorb_core := hra_core
    regAbsorb_spectator := hra_spec
    regAbsorb_rlct := hra_rlct
    loss_squeeze := hsq }⟩

end DLNFibre.DLN.RLCT
