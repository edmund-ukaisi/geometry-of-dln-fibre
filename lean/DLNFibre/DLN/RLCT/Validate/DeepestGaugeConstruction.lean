import DLNFibre.DLN.RLCT.Validate.DeepestGaugeChart
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeBlocks
import DLNFibre.DLN.RLCT.Validate.DeepestSplitReindex
import DLNFibre.DLN.RLCT.Validate.DeepestFrame
import DLNFibre.DLN.RLCT.Validate.DeepestSchurShift
import DLNFibre.DLN.RLCT.Foundations.CoreShearMP

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
  the origin, via the MEASURE-PRESERVING route — `measurePreserving_coreShear` (the additive Schur
  shear is `det = 1`) ⟹ `rlctAtOn_comp_homeomorph` (NO Jacobian/weight bookkeeping; #61/g156 corrected
  the refuted non-MP `det(I−VY)⁻ᴹ⁰` weight-unit route of the multiplicative form).
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

/-- **PIN 1 — the regular straightening** (the (C) wall-fallback shape, #90). The honest E-straightening
is a LOCAL diffeo on `𝓝 0` that does NOT extend to a global spectator-fixing homeomorph in Mathlib
v4.29 (the piecewise cutoff is discontinuous at `∂V`). The (C) fallback (controller-blessed): a bare
TOTAL CONTINUOUS function `regStraighten` (a cutoff-interpolation between the honest `E` near `0` and
the identity outside — globally continuous, so `Φ` stays globally measurable for `rlctAtOn_squeeze`),
core/spectator/origin-fixing, with `regAbsorb_rlct` peeled via `#72`'s LOCAL bounded-unit Jacobian (the
`(πsymm, Dπ, V)` data lives inside this proof, not as a field). -/
theorem deepest_regAbsorb_exists (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (nGauge : ℕ)
    (coreAbsorb : DeepestSplit H r nGauge ≃ₜ DeepestSplit H r nGauge) :
    ∃ regStraighten : DeepestSplit H r nGauge → DeepestSplit H r nGauge,
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
            (0 : DeepestSplit H r nGauge) := by
  sorry

/-- **PIN 2 — the loss squeeze** (the geometric heart). Near the deepest point (flat coords), the loss
is two-sidedly bounded by `Φ = ∑ (regStraighten (split w)).1² + deepestCoreF (coreAbsorb (split w)).2.1`.
The matrix-block reduction `∏C − blockNormal → P11 = leak + Rcore` (g164 boundary frames) feeding the
banked `core_comparability_squeeze` (#54: leak ∈ ideal(reg), charged to `∑E²`). `regStraighten` is the
(C)-fallback total continuous fn; the squeeze is the local `∃ U` germ where `(regStraighten w).1 = E`. -/
theorem deepest_loss_squeeze (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (nGauge : ℕ)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r nGauge)
    (coreAbsorb : DeepestSplit H r nGauge ≃ₜ DeepestSplit H r nGauge)
    (regStraighten : DeepestSplit H r nGauge → DeepestSplit H r nGauge)
    (hsplit_base : split ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) = 0) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∃ U ∈ 𝓝 ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
        ∀ w ∈ U,
          0 ≤ ((∑ i, (regStraighten (split w)).1 i ^ 2)
              + deepestCoreF H r (coreAbsorb (split w)).2.1) ∧
          c₁ * ((∑ i, (regStraighten (split w)).1 i ^ 2)
              + deepestCoreF H r (coreAbsorb (split w)).2.1)
            ≤ dlnLoss H B ((paramsEquivFlat H).symm w) ∧
          dlnLoss H B ((paramsEquivFlat H).symm w)
            ≤ c₂ * ((∑ i, (regStraighten (split w)).1 i ^ 2)
              + deepestCoreF H r (coreAbsorb (split w)).2.1) := by
  sorry

/-! ## The measure-preserving core-shear peel (Route A, Codex g165)

The core-shear `coreShearHomeo shift` is MEASURE-PRESERVING (det = 1, a fiber translation), so it
peels the RLCT via `rlctAtOn_comp_homeomorph` (NO derivative bookkeeping). The two MP helpers
`measurePreserving_coreReassoc` + `measurePreserving_coreShear` live in `Foundations.CoreShearMP`
(crux2, #83) — the `MeasurePreserving.skew_product` (fiber-shift `(a,c) ↦ (a, c + shift a)`, per-fiber
`measurePreserving_add_right`) sandwiched by the `(Reg × Spec) × Core` regrouping. -/

/-- **The shift-agnostic core-shear peel** (PIN 0's mechanism). For ANY continuous shift on the gauge
slots vanishing at the origin, `coreShearHomeo shift` satisfies all four `coreAbsorb` obligations: it
fixes reg+spec (`coreShearHomeo_regular`/`_spectator`), fixes the origin (`coreShearHomeo_basepoint`),
and its RLCT peel `coreAbsorb_rlct` holds because the shear is MEASURE-PRESERVING
(`measurePreserving_coreShear`) ⟹ `rlctAtOn_comp_homeomorph`. The concrete Schur shift is plugged in
by `deepest_coreAbsorb_exists`; this isolates the (shift-agnostic) peel mechanism. -/
private theorem coreShear_satisfies_coreAbsorb (H : Fin (L + 1) → ℕ) (r : ℕ) (nGauge : ℕ)
    (shift : (Fin (deepestNReg H r) → ℝ) × (Fin nGauge → ℝ) → (Fin (flatDim (deepestM H r)) → ℝ))
    (hshift : Continuous shift) (h0 : shift (0, 0) = 0) :
    (coreShearHomeo shift hshift) 0 = 0 ∧
    (∀ q : DeepestSplit H r nGauge, ((coreShearHomeo shift hshift) q).1 = q.1) ∧
    (∀ q : DeepestSplit H r nGauge, ((coreShearHomeo shift hshift) q).2.2 = q.2.2) ∧
    rlctAtOn
        (fun q : DeepestSplit H r nGauge =>
          (∑ i, q.1 i ^ 2) + deepestCoreF H r ((coreShearHomeo shift hshift) q).2.1)
        (0 : DeepestSplit H r nGauge)
      = rlctAtOn
          (fun q : DeepestSplit H r nGauge => (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
          (0 : DeepestSplit H r nGauge) := by
  refine ⟨coreShearHomeo_basepoint shift hshift h0, coreShearHomeo_regular shift hshift,
    coreShearHomeo_spectator shift hshift, ?_⟩
  -- `coreAbsorb_rlct`: the shear is MP ⟹ `rlctAtOn_comp_homeomorph`, then `coreAbsorb 0 = 0`.
  set G : DeepestSplit H r nGauge → ℝ :=
    fun q => (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1 with hG
  have hmp : MeasurePreserving (coreShearHomeo shift hshift) volume volume :=
    measurePreserving_coreShear (deepestNReg H r) (flatDim (deepestM H r)) nGauge shift hshift
  have hkey := rlctAtOn_comp_homeomorph (coreShearHomeo shift hshift) hmp
    (coreShearHomeo shift hshift).measurableEmbedding G 0
  have hbase : (coreShearHomeo shift hshift) 0 = 0 := coreShearHomeo_basepoint shift hshift h0
  rw [hbase] at hkey
  -- `G ∘ coreShearHomeo` has reg fixed, so it equals the LHS integrand.
  have hLHS : (fun q : DeepestSplit H r nGauge => G ((coreShearHomeo shift hshift) q))
      = fun q => (∑ i, q.1 i ^ 2) + deepestCoreF H r ((coreShearHomeo shift hshift) q).2.1 := by
    funext q; rw [hG]; simp only [coreShearHomeo_regular shift hshift q]
  rw [hLHS] at hkey
  exact hkey

/-- **The concrete core absorption** (PIN 0, Route A peel). `coreAbsorb = coreShearHomeo` with the
globally-continuous **cutoff Schur shift** `schurCutoffShift` (`= χ·(−Z_s(I+X_s)⁻¹Y_s)`, the honest
Schur correction times the gauge-slot bump; globally continuous via `continuous_of_tsupport`, equal to
the honest correction on the inner ball). The shift slot type is fixed to `deepestNGauge H r` (the
spectator count the assembly uses). Concrete (not existential) so PIN 2's `loss_squeeze` sees the same
definitional map — Codex-confirmed Option A for the PIN0↔PIN2 coupling. -/
noncomputable def deepestCoreAbsorb (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    DeepestSplit H r (deepestNGauge H r) ≃ₜ DeepestSplit H r (deepestNGauge H r) :=
  coreShearHomeo (schurCutoffShift H r hr hL) (continuous_schurCutoffShift H r hr hL)

/-- **PIN 0 — the core absorption obligations**. `deepestCoreAbsorb` fixes reg+spec+origin and its
`coreAbsorb_rlct` peel holds — all four via the shift-agnostic, MEASURE-PRESERVING
`coreShear_satisfies_coreAbsorb` (`rlctAtOn_comp_homeomorph` on the det-1 shear). The concrete shift
is `schurCutoffShift`, continuous and vanishing at the origin. -/
theorem deepest_coreAbsorb_exists (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    (deepestCoreAbsorb H r hr hL) 0 = 0 ∧
      (∀ q : DeepestSplit H r (deepestNGauge H r), (deepestCoreAbsorb H r hr hL q).1 = q.1) ∧
      (∀ q : DeepestSplit H r (deepestNGauge H r), (deepestCoreAbsorb H r hr hL q).2.2 = q.2.2) ∧
      rlctAtOn
          (fun q : DeepestSplit H r (deepestNGauge H r) =>
            (∑ i, q.1 i ^ 2) + deepestCoreF H r (deepestCoreAbsorb H r hr hL q).2.1)
          (0 : DeepestSplit H r (deepestNGauge H r))
        = rlctAtOn
            (fun q : DeepestSplit H r (deepestNGauge H r) =>
              (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
            (0 : DeepestSplit H r (deepestNGauge H r)) :=
  coreShear_satisfies_coreAbsorb H r (deepestNGauge H r) (schurCutoffShift H r hr hL)
    (continuous_schurCutoffShift H r hr hL) (schurCutoffShift_zero H r hr hL)

/-- **The bundled gauge-slice construction** (#44c sub-3, the COUPLED obligation). Assembles the
`split` (`deepestSplit_exists`, MP reindex), `coreAbsorb` (`deepest_coreAbsorb_exists`, PIN 0),
`regAbsorb` (`deepest_regAbsorb_exists`, PIN 1), and the `loss_squeeze` (`deepest_loss_squeeze`,
PIN 2) into the bundled existence the structure consumes. -/
theorem deepest_gauge_construction (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
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
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        ∃ U ∈ 𝓝 ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
          ∀ w ∈ U,
            0 ≤ ((∑ i, (regStraighten (split w)).1 i ^ 2)
                + deepestCoreF H r (coreAbsorb (split w)).2.1) ∧
            c₁ * ((∑ i, (regStraighten (split w)).1 i ^ 2)
                + deepestCoreF H r (coreAbsorb (split w)).2.1)
              ≤ dlnLoss H B ((paramsEquivFlat H).symm w) ∧
            dlnLoss H B ((paramsEquivFlat H).symm w)
              ≤ c₂ * ((∑ i, (regStraighten (split w)).1 i ^ 2)
                + deepestCoreF H r (coreAbsorb (split w)).2.1) := by
  -- `split` (obligation (i), MP reindex carrying the deepest point to `0`).
  obtain ⟨split, hsplit_mp, hsplit_base⟩ :=
    deepestSplit_exists H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL))
  -- PIN 0: the CONCRETE `coreAbsorb = deepestCoreAbsorb` (the cutoff Schur shear) + its
  -- slot-fix/basepoint/rlct (Option A: concrete, so PIN 2 sees the same map).
  set coreAbsorb := deepestCoreAbsorb H r hr hL with hca_def
  obtain ⟨hca_base, hca_reg, hca_spec, hca_rlct⟩ := deepest_coreAbsorb_exists H r hr hL
  -- PIN 1: `regStraighten` (the (C)-fallback total-fn E-straightening) + its props (against `coreAbsorb`).
  obtain ⟨regStraighten, hra_cont, hra_base, hra_core, hra_spec, hra_rlct⟩ :=
    deepest_regAbsorb_exists H r B hB hr hL (deepestNGauge H r) coreAbsorb
  -- PIN 2: the loss squeeze (consuming the concrete `coreAbsorb` + `regStraighten`).
  obtain ⟨c₁, c₂, hc₁, hc₂, U, hU, hsq⟩ :=
    deepest_loss_squeeze H r B hB hr hL (deepestNGauge H r) split coreAbsorb regStraighten hsplit_base
  exact ⟨deepestNGauge H r, split, coreAbsorb, regStraighten, hsplit_mp, hsplit_base,
    hca_base, hca_reg, hca_spec, hca_rlct, hra_cont, hra_base, hra_core, hra_spec, hra_rlct,
    c₁, c₂, hc₁, hc₂, U, hU, hsq⟩

/-- **The `DeepestGaugeChart` instance** (#44c sub-3, `deepest_gauge_squeeze_exists`). Destructures
the bundled construction into the structure. crux2 wires `deepest_gauge_squeeze_exists := this`. -/
theorem deepest_gauge_chart_construct (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Nonempty (DeepestGaugeChart H r B hB hr hL) := by
  obtain ⟨nGauge, split, coreAbsorb, regStraighten, hsplit_mp, hsplit_base, hca_base, hca_reg,
    hca_spec, hca_rlct, hra_cont, hra_base, hra_core, hra_spec, hra_rlct, hsq⟩ :=
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
    regStraighten := regStraighten
    regStraighten_continuous := hra_cont
    regStraighten_basepoint := hra_base
    regStraighten_core := hra_core
    regStraighten_spectator := hra_spec
    regAbsorb_rlct := hra_rlct
    loss_squeeze := hsq }⟩

end DLNFibre.DLN.RLCT
