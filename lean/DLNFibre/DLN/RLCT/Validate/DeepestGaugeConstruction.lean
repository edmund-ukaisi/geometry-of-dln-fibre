import DLNFibre.DLN.RLCT.Validate.DeepestGaugeChart
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeBlocks
import DLNFibre.DLN.RLCT.Validate.DeepestSplitReindex
import DLNFibre.DLN.RLCT.Validate.DeepestFrameRaw
import DLNFibre.DLN.RLCT.Validate.DeepestFrame
import DLNFibre.DLN.RLCT.Validate.DeepestFramedProduct
import DLNFibre.DLN.RLCT.Validate.DeepestTelescoping
import DLNFibre.DLN.RLCT.Validate.DeepestSchurShift
import DLNFibre.DLN.RLCT.Validate.DeepestRegAbsorbIFT
import DLNFibre.DLN.RLCT.Validate.DeepestRegSliceFderiv
import DLNFibre.DLN.RLCT.Validate.DeepestRegBlockInvertible
import DLNFibre.DLN.RLCT.Validate.DeepestFramedProductPivot
import DLNFibre.DLN.RLCT.Validate.DeepestRegSliceFderivPivot
import DLNFibre.DLN.RLCT.Validate.DeepestPivotFrame
import DLNFibre.DLN.RLCT.Foundations.CoreShearMP
import DLNFibre.DLN.RLCT.Foundations.DeepestSplitHaar

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

/-- **`gaugeSlotRead` is continuous** — each per-layer block is a coordinate of the homeomorphism
`regGaugeSlotEquiv` (the `X/Y/Z` blocks) or of `paramsEquivFlat.symm` (the `T`-core), composed with
continuous slot projections. The continuity half of `IsGaugeSliceDecode`. -/
theorem continuous_gaugeSlotRead (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Continuous (gaugeSlotRead H r hr hL) := by
  have hg : Continuous (fun q : DeepestSplit H r (deepestNGauge H r) =>
      regGaugeSlotEquiv H r hr hL (q.1, q.2.2)) :=
    (regGaugeSlotEquiv H r hr hL).continuous.comp
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  refine continuous_pi (fun s => ?_)
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_))
  · exact continuous_matrix (fun i j =>
      (continuous_apply (⟨s, Sum.inl (Sum.inl (i, j))⟩ : RegGaugeIdx H r)).comp hg)
  · exact continuous_matrix (fun i j =>
      (continuous_apply (⟨s, Sum.inl (Sum.inr (i, j))⟩ : RegGaugeIdx H r)).comp hg)
  · exact continuous_matrix (fun i j =>
      (continuous_apply (⟨s, Sum.inr (i, j)⟩ : RegGaugeIdx H r)).comp hg)
  · exact (continuous_apply s).comp
      ((continuous_paramsEquivFlat_symm (deepestM H r)).comp (continuous_fst.comp continuous_snd))

/-- **`gaugeSlotRead` at the origin reads all-zero blocks** — `regGaugeSlotEquiv (0,0) = 0` zeroes the
`X/Y/Z` blocks; `paramsEquivFlat.symm 0 = (fun _ => 0)` (forward `0 ↦ 0` + `symm_apply_apply`) zeroes
the `T`-core. The basepoint half of `IsGaugeSliceDecode`. -/
theorem gaugeSlotRead_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    gaugeSlotRead H r hr hL 0 = fun _ => (0, 0, 0, 0) := by
  funext s
  have hg : regGaugeSlotEquiv H r hr hL
      ((0 : DeepestSplit H r (deepestNGauge H r)).1, (0 : DeepestSplit H r (deepestNGauge H r)).2.2)
      = 0 := by
    rw [show ((0 : DeepestSplit H r (deepestNGauge H r)).1,
        (0 : DeepestSplit H r (deepestNGauge H r)).2.2) = 0 from rfl]
    exact regGaugeSlotEquiv_zero H r hr hL
  have hfwd : (paramsEquivFlat (deepestM H r)) (fun _ => 0) = 0 := by
    funext i; show (paramsEquivFlat (deepestM H r)) (fun _ => 0) i = (0 : Fin _ → ℝ) i; rfl
  have hTfun : (paramsEquivFlat (deepestM H r)).symm
      ((0 : DeepestSplit H r (deepestNGauge H r)).2.1) = (fun _ => 0) := by
    rw [show (0 : DeepestSplit H r (deepestNGauge H r)).2.1 = 0 from rfl, ← hfwd,
      (paramsEquivFlat (deepestM H r)).symm_apply_apply]
  show (gaugeSlotRead H r hr hL 0 s) = (0, 0, 0, 0)
  simp only [gaugeSlotRead, hg, hTfun]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · ext i j; rfl
  · ext i j; rfl
  · ext i j; rfl
  · rfl

/-- **The deepest-point gauge decode satisfies the slot-grouping contract** (`IsGaugeSliceDecode` —
the controller's durable slot-grouping pin, the #64-confound guard). `gaugeDecode := gaugeSlotRead`
(the frame-free read; the constant frame #77 + `split.symm` compose INSIDE, fixing the origin +
continuous, so the contract's continuity + basepoint hold of the read). Built from `regGaugeSlotEquiv`
(#78) + the g223 slot-index map + `paramsEquivFlat` (the banked accessors). -/
theorem deepest_isGaugeSliceDecode (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    IsGaugeSliceDecode H r (deepestNGauge H r) (gaugeSlotRead H r hr hL) where
  continuous := continuous_gaugeSlotRead H r hr hL
  basepoint := gaugeSlotRead_zero H r hr hL

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
determined slot-fix / basepoint / `coreAbsorb_rlct` (the MP route: `measurePreserving_coreShear` ⟹
`rlctAtOn_comp_homeomorph`, det = 1 — NOT the abstract #71 bounded-unit peel) are wired directly. -/

/-- **PIN 1 — the regular straightening** (the (C) wall-fallback shape, #90). Built from a pivot map
`E_pivot : Reg × Spec → Reg` (the producer's nonlinear reg-straightening, reading reg + spec): the
total self-map `regStraightenOf E_pivot` (core/spectator/origin-fixing, globally continuous, so `Φ`
stays globally measurable for `rlctAtOn_squeeze`). The `regAbsorb_rlct` peel is discharged by
`rlctAtOn_regAbsorb_reduce` (the `coreAbsorb.symm` conjugation stripping `coreAbsorb` from the core
term) composed with `rlctAtOn_comp_localDiffeo` (the IFT → `#72` adapter): `E_pivot` need only be
`ContDiff ℝ ⊤` with `dE(0) = id` (typed as `HasStrictFDerivAt E_pivot (fst) 0`) — its concrete
nonlinear form is PIN 2's (the squeeze). The `coreAbsorb` MP + slot-fix data threads the reduce. -/
theorem deepest_regAbsorb_exists (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (nGauge : ℕ)
    (coreAbsorb : DeepestSplit H r nGauge ≃ₜ DeepestSplit H r nGauge)
    (hca_mp : MeasurePreserving coreAbsorb volume volume)
    (hca_base : coreAbsorb 0 = 0)
    (hca_reg : ∀ q : DeepestSplit H r nGauge, (coreAbsorb q).1 = q.1)
    (hca_spec : ∀ q : DeepestSplit H r nGauge, (coreAbsorb q).2.2 = q.2.2)
    (E_pivot : (Fin (deepestNReg H r) → ℝ) × (Fin nGauge → ℝ) → (Fin (deepestNReg H r) → ℝ))
    (hEp_contdiff : ContDiff ℝ (⊤ : ℕ∞) E_pivot)
    (D_E : ((Fin (deepestNReg H r) → ℝ) × (Fin nGauge → ℝ)) →L[ℝ] (Fin (deepestNReg H r) → ℝ))
    (hEp_deriv : HasStrictFDerivAt E_pivot D_E 0)
    (e : DeepestSplit H r nGauge ≃L[ℝ] DeepestSplit H r nGauge)
    (he : (e : DeepestSplit H r nGauge →L[ℝ] DeepestSplit H r nGauge) = regStraightenTotalCLM D_E)
    (hEp_base : E_pivot 0 = 0) :
    ∃ regStraighten : DeepestSplit H r nGauge → DeepestSplit H r nGauge,
      Continuous regStraighten ∧
      regStraighten 0 = 0 ∧
      (∀ q : DeepestSplit H r nGauge, (regStraighten q).2.1 = q.2.1) ∧
      (∀ q : DeepestSplit H r nGauge, (regStraighten q).2.2 = q.2.2) ∧
      -- The reg-output IS the pivot residual `E_pivot` on `(reg, spec)` (the defining identity that
      -- PIN 2's `loss_squeeze` needs — `regStraighten` reads the SAME nonlinear residual the loss does).
      (∀ q : DeepestSplit H r nGauge, (regStraighten q).1 = E_pivot (q.1, q.2.2)) ∧
      rlctAtOn
          (fun q : DeepestSplit H r nGauge =>
            (∑ i, (regStraighten q).1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
          (0 : DeepestSplit H r nGauge)
        = rlctAtOn
            (fun q : DeepestSplit H r nGauge =>
              (∑ i, q.1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
            (0 : DeepestSplit H r nGauge) := by
  classical
  -- The reg-straightening witness and its structural props (incl. the reg-output value).
  refine ⟨regStraightenOf E_pivot,
    continuous_regStraightenOf E_pivot hEp_contdiff.continuous,
    regStraightenOf_basepoint E_pivot hEp_base,
    fun q => regStraightenOf_core E_pivot q,
    fun q => regStraightenOf_spectator E_pivot q,
    fun q => regStraightenOf_fst E_pivot q, ?_⟩
  -- `regAbsorb_rlct`: strip `coreAbsorb` from the core term (reduce), then peel `regStraightenOf`
  -- via the IFT local-diffeo adapter (the decoupled `hpeel`).
  refine rlctAtOn_regAbsorb_reduce coreAbsorb (regStraightenOf E_pivot)
    (fun rg : Fin (deepestNReg H r) → ℝ => ∑ i, rg i ^ 2) (deepestCoreF H r)
    hca_mp hca_base hca_reg hca_spec
    (fun q q' hq hq' => regStraightenOf_regdep E_pivot q q' hq hq') ?_
  -- The decoupled peel: `f = regStraightenOf E_pivot`, smooth + `dE(0) = the invertible SHEAR e`
  -- (#120-corrected: NOT `fst` — the opaque layout shears the gauge-X's into reg) ⟹ local diffeo.
  refine rlctAtOn_comp_localDiffeo
    (fun q : DeepestSplit H r nGauge => (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
    (0 : DeepestSplit H r nGauge) (regStraightenOf E_pivot) e ?_ ?_ ?_
  · -- `regStraightenOf E_pivot` is `ContDiff ⊤`.
    refine ContDiff.prodMk ?_ (ContDiff.prodMk (contDiff_fst.comp contDiff_snd)
      (contDiff_snd.comp contDiff_snd))
    exact hEp_contdiff.comp (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd))
  · -- `HasStrictFDerivAt (regStraightenOf E_pivot) (e) 0`: the assembled total CLM IS `e` (via `he`).
    rw [he]
    exact hasStrictFDerivAt_regStraightenOf_gen E_pivot D_E hEp_deriv
  · -- `regStraightenOf E_pivot 0 = 0`.
    exact regStraightenOf_basepoint E_pivot hEp_base

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

/-- `deepestCoreAbsorb` is MEASURE-PRESERVING (the det-1 cutoff-Schur shear — `measurePreserving_coreShear`).
Threaded into PIN 1's `regAbsorb_rlct` (`rlctAtOn_regAbsorb_reduce` needs `coreAbsorb` MP for the
`coreAbsorb.symm` conjugation that strips it from the core term). -/
theorem deepestCoreAbsorb_mp (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    MeasurePreserving (deepestCoreAbsorb H r hr hL) volume volume :=
  measurePreserving_coreShear (deepestNReg H r) (flatDim (deepestM H r)) (deepestNGauge H r)
    (schurCutoffShift H r hr hL) (continuous_schurCutoffShift H r hr hL)

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

/-! ## The shared pivot map `deepestEPivot` (the PIN1↔PIN2 coupling object)

The reg-straightening's reg-output is `deepestEPivot` — the genuine nonlinear straightened residual
reading the reg + spectator slots, with `dE(0) = id` (typed `HasStrictFDerivAt deepestEPivot (fst) 0`).
PIN 1 needs ONLY that derivative fact (the IFT/peel is form-agnostic); PIN 2's squeeze needs its
concrete value (`(deepestEPivot (split w).reg, (split w).spec)` ≍ the loss residual `E`). So this is
the SHARED coupling object — defined once, consumed by both pins. Its three properties (`ContDiff ⊤`,
`HasStrictFDerivAt (fst) 0`, `0 ↦ 0`) are the residual gauge-geometry obligation: the product-residual
expansion `∏(I+X_s) − I` read off the gauge slots, certified `dE(0) = id` (pp2 #91, general L). -/

/-- The pack equivalence `Fin nReg ≃ (r×r) ⊕ ((r×M_L) ⊕ (M_0×r))` — the THREE regular residual blocks
`(P11−I, P12, P21)` of `∏C` flatten into the `nReg = r(H_0+H_L−r)` reg coordinates. **#120 explicit:**
`:= regPivotFinEquiv` (the TRANSPARENT `finProdFinEquiv`/`finSumFinEquiv` enumeration in
`DeepestSplitReindex`), SHARED with `regGaugeIdxSplit`'s reg-half (which routes via
`regBoundaryToRegGauge ∘ regPivotFinEquiv`), so the two cancel and the gauge-zero reg-slice derivative is
`id` by construction. `_base`/`_contdiff` need only that it is a coordinate bijection (it is, an `Equiv`). -/
noncomputable def regResidualPack (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    Fin (deepestNReg H r)
      ≃ (Fin r × Fin r) ⊕ ((Fin r × Fin (H (Fin.last L) - r)) ⊕ (Fin (H 0 - r) × Fin r)) :=
  regPivotFinEquiv H r hr

/-- The regular residual blocks `(P11 − I, P12, P21)` of the framed product `∏C|_{T=0}`, packed into
`Fin nReg → ℝ` via `regResidualPack`. `P = ∏ (framedParamsReg p)` reindexed to `r ⊕ M` block shape;
`P11 = toBlocks₁₁`, `P12 = toBlocks₁₂`, `P21 = toBlocks₂₁`; the residual is `(P11−1, P12, P21)`. -/
noncomputable def deepestEPivot (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
    (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ) → (Fin (deepestNReg H r) → ℝ) :=
  fun p =>
    let P := Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
      (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
      (prod H (framedParamsRegPivot H r hr hL J Pf Qf p))
    fun i => match regResidualPack H r hr i with
      | Sum.inl (a, b) => (P.toBlocks₁₁ - 1) a b
      | Sum.inr (Sum.inl (a, b)) => P.toBlocks₁₂ a b
      | Sum.inr (Sum.inr (a, b)) => P.toBlocks₂₁ a b

theorem deepestEPivot_contdiff (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (deepestEPivot H r hr hL J Pf Qf) := by
  -- Each layer entry of `framedParamsRegPivot` is `ContDiff` (`contDiff_framedParamsRegPivot_entry`),
  -- so each entry of `prod H (framedParamsRegPivot ·)` is `ContDiff` (`contDiff_prod_entry`).
  have hlayer : ∀ (s : Fin L) (a : Fin (H s.castSucc)) (b : Fin (H s.succ)),
      ContDiff ℝ (⊤ : ℕ∞) (fun p => framedParamsRegPivot H r hr hL J Pf Qf p s a b) :=
    contDiff_framedParamsRegPivot_entry H r hr hL J Pf Qf
  have hprod : ∀ (a : Fin (H 0)) (b : Fin (H (Fin.last L))),
      ContDiff ℝ (⊤ : ℕ∞) (fun p => prod H (framedParamsRegPivot H r hr hL J Pf Qf p) a b) :=
    fun a b => contDiff_prod_entry H (framedParamsRegPivot H r hr hL J Pf Qf) hlayer a b
  -- `deepestEPivot p` is a `Fin nReg → ℝ` whose each coordinate is (a `prod`-entry, reindexed) − const.
  refine contDiff_pi.2 (fun i => ?_)
  -- The `i`-coordinate selects one match-arm (independent of `p`); rewrite to that arm, then it is a
  -- reindexed `prod`-entry (minus the constant `1` on the `inl` arm).
  have hcoord : (fun p => deepestEPivot H r hr hL J Pf Qf p i)
      = fun p =>
        let P := Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (prod H (framedParamsRegPivot H r hr hL J Pf Qf p))
        match regResidualPack H r hr i with
        | Sum.inl (a, b) => (P.toBlocks₁₁ - 1) a b
        | Sum.inr (Sum.inl (a, b)) => P.toBlocks₁₂ a b
        | Sum.inr (Sum.inr (a, b)) => P.toBlocks₂₁ a b := rfl
  rw [hcoord]
  rcases regResidualPack H r hr i with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · simp only [Matrix.toBlocks₁₁, Matrix.sub_apply, Matrix.of_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_symm]
    exact (hprod _ _).sub contDiff_const
  · simp only [Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm]
    exact hprod _ _
  · simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm]
    exact hprod _ _

/-- **The pivot-split P11 cross-read** (the `Y · B₂₁` analogue of `pivot_devY_read_toBlocks₁₂`). The
top-left (`P11`, `Fin r × Fin r`) block of the read of the Y-deviation-conjugated `Q` is
`Y · (reindex eJ eJ Q).toBlocks₂₁` — the cross term that `regBlockCLE`'s `+ Y · B₂₁` consumes in the
`P11` block. Proof idiom identical to the banked `toBlocks₁₂` keystone: split at the middle index `eJ`
(`submatrix_mul_equiv`), the outer reindex cancels the inserted one, then `fromBlocks_multiply`. -/
theorem pivot_devY_read_toBlocks₁₁ {a b r : ℕ}
    (eR : Fin a ≃ Fin r ⊕ Fin (a - r)) (eJ : Fin b ≃ Fin r ⊕ Fin (b - r))
    (Y : Matrix (Fin r) (Fin (b - r)) ℝ) (Q : Matrix (Fin b) (Fin b) ℝ) :
    (Matrix.reindex eR eJ
        ((Matrix.reindex eR.symm eJ.symm (Matrix.fromBlocks 0 Y 0 0)) * Q)).toBlocks₁₁
      = Y * (Matrix.reindex eJ eJ Q).toBlocks₂₁ := by
  have hsplit : Matrix.reindex eR eJ
        ((Matrix.reindex eR.symm eJ.symm (Matrix.fromBlocks 0 Y 0 0)) * Q)
      = (Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) ℝ) Y 0 0)
          * (Matrix.reindex eJ eJ Q) := by
    have hQ : Q = (Matrix.reindex eJ eJ Q).submatrix eJ eJ := by
      simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
        Matrix.submatrix_id_id]
    simp only [Matrix.reindex_apply, Equiv.symm_symm]
    conv_lhs => rw [hQ]
    rw [Matrix.submatrix_mul_equiv (Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) ℝ) Y 0 0)
        (Matrix.reindex eJ eJ Q) eR eJ eJ, Matrix.submatrix_submatrix,
      Equiv.self_comp_symm, Equiv.self_comp_symm, Matrix.submatrix_id_id]
    rfl
  rw [hsplit]
  -- `(fromBlocks 0 Y 0 0 * M).toBlocks₁₁ = Y · M.toBlocks₂₁`: expand `M` into its blocks, multiply.
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (Matrix.reindex eJ eJ Q)]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁]
  simp only [Matrix.zero_mul, zero_add]

/-- The matrix-to-pi reshape `≃L` `Matrix (Fin a) (Fin b) ℝ ≃L (Fin a × Fin b → ℝ)` (finite-dim, so the
`LinearEquiv` upgrades to a `≃L`). The reg-residual decode reads `r0` into the three block matrices
through `regResidualPack`; this is the per-block reshape brick. -/
noncomputable def matrixPiCLE (a b : ℕ) :
    Matrix (Fin a) (Fin b) ℝ ≃L[ℝ] (Fin a × Fin b → ℝ) :=
  (((Matrix.ofLinearEquiv ℝ).symm.trans
    (LinearEquiv.curry ℝ ℝ (Fin a) (Fin b)).symm) : Matrix (Fin a) (Fin b) ℝ ≃ₗ[ℝ]
      (Fin a × Fin b → ℝ)).toContinuousLinearEquiv

@[simp] theorem matrixPiCLE_apply (a b : ℕ) (M : Matrix (Fin a) (Fin b) ℝ) (p : Fin a × Fin b) :
    matrixPiCLE a b M p = M p.1 p.2 := rfl

/-- The matrix-to-pi reshape `LinearEquiv` `Matrix (Fin a) (Fin b) ℝ ≃ₗ (Fin a × Fin b → ℝ)` (the
un-upgraded `matrixPiCLE`; kept as a `LinearEquiv` so the reg-slice decode composes WITHOUT the
`piCongrLeft` cast and reads each block by `rfl`). -/
noncomputable def matrixPiLE (a b : ℕ) :
    Matrix (Fin a) (Fin b) ℝ ≃ₗ[ℝ] (Fin a × Fin b → ℝ) :=
  (Matrix.ofLinearEquiv ℝ).symm.trans (LinearEquiv.curry ℝ ℝ (Fin a) (Fin b)).symm

@[simp] theorem matrixPiLE_symm_apply (a b : ℕ) (f : Fin a × Fin b → ℝ) (i : Fin a) (j : Fin b) :
    (matrixPiLE a b).symm f i j = f (i, j) := rfl

/-- **The reg-slice decode `LinearEquiv`** `(Fin nReg → ℝ) ≃ₗ (YSp × (XSp × ZSp))`, the reshape the
value-fold lands `regBlockCLE` on (layout `(Y, (X, Z))`: `Y` = P12-block, `X` = P11-block, `Z` =
P21-block). Built CAST-FREE: `funCongrLeft` precomposes by `regResidualPack.symm` (a clean `f ∘ ·`, no
`piCongrLeft` transport), `sumArrowLequivProdArrow` splits the sum-domain, `matrixPiLE.symm` reshapes
each arm, and a prod-reorder lands `(Y, (X, Z))`. Every step reads by `rfl`, so the block-apply lemmas
below are `rfl`. -/
noncomputable def decodeRegSliceLE (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    (Fin (deepestNReg H r) → ℝ) ≃ₗ[ℝ]
      (Matrix (Fin r) (Fin (H (Fin.last L) - r)) ℝ
        × (Matrix (Fin r) (Fin r) ℝ × Matrix (Fin (H 0 - r)) (Fin r) ℝ)) :=
  -- (Fin nReg → ℝ) ≃ₗ (Xidx ⊕ (Yidx ⊕ Zidx) → ℝ) by precomposition with regResidualPack.symm
  (LinearEquiv.funCongrLeft ℝ ℝ (regResidualPack H r hr).symm).trans <|
  -- split the outer sum: (Xidx → ℝ) × ((Yidx ⊕ Zidx) → ℝ)
  (LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).trans <|
  -- reshape Xidx-arm to a matrix; split the inner sum on the second arm
  ((matrixPiLE r r).symm.prodCongr
    ((LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).trans
      ((matrixPiLE r (H (Fin.last L) - r)).symm.prodCongr (matrixPiLE (H 0 - r) r).symm))).trans <|
  -- reorder (X, (Y, Z)) → (Y, (X, Z))
  { toFun := fun p => (p.2.1, (p.1, p.2.2))
    invFun := fun q => (q.2.1, (q.1, q.2.2))
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- **The reg-slice decode `≃L`** — the finite-dim upgrade of `decodeRegSliceLE` (the reshape the
value-fold lands `regBlockCLE` on). -/
noncomputable def decodeRegSliceCLE (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    (Fin (deepestNReg H r) → ℝ) ≃L[ℝ]
      (Matrix (Fin r) (Fin (H (Fin.last L) - r)) ℝ
        × (Matrix (Fin r) (Fin r) ℝ × Matrix (Fin (H 0 - r)) (Fin r) ℝ)) :=
  (decodeRegSliceLE H r hr).toContinuousLinearEquiv

@[simp] theorem decodeRegSliceCLE_coe (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    ⇑(decodeRegSliceCLE H r hr) = decodeRegSliceLE H r hr :=
  LinearEquiv.coe_toContinuousLinearEquiv' _

/-- **The decode forward reads** `decodeRegSliceCLE v = (Y, (X, Z))` where each block reads `v` at the
matching `regResidualPack`-coordinate (X = P11 on the `inl` arm, Y = P12 on `inr ∘ inl`, Z = P21 on
`inr ∘ inr`). All three are `rfl` (the decode is cast-free). -/
@[simp] theorem decodeRegSliceCLE_apply_X (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (v : Fin (deepestNReg H r) → ℝ) (a b : Fin r) :
    (decodeRegSliceCLE H r hr v).2.1 a b
      = v ((regResidualPack H r hr).symm (Sum.inl (a, b))) := rfl

@[simp] theorem decodeRegSliceCLE_apply_Y (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (v : Fin (deepestNReg H r) → ℝ) (a : Fin r)
    (b : Fin (H (Fin.last L) - r)) :
    (decodeRegSliceCLE H r hr v).1 a b
      = v ((regResidualPack H r hr).symm (Sum.inr (Sum.inl (a, b)))) := rfl

@[simp] theorem decodeRegSliceCLE_apply_Z (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (v : Fin (deepestNReg H r) → ℝ)
    (a : Fin (H 0 - r)) (b : Fin r) :
    (decodeRegSliceCLE H r hr v).2.2 a b
      = v ((regResidualPack H r hr).symm (Sum.inr (Sum.inr (a, b)))) := rfl

/-- **The encode read** `decodeRegSliceCLE.symm (Y, (X, Z)) i` reads back the matching block entry at the
`regResidualPack`-coordinate of `i` (cast-free, `rfl` after casing the pack). The normal-form direction. -/
theorem decodeRegSliceCLE_symm_apply (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (Y : Matrix (Fin r) (Fin (H (Fin.last L) - r)) ℝ) (X : Matrix (Fin r) (Fin r) ℝ)
    (Z : Matrix (Fin (H 0 - r)) (Fin r) ℝ) (i : Fin (deepestNReg H r)) :
    (decodeRegSliceCLE H r hr).symm (Y, (X, Z)) i
      = match regResidualPack H r hr i with
        | Sum.inl (a, b) => X a b
        | Sum.inr (Sum.inl (a, b)) => Y a b
        | Sum.inr (Sum.inr (a, b)) => Z a b := by
  rw [decodeRegSliceCLE, LinearEquiv.coe_toContinuousLinearEquiv_symm']
  simp only [decodeRegSliceLE, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearEquiv.funCongrLeft_symm, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    Equiv.symm_symm, Function.comp_apply]
  rcases regResidualPack H r hr i with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> rfl

/-- `reindex` distributes over `+` (entrywise; `submatrix_add`). -/
theorem reindex_add {a b r s : ℕ} (eₘ : Fin a ≃ Fin r ⊕ Fin (a - r))
    (eₙ : Fin b ≃ Fin s ⊕ Fin (b - s)) (A B : Matrix (Fin a) (Fin b) ℝ) :
    Matrix.reindex eₘ eₙ (A + B) = Matrix.reindex eₘ eₙ A + Matrix.reindex eₘ eₙ B := rfl

/-- `toBlocks₁₁` distributes over `+` (entrywise). -/
theorem toBlocks₁₁_add {n o l m : Type*} (A B : Matrix (n ⊕ o) (l ⊕ m) ℝ) :
    (A + B).toBlocks₁₁ = A.toBlocks₁₁ + B.toBlocks₁₁ := rfl

/-- `toBlocks₁₂` distributes over `+` (entrywise). -/
theorem toBlocks₁₂_add {n o l m : Type*} (A B : Matrix (n ⊕ o) (l ⊕ m) ℝ) :
    (A + B).toBlocks₁₂ = A.toBlocks₁₂ + B.toBlocks₁₂ := rfl

/-- `toBlocks₂₁` distributes over `+` (entrywise). -/
theorem toBlocks₂₁_add {n o l m : Type*} (A B : Matrix (n ⊕ o) (l ⊕ m) ℝ) :
    (A + B).toBlocks₂₁ = A.toBlocks₂₁ + B.toBlocks₂₁ := rfl

/-- **The row-frame left-conjugation read** `reindex eR eJ (A · reindex eR.symm eJ.symm (fromBlocks X 0 Z
0)) = (reindex eR eR A) · fromBlocks X 0 Z 0` — split the product at the shared row interface `eR`. The
`A·devXZ` analogue of `pivot_devY_read`; its `toBlocks` read off the `(A₁₁X+A₁₂Z, A₂₁X+A₂₂Z)` pair. -/
theorem mulBlock_devXZ_read {a b r : ℕ}
    (eR : Fin a ≃ Fin r ⊕ Fin (a - r)) (eJ : Fin b ≃ Fin r ⊕ Fin (b - r))
    (A : Matrix (Fin a) (Fin a) ℝ) (X : Matrix (Fin r) (Fin r) ℝ)
    (Z : Matrix (Fin (a - r)) (Fin r) ℝ) :
    Matrix.reindex eR eJ
        (A * Matrix.reindex eR.symm eJ.symm (Matrix.fromBlocks X 0 Z 0))
      = Matrix.reindex eR eR A * Matrix.fromBlocks X 0 Z 0 := by
  have hA : A = (Matrix.reindex eR eR A).submatrix eR eR := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
      Matrix.submatrix_id_id]
  simp only [Matrix.reindex_apply, Equiv.symm_symm]
  conv_lhs => rw [hA]
  rw [Matrix.submatrix_mul_equiv (Matrix.reindex eR eR A) (Matrix.fromBlocks X 0 Z 0) eR eR eJ,
    Matrix.submatrix_submatrix, Equiv.self_comp_symm, Equiv.self_comp_symm, Matrix.submatrix_id_id]
  rfl

/-- The `A·devXZ` read's top-left block: `(reindex eR eR A · fromBlocks X 0 Z 0).toBlocks₁₁ =
A₁₁·X + A₁₂·Z`. -/
theorem mulBlock_devXZ_toBlocks₁₁ {a c r : ℕ} (eR : Fin a ≃ Fin r ⊕ Fin (a - r))
    (A : Matrix (Fin a) (Fin a) ℝ) (X : Matrix (Fin r) (Fin r) ℝ)
    (Z : Matrix (Fin (a - r)) (Fin r) ℝ) :
    (Matrix.reindex eR eR A * Matrix.fromBlocks X (0 : Matrix (Fin r) (Fin c) ℝ) Z 0).toBlocks₁₁
      = (Matrix.reindex eR eR A).toBlocks₁₁ * X + (Matrix.reindex eR eR A).toBlocks₁₂ * Z := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (Matrix.reindex eR eR A)]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁]

/-- The `A·devXZ` read's top-right block is `0` (the right column-block of `fromBlocks X 0 Z 0` is 0). -/
theorem mulBlock_devXZ_toBlocks₁₂ {a c r : ℕ} (eR : Fin a ≃ Fin r ⊕ Fin (a - r))
    (A : Matrix (Fin a) (Fin a) ℝ) (X : Matrix (Fin r) (Fin r) ℝ)
    (Z : Matrix (Fin (a - r)) (Fin r) ℝ) :
    (Matrix.reindex eR eR A
        * Matrix.fromBlocks X (0 : Matrix (Fin r) (Fin c) ℝ) Z 0).toBlocks₁₂ = 0 := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (Matrix.reindex eR eR A)]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₂]
  simp [Matrix.mul_zero]

/-- The `A·devXZ` read's bottom-left block: `(reindex eR eR A · fromBlocks X 0 Z 0).toBlocks₂₁ =
A₂₁·X + A₂₂·Z`. -/
theorem mulBlock_devXZ_toBlocks₂₁ {a c r : ℕ} (eR : Fin a ≃ Fin r ⊕ Fin (a - r))
    (A : Matrix (Fin a) (Fin a) ℝ) (X : Matrix (Fin r) (Fin r) ℝ)
    (Z : Matrix (Fin (a - r)) (Fin r) ℝ) :
    (Matrix.reindex eR eR A * Matrix.fromBlocks X (0 : Matrix (Fin r) (Fin c) ℝ) Z 0).toBlocks₂₁
      = (Matrix.reindex eR eR A).toBlocks₂₁ * X + (Matrix.reindex eR eR A).toBlocks₂₂ * Z := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (Matrix.reindex eR eR A)]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁]

/-- The pivot-split P21 cross-read is `0`: `(reindex eR eJ ((reindex eR.symm eJ.symm (fromBlocks 0 Y 0
0)) * Q)).toBlocks₂₁ = 0` — the `fromBlocks 0 Y 0 0` has zero bottom rows. -/
theorem pivot_devY_read_toBlocks₂₁ {a b r : ℕ}
    (eR : Fin a ≃ Fin r ⊕ Fin (a - r)) (eJ : Fin b ≃ Fin r ⊕ Fin (b - r))
    (Y : Matrix (Fin r) (Fin (b - r)) ℝ) (Q : Matrix (Fin b) (Fin b) ℝ) :
    (Matrix.reindex eR eJ
        ((Matrix.reindex eR.symm eJ.symm (Matrix.fromBlocks 0 Y 0 0)) * Q)).toBlocks₂₁ = 0 := by
  have hsplit : Matrix.reindex eR eJ
        ((Matrix.reindex eR.symm eJ.symm (Matrix.fromBlocks 0 Y 0 0)) * Q)
      = (Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) ℝ) Y 0 0) * (Matrix.reindex eJ eJ Q) := by
    have hQ : Q = (Matrix.reindex eJ eJ Q).submatrix eJ eJ := by
      simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
        Matrix.submatrix_id_id]
    simp only [Matrix.reindex_apply, Equiv.symm_symm]
    conv_lhs => rw [hQ]
    rw [Matrix.submatrix_mul_equiv (Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) ℝ) Y 0 0)
        (Matrix.reindex eJ eJ Q) eR eJ eJ, Matrix.submatrix_submatrix,
      Equiv.self_comp_symm, Equiv.self_comp_symm, Matrix.submatrix_id_id]
    rfl
  rw [hsplit]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (Matrix.reindex eJ eJ Q)]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁]
  simp

/-- **A corner left-absorbs a Y-deviation** `reindex(fromBlocks 1 0 0 0) · reindex(fromBlocks 0 Y 0 0)
= reindex(fromBlocks 0 Y 0 0)`: the corner identity passes `Y` to the top-right block; the bottom rows
stay `0`. The `corner·devY` companion of `devXZ_mul_corner` (the `Y`-frame term of the product). -/
theorem corner_mul_devY {a b c r : ℕ}
    (eA : Fin a ≃ Fin r ⊕ Fin (a - r)) (eB : Fin b ≃ Fin r ⊕ Fin (b - r))
    (eC : Fin c ≃ Fin r ⊕ Fin (c - r)) (Y : Matrix (Fin r) (Fin (c - r)) ℝ) :
    (Matrix.reindex eA.symm eB.symm (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0))
        * (Matrix.reindex eB.symm eC.symm (Matrix.fromBlocks 0 Y 0 0))
      = Matrix.reindex eA.symm eC.symm (Matrix.fromBlocks 0 Y 0 0) := by
  simp only [Matrix.reindex_apply, Equiv.symm_symm]
  rw [Matrix.submatrix_mul_equiv (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
      (Matrix.fromBlocks 0 Y 0 0) eA eB eC]
  congr 1
  rw [Matrix.fromBlocks_multiply]
  congr 1 <;>
    · simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      try exact Matrix.one_mul _

/-- **`deepestEPivot`'s reg-block derivative at `0` is the invertible frame factor `F`** (the #91
analytic crux, PIVOT-aligned). On the pivot path the reg-slice `r0 ↦ deepestEPivot J Pf Qf (r0, 0)` has
constant strict derivative `F` (the idempotent sandwich: only `firstLayer` X,Z / `lastLayer` Y survive;
the quadratic cross term `devXZ_corner_devY` has derivative 0). The linear part is the `regBlockCLE`
shape `(X,Y,Z) ↦ (A₁₁X+A₁₂Z + Y·B₂₁, Y·B₂₂, A₂₁X+A₂₂Z)` with `A = reindex (Pf first)` (unit, `hPf`) and
`B₂₂ = (reindex eJ eJ (Qf last))₂₂` (unit, `hQf22` — the genuinely-needed pivot hypothesis the threshold
path lacked, discharged at the call site from the pivot-aligned deepest-point frame). Block-triangular,
so invertible from `IsUnit A` + `IsUnit B₂₂` (`regBlockCLE`). -/
theorem deepestEPivot_regSlice_fderiv (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂)) :
    ∃ F : (Fin (deepestNReg H r) → ℝ) ≃L[ℝ] (Fin (deepestNReg H r) → ℝ),
      HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
          deepestEPivot H r hr hL J Pf Qf (r0, 0))
        (F : (Fin (deepestNReg H r) → ℝ) →L[ℝ] (Fin (deepestNReg H r) → ℝ)) 0 := by
  -- The #91 frame-decorated sandwich, PIVOT-aligned. With the `hQf22` hypothesis NOW supplied (the
  -- pivot frame's `B₂₂`-unit fact, discharged at the call site from `deepestPoint_frame_pivot_exists`),
  -- the `∃ F : ≃L` conclusion IS provable — the threshold-path obstruction (a unit `Qf last` can have a
  -- SINGULAR ₂₂ block; `IsDeepLayers` does NOT force `Qf last` ₂₂-invertible) is sidestepped by the
  -- pivot column-split: the residual `P12` block then reads `readY · B₂₂` with `B₂₂` THIS unit.
  --
  -- THE VALUE-FOLD (the remaining ~250 LoC; Codex `xhigh` skeleton validated, banked bricks below).
  -- The reg-slice product collapses (banked `prod_framedParamsRegPivot_regSlice_collapse`, needs `2≤L`,
  -- `Qf first = 1`) to `firstShapeF (last).castSucc · framedParamsRegPivot (last)`. Writing
  -- `A := reindex e_first e_first (Pf first)`, `B := reindex eJ eJ (Qf last)` in `r ⊕ (·−r)` blocks
  -- (`hPfL` gives `Pf last = 1`; `hQf0` gives `Qf first = 1`), the three residual blocks are LINEAR(r0)
  -- + genuine QUADRATIC(r0). The linear part is, in residual-pack order `(P11−I, P12, P21)`:
  --     F(X,Y,Z) = ( A₁₁·X + A₁₂·Z + Y·B₂₁ ,   Y·B₂₂ ,   A₂₁·X + A₂₂·Z )
  -- — block-triangular, the `regBlockCLE` shape (invertible from `IsUnit A` (`hPf`) + `IsUnit B₂₂`
  -- (`hQf22`)). The quadratic cross `Pf·reindex(fromBlocks 0 (X·Y) 0 (Z·Y))·Qf` (banked
  -- `devXZ_corner_devY`) has strict derivative 0 at 0 (`hasStrictFDerivAt_sum_mul_zero`), so
  -- `deepestEPivot (·,0) = F·(·) + quad`. Then `F.hasStrictFDerivAt.add (quad-deriv-0)` ▸ the normal form.
  --
  -- BANKED bricks for the assembly (all sorry-free, axiom-clean this tide):
  --   • `pivot_devY_read_toBlocks₁₂` (P12 = `Y·B₂₂`) / `pivot_devY_read_toBlocks₁₁` (P11 cross = `Y·B₂₁`);
  --   • `mulBlockPairCLE_apply` (the `(X,Z) ↦ (A₁₁X+A₁₂Z, A₂₁X+A₂₂Z)` arm) + `regBlockCLE`/`_apply`;
  --   • `matrixPiCLE` (per-block reshape `Matrix ≃L (Fin·×Fin·→ℝ)`) — the decode/encode CLE brick;
  --   • `prod_framedParamsRegPivot_regSlice_collapse`, `framedParamsRegPivot_regSlice_last`, `firstShapeF`,
  --     `readX/Y/Z_regSlice_{first,last}` (= single `r0`-coords via `regPivotFinEquiv`), `devXZ_corner_devY`,
  --     `hasStrictFDerivAt_sum_mul_zero`, `hasStrictFDerivAt_prodAux_entry_explicit`.
  -- REMAINING (the genuine bulk, NOT yet written — an honest red): (i) the encode/decode reshape `≃L`s
  -- (`decodeRegSliceCLE : (Fin nReg→ℝ) ≃L (YSp×(XSp×ZSp))` via `matrixPiCLE`+`regPivotFinEquiv`+the
  -- `regResidualPack` layout swap, `encodeResidualCLE` via `regResidualPack.symm`); (ii) the normal-form
  -- matrix identity `hnormal : deepestEPivot (r0,0) = F r0 + quadResidual r0` (`ext i`; case on
  -- `regResidualPack i`; the three block reads + the `P11−1` corner cancel); (iii) the derivative combine.
  --
  -- HISTORICAL (the threshold-path obstruction, why `hQf22` was added; resolved by the pivot split):
  -- the threshold `rank_normal_form_right_only` (rank `r`, tail ROWS vanish) CANNOT yield
  -- `IsUnit (reindex Q).toBlocks₂₂` — COUNTEREXAMPLE (`r = 1`): `A = [0 1]` has rank 1, tail rows vanish,
  -- and ANY `Q` with `A·Q = [1 0]` forces `Q₂₂ = 0`. And a "first `r` columns independent" clause is
  -- UNSATISFIABLE for general `B`: the deepest last layer is `embM·V`, `V = projM·Q⁻¹` a rank-`r` factor
  -- of `B = U·V` (`U` full column rank); its first `r` columns are
  -- independent ⟺ `V`'s first `r` columns are ⟺ (since `B_{:,<r} = U·V_{:,<r}`, `U` injective)
  -- `B`'s OWN first `r` columns are independent — FALSE for valid rank-`r` `B` (e.g. `r=1`, `B = [0,b]`).
  -- The PIVOT split (this statement's `J`) resolves it: the chosen pivot columns lead, so `B₂₂` is the
  -- unit block `hQf22` supplies, and `F` is invertible WITHOUT restricting `B`.
  --
  -- STAGE F (this tide): the value-fold strict-derivative. `L = n+1+1` (from `2 ≤ L`) so the collapse
  -- applies with defeq column types; `F := decode ∘ regBlockCLE ∘ decode.symm` is the invertible frame
  -- factor; `deepestEPivot (r0,0) = F r0 + quad r0` with `quad` purely quadratic (deriv 0 at 0).
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 + 1 := ⟨L - 2, by omega⟩
  -- The block-split row frame and the pivot column frame's lower-right unit block.
  set eR := rThresholdSplit r (H (firstLayer hL).castSucc) (hr _) with heR
  set eJsucc := pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J)
    with heJsucc
  set Bmat := Matrix.reindex eJsucc eJsucc (Qf (lastLayer hL)) with hBmat
  -- The assembled reg-block `≃L` `F` (invertible from `IsUnit (Pf first)` + the `hQf22` `B₂₂`-unit).
  set Fblk := regBlockCLE eR (Pf (firstLayer hL)) hPf Bmat.toBlocks₂₁ Bmat.toBlocks₂₂ hQf22
    with hFblk
  set Fmap : (Fin (deepestNReg H r) → ℝ) ≃L[ℝ] (Fin (deepestNReg H r) → ℝ) :=
    (decodeRegSliceCLE H r hr).trans (Fblk.trans (decodeRegSliceCLE H r hr).symm) with hFmap
  refine ⟨Fmap, ?_⟩
  -- The eJlast/eJsucc reconciliation: the `deepestEPivot` outer column reindex uses
  -- `pivotThresholdSplit r (H (Fin.last L)) J`; the last-layer factor `framedParamsRegPivot_regSlice_last`
  -- uses `eJsucc = pivotThresholdSplit r (H last.succ) (pivotJSucc J)`. At `L = n+1+1` these are defeq.
  have heJ : pivotThresholdSplit r (H (Fin.last (n + 1 + 1))) (hr (Fin.last (n + 1 + 1))) J = eJsucc := by
    rw [heJsucc]; rfl
  -- The collapsed-and-expanded product `prod (framedParamsRegPivot (r0,0))`. Abbreviate the slice reads.
  have hprod : ∀ r0 : Fin (deepestNReg H r) → ℝ,
      prod H (framedParamsRegPivot H r hr hL J Pf Qf (r0, 0))
        = firstShapeF H r hr hL Pf Qf r0 (lastLayer hL).castSucc
            * framedParamsRegPivot H r hr hL J Pf Qf (r0, 0) (lastLayer hL) :=
    fun r0 => prod_framedParamsRegPivot_regSlice_collapse H r hr hL hL2 J Pf Qf hQf0 r0
  -- The product expansion: `firstShapeF₀ · last = corner + (Y-frame) + (A·XZ) + (quad)`. The quad term
  -- is the genuine quadratic cross `Pf_first · reindex(fromBlocks 0 (X·Y) 0 (Z·Y)) · Qf_last`. Stated at
  -- the `firstShapeF₀ · last` (NOT `prod`) form so all row indices are `(firstLayer hL).castSucc` (the
  -- `firstShapeF`/`Pf` spelling) consistently — distributivity then fires without the `H 0`-cast wall.
  have hPexp : ∀ r0 : Fin (deepestNReg H r) → ℝ,
      firstShapeF H r hr hL Pf Qf r0 (lastLayer hL).castSucc
          * framedParamsRegPivot H r hr hL J Pf Qf (r0, 0) (lastLayer hL)
        = Matrix.reindex eR.symm eJsucc.symm (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
          + (Matrix.reindex eR.symm eJsucc.symm
              (Matrix.fromBlocks 0 (readY H r hr hL (r0, 0) (lastLayer hL)) 0 0)) * Qf (lastLayer hL)
          + Pf (firstLayer hL) * Matrix.reindex eR.symm eJsucc.symm
              (Matrix.fromBlocks (readX H r hr hL (r0, 0) (firstLayer hL)) 0
                (readZ H r hr hL (r0, 0) (firstLayer hL)) 0)
          + Pf (firstLayer hL) * Matrix.reindex eR.symm eJsucc.symm
              (Matrix.fromBlocks 0
                (readX H r hr hL (r0, 0) (firstLayer hL) * readY H r hr hL (r0, 0) (lastLayer hL)) 0
                (readZ H r hr hL (r0, 0) (firstLayer hL) * readY H r hr hL (r0, 0) (lastLayer hL)))
              * Qf (lastLayer hL) := by
    intro r0
    -- `firstShapeF`'s codomain is `Fin (H 0)` but its body's row split is `H (firstLayer hL).castSucc`
    -- (defeq). Restate `firstShapeF₀` with the body's `castSucc` row spelling (by `rfl` across the defeq).
    have hfs : firstShapeF H r hr hL Pf Qf r0 (lastLayer hL).castSucc
        = Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _)).symm
            (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
            (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
          + Pf (firstLayer hL) * Matrix.reindex
              (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _)).symm
              (rThresholdSplit r (H (firstLayer hL).succ) (hr _)).symm
              (Matrix.fromBlocks (readX H r hr hL (r0, 0) (firstLayer hL)) 0
                (readZ H r hr hL (r0, 0) (firstLayer hL)) 0)
            * Matrix.reindex (rThresholdSplit r (H (firstLayer hL).succ) (hr _)).symm
                (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
                (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
      rw [firstShapeF, hQf0, Matrix.mul_one]
    -- The last-layer factor (`Pf last = 1`).
    have hlast : framedParamsRegPivot H r hr hL J Pf Qf (r0, 0) (lastLayer hL)
        = Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm eJsucc.symm
            (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
          + Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm eJsucc.symm
              (Matrix.fromBlocks 0 (readY H r hr hL (r0, 0) (lastLayer hL)) 0 0) * Qf (lastLayer hL) := by
      rw [framedParamsRegPivot_regSlice_last H r hr hL hL2 J Pf Qf r0, hPfL, Matrix.one_mul]
    -- Re-elaborate the product `*` node at the body's `castSucc` row index (full `change`), so the
    -- heterogeneous-dim distributivity rewrites fire syntactically.
    rw [hfs, hlast]
    set C0 := Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _)).symm
        (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
        (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) with hC0
    set PD := Pf (firstLayer hL) * Matrix.reindex
        (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _)).symm
        (rThresholdSplit r (H (firstLayer hL).succ) (hr _)).symm
        (Matrix.fromBlocks (readX H r hr hL (r0, 0) (firstLayer hL)) 0
          (readZ H r hr hL (r0, 0) (firstLayer hL)) 0)
      * Matrix.reindex (rThresholdSplit r (H (firstLayer hL).succ) (hr _)).symm
          (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
          (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) with hPD
    set C' := Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm eJsucc.symm
        (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) with hC'
    set EQ := Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm eJsucc.symm
        (Matrix.fromBlocks 0 (readY H r hr hL (r0, 0) (lastLayer hL)) 0 0) * Qf (lastLayer hL) with hEQ
    show (C0 + PD) * (C' + EQ) = _
    rw [Matrix.add_mul C0 PD (C' + EQ), Matrix.mul_add C0 C' EQ, Matrix.mul_add PD C' EQ]
    -- The four terms: `C0·C'`, `C0·EQ`, `PD·C'`, `PD·EQ`, each simplified by the banked corner / dev
    -- lemmas (grouped explicitly so the lemma shapes match), then regrouped by `abel`.
    have ht1 : C0 * C' = Matrix.reindex eR.symm eJsucc.symm
        (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
      rw [hC0, hC']; exact corner_reindex_mul _ _ _
    have ht2 : C0 * EQ = Matrix.reindex eR.symm eJsucc.symm
        (Matrix.fromBlocks 0 (readY H r hr hL (r0, 0) (lastLayer hL)) 0 0) * Qf (lastLayer hL) := by
      rw [hC0, hEQ, ← Matrix.mul_assoc, corner_mul_devY]
    have ht3 : PD * C' = Pf (firstLayer hL) * Matrix.reindex eR.symm eJsucc.symm
        (Matrix.fromBlocks (readX H r hr hL (r0, 0) (firstLayer hL)) 0
          (readZ H r hr hL (r0, 0) (firstLayer hL)) 0) := by
      rw [hPD, hC',
        Matrix.mul_assoc (Pf (firstLayer hL) * Matrix.reindex _ _
          (Matrix.fromBlocks (readX H r hr hL (r0, 0) (firstLayer hL)) 0
            (readZ H r hr hL (r0, 0) (firstLayer hL)) 0)),
        corner_reindex_mul, Matrix.mul_assoc (Pf (firstLayer hL)), devXZ_mul_corner]
    have ht4 : PD * EQ = Pf (firstLayer hL) * Matrix.reindex eR.symm eJsucc.symm
        (Matrix.fromBlocks 0
          (readX H r hr hL (r0, 0) (firstLayer hL) * readY H r hr hL (r0, 0) (lastLayer hL)) 0
          (readZ H r hr hL (r0, 0) (firstLayer hL) * readY H r hr hL (r0, 0) (lastLayer hL)))
        * Qf (lastLayer hL) := by
      rw [hPD, hEQ, Matrix.mul_assoc (Pf (firstLayer hL)),
        Matrix.mul_assoc (Pf (firstLayer hL)),
        ← Matrix.mul_assoc (Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _)).symm
            (rThresholdSplit r (H (firstLayer hL).succ) (hr _)).symm
            (Matrix.fromBlocks (readX H r hr hL (r0, 0) (firstLayer hL)) 0
              (readZ H r hr hL (r0, 0) (firstLayer hL)) 0) *
          Matrix.reindex (rThresholdSplit r (H (firstLayer hL).succ) (hr _)).symm
            (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
            (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)) _ (Qf (lastLayer hL)),
        devXZ_corner_devY, ← heR, ← Matrix.mul_assoc]
    rw [ht1, ht2, ht3, ht4]
    abel
  -- The reindexed product `P = reindex eR eJsucc prod`, as a sum: corner + (Y·Qf) + (A·devXZ) + (quad).
  -- Reading each `toBlocks` (the read lemmas) gives the three residual blocks: P11 = I + (A₁₁X+A₁₂Z) +
  -- Y·B21 + quad11, P12 = Y·B22 + quad12, P21 = (A₂₁X+A₂₂Z) + quad21. The linear parts match `Fblk`.
  -- The quadratic block-read (per coordinate), the deriv-0 part of the normal form.
  set quadM := fun r0 : Fin (deepestNReg H r) → ℝ => Matrix.reindex eR eJsucc (Pf (firstLayer hL)
      * Matrix.reindex eR.symm eJsucc.symm (Matrix.fromBlocks 0
          (readX H r hr hL (r0, 0) (firstLayer hL) * readY H r hr hL (r0, 0) (lastLayer hL)) 0
          (readZ H r hr hL (r0, 0) (firstLayer hL) * readY H r hr hL (r0, 0) (lastLayer hL)))
        * Qf (lastLayer hL)) with hquadM
  set quadE : (Fin (deepestNReg H r) → ℝ) → (Fin (deepestNReg H r) → ℝ) :=
    fun r0 i => match regResidualPack H r hr i with
      | Sum.inl (a, b) => (quadM r0).toBlocks₁₁ a b
      | Sum.inr (Sum.inl (a, b)) => (quadM r0).toBlocks₁₂ a b
      | Sum.inr (Sum.inr (a, b)) => (quadM r0).toBlocks₂₁ a b with hquadE
  -- The reindexed product as a sum of the four reindexed terms (`reindex_add`, rfl). The corner
  -- reindexes to `fromBlocks 1 0 0 0`; the `A·devXZ` term to `(reindex eR eR A)·fromBlocks X 0 Z 0`
  -- (`mulBlock_devXZ_read`); the quad term is `quadM r0`.
  have hPdec : ∀ r0 : Fin (deepestNReg H r) → ℝ,
      Matrix.reindex eR eJsucc (prod H (framedParamsRegPivot H r hr hL J Pf Qf (r0, 0)))
        = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0
          + Matrix.reindex eR eJsucc (Matrix.reindex eR.symm eJsucc.symm
              (Matrix.fromBlocks 0 (readY H r hr hL (r0, 0) (lastLayer hL)) 0 0) * Qf (lastLayer hL))
          + Matrix.reindex eR eR (Pf (firstLayer hL)) * Matrix.fromBlocks
              (readX H r hr hL (r0, 0) (firstLayer hL)) 0 (readZ H r hr hL (r0, 0) (firstLayer hL)) 0
          + quadM r0 := by
    intro r0
    rw [hprod r0, hPexp r0, reindex_add, reindex_add, reindex_add,
      show Matrix.reindex eR eJsucc (Matrix.reindex eR.symm eJsucc.symm
          (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0))
        = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 from by
        simp only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_submatrix,
          Equiv.self_comp_symm, Matrix.submatrix_id_id],
      mulBlock_devXZ_read]
  -- The deepestEPivot reindex (`rThresholdSplit (H 0)` / `pivotThresholdSplit (H (Fin.last L)) J`) is the
  -- same as `reindex eR eJsucc` (defeq: `(firstLayer hL).castSucc = 0`, `heJ`).
  have hPread : ∀ (r0 : Fin (deepestNReg H r) → ℝ),
      Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last (n + 1 + 1))) (hr (Fin.last (n + 1 + 1))) J)
          (prod H (framedParamsRegPivot H r hr hL J Pf Qf (r0, 0)))
        = Matrix.reindex eR eJsucc (prod H (framedParamsRegPivot H r hr hL J Pf Qf (r0, 0))) := by
    intro r0; rw [heJ]; rfl
  -- The decode blocks ARE the slice reads (`decodeRegSliceCLE_apply_*` + `readX/Y/Z_regSlice_*`).
  have hdX : ∀ (r0 : Fin (deepestNReg H r) → ℝ),
      (decodeRegSliceCLE H r hr r0).2.1 = readX H r hr hL (r0, 0) (firstLayer hL) := by
    intro r0; funext a b
    rw [decodeRegSliceCLE_apply_X, readX_regSlice_first, regResidualPack]
  have hdZ : ∀ (r0 : Fin (deepestNReg H r) → ℝ),
      (decodeRegSliceCLE H r hr r0).2.2 = readZ H r hr hL (r0, 0) (firstLayer hL) := by
    intro r0; funext a b
    rw [decodeRegSliceCLE_apply_Z, readZ_regSlice_first, regResidualPack]
  have hdY : ∀ (r0 : Fin (deepestNReg H r) → ℝ),
      (decodeRegSliceCLE H r hr r0).1 = readY H r hr hL (r0, 0) (lastLayer hL) := by
    intro r0; funext a b
    rw [decodeRegSliceCLE_apply_Y, readY_regSlice_last, regResidualPack]
    congr 2
  -- The full decode triple (so `mulBlockPairCLE` / `decode.symm` see concrete pairs).
  have hdec : ∀ (r0 : Fin (deepestNReg H r) → ℝ),
      decodeRegSliceCLE H r hr r0 = (readY H r hr hL (r0, 0) (lastLayer hL),
        (readX H r hr hL (r0, 0) (firstLayer hL), readZ H r hr hL (r0, 0) (firstLayer hL))) := by
    intro r0
    rw [← hdX r0, ← hdY r0, ← hdZ r0]
    rfl
  -- The normal form: `deepestEPivot (r0,0) i = Fmap r0 i + quadE r0 i`. Per coordinate, case the pack;
  -- read `deepestEPivot`'s block (`hPread` + `hPdec` + the block-read lemmas) and `Fmap`'s block
  -- (`decodeRegSliceCLE_symm_apply` + `regBlockCLE_apply` + `mulBlockPairCLE_apply` + the decode reads).
  -- The three block matrix-identities of `P = reindex eR eJsucc prod`, read off `hPdec` (block-additive)
  -- + the read lemmas. `Bmat = reindex eJsucc eJsucc (Qf last)`, so `B22 = Bmat.toBlocks₂₂`,
  -- `B21 = Bmat.toBlocks₂₁`. The linear parts match `regBlockCLE`'s components; the residual is `quadM`.
  have hb11 : ∀ (r0 : Fin (deepestNReg H r) → ℝ),
      (Matrix.reindex eR eJsucc (prod H (framedParamsRegPivot H r hr hL J Pf Qf (r0, 0)))).toBlocks₁₁
        = 1 + (readY H r hr hL (r0, 0) (lastLayer hL) * Bmat.toBlocks₂₁
            + ((Matrix.reindex eR eR (Pf (firstLayer hL))).toBlocks₁₁
                * readX H r hr hL (r0, 0) (firstLayer hL)
              + (Matrix.reindex eR eR (Pf (firstLayer hL))).toBlocks₁₂
                * readZ H r hr hL (r0, 0) (firstLayer hL)))
          + (quadM r0).toBlocks₁₁ := by
    intro r0
    rw [hPdec r0, toBlocks₁₁_add, toBlocks₁₁_add, toBlocks₁₁_add, Matrix.toBlocks_fromBlocks₁₁,
      mulBlock_devXZ_toBlocks₁₁, pivot_devY_read_toBlocks₁₁, hBmat]
    abel
  have hb12 : ∀ (r0 : Fin (deepestNReg H r) → ℝ),
      (Matrix.reindex eR eJsucc (prod H (framedParamsRegPivot H r hr hL J Pf Qf (r0, 0)))).toBlocks₁₂
        = readY H r hr hL (r0, 0) (lastLayer hL) * Bmat.toBlocks₂₂ + (quadM r0).toBlocks₁₂ := by
    intro r0
    rw [hPdec r0, toBlocks₁₂_add, toBlocks₁₂_add, toBlocks₁₂_add, Matrix.toBlocks_fromBlocks₁₂,
      mulBlock_devXZ_toBlocks₁₂, pivot_devY_read_toBlocks₁₂, hBmat]
    abel
  have hb21 : ∀ (r0 : Fin (deepestNReg H r) → ℝ),
      (Matrix.reindex eR eJsucc (prod H (framedParamsRegPivot H r hr hL J Pf Qf (r0, 0)))).toBlocks₂₁
        = ((Matrix.reindex eR eR (Pf (firstLayer hL))).toBlocks₂₁
              * readX H r hr hL (r0, 0) (firstLayer hL)
            + (Matrix.reindex eR eR (Pf (firstLayer hL))).toBlocks₂₂
              * readZ H r hr hL (r0, 0) (firstLayer hL))
          + (quadM r0).toBlocks₂₁ := by
    intro r0
    rw [hPdec r0, toBlocks₂₁_add, toBlocks₂₁_add, toBlocks₂₁_add, Matrix.toBlocks_fromBlocks₂₁,
      mulBlock_devXZ_toBlocks₂₁, pivot_devY_read_toBlocks₂₁]
    abel
  have hNF : ∀ (r0 : Fin (deepestNReg H r) → ℝ) (i : Fin (deepestNReg H r)),
      deepestEPivot H r hr hL J Pf Qf (r0, 0) i = Fmap r0 i + quadE r0 i := by
    intro r0 i
    -- `Fmap r0 i = decode.symm (Fblk (decode r0)) i`.
    have hFm : Fmap r0 i = (decodeRegSliceCLE H r hr).symm
        (Fblk (decodeRegSliceCLE H r hr r0)) i := by rw [hFmap]; rfl
    rw [hFm, hdec r0]
    simp only [hFblk, regBlockCLE_apply, mulBlockPairCLE_apply]
    -- Reduce the `decode.symm` (encode read) on the `Fmap` side (`erw`: its `Z`-block type `H 0 − r`
    -- vs the `Fblk` `Z`-block `H (firstLayer hL).castSucc − r` are defeq), and unfold `deepestEPivot`'s
    -- match + align its reindex with `hbᵢⱼ`'s `reindex eR eJsucc` spelling (`hPread`).
    erw [decodeRegSliceCLE_symm_apply]
    simp only [deepestEPivot, hPread r0]
    rcases hcase : regResidualPack H r hr i with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
      simp only [hcase, hquadE]
    · erw [hb11 r0]; simp only [Matrix.add_apply, Matrix.sub_apply]; ring
    · erw [hb12 r0]; simp only [Matrix.add_apply]
    · erw [hb21 r0]; simp only [Matrix.add_apply]
  -- The function equality `(fun r0 => deepestEPivot (r0,0)) = fun r0 => Fmap r0 + quadE r0`.
  have hfun : (fun r0 : Fin (deepestNReg H r) → ℝ => deepestEPivot H r hr hL J Pf Qf (r0, 0))
      = fun r0 => (Fmap r0 : Fin (deepestNReg H r) → ℝ) + quadE r0 := by
    funext r0; funext i; rw [hNF r0 i]; rfl
  -- The quadratic residual has strict derivative `0` at `0` (each coordinate is a sum of products of two
  -- `r0`-linear factors vanishing at `0`; `hasStrictFDerivAt_sum_mul_zero` per coord + `hasStrictFDerivAt_pi'`).
  have hquadderiv : HasStrictFDerivAt quadE (0 : (Fin (deepestNReg H r) → ℝ) →L[ℝ]
      (Fin (deepestNReg H r) → ℝ)) 0 := by
    -- The decode blocks have strict derivatives (CLE) and vanish at 0; each read entry is a coordinate of
    -- a decode block, hence a continuous-linear functional of r0 vanishing at 0. `quadM`'s entries are
    -- sums of products of two such (the `X·Y`/`Z·Y` cross), so each `quadE` coord has strict deriv 0.
    -- The decode blocks (X = `.2.1`, Y = `.1`, Z = `.2.2`) are CLE-components of `r0`: strict deriv + 0.
    set Dfst := ContinuousLinearMap.fst ℝ (Matrix (Fin r) (Fin r) ℝ)
      (Matrix (Fin (H 0 - r)) (Fin r) ℝ) with hDfst
    set Dsnd := ContinuousLinearMap.snd ℝ (Matrix (Fin r) (Fin (H (Fin.last (n + 1 + 1)) - r)) ℝ)
      (Matrix (Fin r) (Fin r) ℝ × Matrix (Fin (H 0 - r)) (Fin r) ℝ) with hDsnd
    set Dc := (decodeRegSliceCLE H r hr).toContinuousLinearMap with hDc
    have heqX : (fun r0 : Fin (deepestNReg H r) → ℝ => readX H r hr hL (r0, 0) (firstLayer hL))
        = ⇑((Dfst.comp Dsnd).comp Dc) := by funext y; rw [← hdX y]; rfl
    have heqY : (fun r0 : Fin (deepestNReg H r) → ℝ => readY H r hr hL (r0, 0) (lastLayer hL))
        = ⇑((ContinuousLinearMap.fst ℝ (Matrix (Fin r) (Fin (H (Fin.last (n + 1 + 1)) - r)) ℝ)
            (Matrix (Fin r) (Fin r) ℝ × Matrix (Fin (H 0 - r)) (Fin r) ℝ)).comp Dc) := by
      funext y; rw [← hdY y]; rfl
    have heqZ : (fun r0 : Fin (deepestNReg H r) → ℝ => readZ H r hr hL (r0, 0) (firstLayer hL))
        = ⇑((ContinuousLinearMap.snd ℝ (Matrix (Fin r) (Fin r) ℝ)
            (Matrix (Fin (H 0 - r)) (Fin r) ℝ)).comp (Dsnd.comp Dc)) := by
      funext y; rw [← hdZ y]; rfl
    have hXsd : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
          readX H r hr hL (r0, 0) (firstLayer hL)) ((Dfst.comp Dsnd).comp Dc) 0 := by
      rw [heqX]; exact ((Dfst.comp Dsnd).comp Dc).hasStrictFDerivAt
    have hYsd : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
          readY H r hr hL (r0, 0) (lastLayer hL))
        ((ContinuousLinearMap.fst ℝ (Matrix (Fin r) (Fin (H (Fin.last (n + 1 + 1)) - r)) ℝ)
            (Matrix (Fin r) (Fin r) ℝ × Matrix (Fin (H 0 - r)) (Fin r) ℝ)).comp Dc) 0 := by
      rw [heqY]
      exact ((ContinuousLinearMap.fst ℝ (Matrix (Fin r) (Fin (H (Fin.last (n + 1 + 1)) - r)) ℝ)
        (Matrix (Fin r) (Fin r) ℝ × Matrix (Fin (H 0 - r)) (Fin r) ℝ)).comp Dc).hasStrictFDerivAt
    have hZsd : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
          readZ H r hr hL (r0, 0) (firstLayer hL))
        ((ContinuousLinearMap.snd ℝ (Matrix (Fin r) (Fin r) ℝ) (Matrix (Fin (H 0 - r)) (Fin r) ℝ)).comp
          (Dsnd.comp Dc)) 0 := by
      rw [heqZ]
      exact ((ContinuousLinearMap.snd ℝ (Matrix (Fin r) (Fin r) ℝ)
        (Matrix (Fin (H 0 - r)) (Fin r) ℝ)).comp (Dsnd.comp Dc)).hasStrictFDerivAt
    have hdec0 : decodeRegSliceCLE H r hr 0 = 0 := map_zero _
    have hX0 : readX H r hr hL ((0 : Fin (deepestNReg H r) → ℝ), 0) (firstLayer hL) = 0 := by
      rw [← hdX 0, hdec0]; rfl
    have hY0 : readY H r hr hL ((0 : Fin (deepestNReg H r) → ℝ), 0) (lastLayer hL) = 0 := by
      rw [← hdY 0, hdec0]; rfl
    have hZ0 : readZ H r hr hL ((0 : Fin (deepestNReg H r) → ℝ), 0) (firstLayer hL) = 0 := by
      rw [← hdZ 0, hdec0]; rfl
    -- Each read ENTRY (scalar) has a strict derivative (the matrix-valued read deriv post-composed with
    -- the entry-projection CLM) and vanishes at 0. Stated via the function-equality `readX·entry = ⇑(CLM)`.
    have hXe : ∀ (p q : Fin r), ∃ φ : (Fin (deepestNReg H r) → ℝ) →L[ℝ] ℝ,
        HasStrictFDerivAt (fun r0 => readX H r hr hL (r0, 0) (firstLayer hL) p q) φ 0 := by
      intro p q
      refine ⟨((Matrix.entryLinearMap ℝ ℝ p q : Matrix (Fin r) (Fin r) ℝ →ₗ[ℝ] ℝ
          ).toContinuousLinearMap).comp ((Dfst.comp Dsnd).comp Dc), ?_⟩
      have : (fun r0 => readX H r hr hL (r0, 0) (firstLayer hL) p q)
          = ⇑(((Matrix.entryLinearMap ℝ ℝ p q : Matrix (Fin r) (Fin r) ℝ →ₗ[ℝ] ℝ
            ).toContinuousLinearMap).comp ((Dfst.comp Dsnd).comp Dc)) := by
        funext y
        exact congrArg (fun M => M p q) (congrFun heqX y)
      rw [this]; exact ContinuousLinearMap.hasStrictFDerivAt _
    have hYe : ∀ (p : Fin r) (q : Fin (H (Fin.last (n + 1 + 1)) - r)),
        ∃ φ : (Fin (deepestNReg H r) → ℝ) →L[ℝ] ℝ,
        HasStrictFDerivAt (fun r0 => readY H r hr hL (r0, 0) (lastLayer hL) p q) φ 0 := by
      intro p q
      refine ⟨((Matrix.entryLinearMap ℝ ℝ p q :
          Matrix (Fin r) (Fin (H (Fin.last (n + 1 + 1)) - r)) ℝ →ₗ[ℝ] ℝ).toContinuousLinearMap).comp
          ((ContinuousLinearMap.fst ℝ (Matrix (Fin r) (Fin (H (Fin.last (n + 1 + 1)) - r)) ℝ)
            (Matrix (Fin r) (Fin r) ℝ × Matrix (Fin (H 0 - r)) (Fin r) ℝ)).comp Dc), ?_⟩
      have : (fun r0 => readY H r hr hL (r0, 0) (lastLayer hL) p q)
          = ⇑(((Matrix.entryLinearMap ℝ ℝ p q :
            Matrix (Fin r) (Fin (H (Fin.last (n + 1 + 1)) - r)) ℝ →ₗ[ℝ] ℝ).toContinuousLinearMap).comp
          ((ContinuousLinearMap.fst ℝ (Matrix (Fin r) (Fin (H (Fin.last (n + 1 + 1)) - r)) ℝ)
            (Matrix (Fin r) (Fin r) ℝ × Matrix (Fin (H 0 - r)) (Fin r) ℝ)).comp Dc)) := by
        funext y
        exact congrArg (fun M => M p q) (congrFun heqY y)
      rw [this]; exact ContinuousLinearMap.hasStrictFDerivAt _
    have hZe : ∀ (p : Fin (H 0 - r)) (q : Fin r), ∃ φ : (Fin (deepestNReg H r) → ℝ) →L[ℝ] ℝ,
        HasStrictFDerivAt (fun r0 => readZ H r hr hL (r0, 0) (firstLayer hL) p q) φ 0 := by
      intro p q
      refine ⟨((Matrix.entryLinearMap ℝ ℝ p q : Matrix (Fin (H 0 - r)) (Fin r) ℝ →ₗ[ℝ] ℝ
          ).toContinuousLinearMap).comp
          ((ContinuousLinearMap.snd ℝ (Matrix (Fin r) (Fin r) ℝ) (Matrix (Fin (H 0 - r)) (Fin r) ℝ)).comp
            (Dsnd.comp Dc)), ?_⟩
      have : (fun r0 => readZ H r hr hL (r0, 0) (firstLayer hL) p q)
          = ⇑(((Matrix.entryLinearMap ℝ ℝ p q : Matrix (Fin (H 0 - r)) (Fin r) ℝ →ₗ[ℝ] ℝ
            ).toContinuousLinearMap).comp
          ((ContinuousLinearMap.snd ℝ (Matrix (Fin r) (Fin r) ℝ)
            (Matrix (Fin (H 0 - r)) (Fin r) ℝ)).comp (Dsnd.comp Dc))) := by
        funext y
        exact congrArg (fun M => M p q) (congrFun heqZ y)
      rw [this]; exact ContinuousLinearMap.hasStrictFDerivAt _
    -- Each matrix-product ENTRY `(X·Y) p q = ∑_k X p k · Y k q` is a sum of products of two read entries,
    -- each vanishing-linear, so it has strict derivative 0 at 0 (`hasStrictFDerivAt_sum_mul_zero`).
    have hXYe : ∀ (p : Fin r) (q : Fin (H (Fin.last (n + 1 + 1)) - r)),
        HasStrictFDerivAt (fun r0 => (readX H r hr hL (r0, 0) (firstLayer hL)
          * readY H r hr hL (r0, 0) (lastLayer hL)) p q) (0 : _ →L[ℝ] ℝ) 0 := by
      intro p q
      have hsum := hasStrictFDerivAt_sum_mul_zero
        (fun k r0 => readX H r hr hL (r0, 0) (firstLayer hL) p k)
        (fun k r0 => readY H r hr hL (r0, 0) (lastLayer hL) k q)
        (fun k => (hXe p k).choose) (fun k => (hYe k q).choose)
        (fun k => (hXe p k).choose_spec) (fun k => (hYe k q).choose_spec)
        (fun k => by show readX H r hr hL ((0 : Fin (deepestNReg H r) → ℝ), 0) (firstLayer hL) p k = 0; rw [hX0]; rfl)
        (fun k => by show readY H r hr hL ((0 : Fin (deepestNReg H r) → ℝ), 0) (lastLayer hL) k q = 0; rw [hY0]; rfl)
      have heq : (fun r0 : Fin (deepestNReg H r) → ℝ => (readX H r hr hL (r0, 0) (firstLayer hL)
          * readY H r hr hL (r0, 0) (lastLayer hL)) p q)
          = fun r0 => ∑ k, readX H r hr hL (r0, 0) (firstLayer hL) p k
              * readY H r hr hL (r0, 0) (lastLayer hL) k q := by
        funext r0; rw [Matrix.mul_apply]
      rw [heq]; exact hsum
    have hZYe : ∀ (p : Fin (H 0 - r)) (q : Fin (H (Fin.last (n + 1 + 1)) - r)),
        HasStrictFDerivAt (fun r0 => (readZ H r hr hL (r0, 0) (firstLayer hL)
          * readY H r hr hL (r0, 0) (lastLayer hL)) p q) (0 : _ →L[ℝ] ℝ) 0 := by
      intro p q
      have hsum := hasStrictFDerivAt_sum_mul_zero
        (fun k r0 => readZ H r hr hL (r0, 0) (firstLayer hL) p k)
        (fun k r0 => readY H r hr hL (r0, 0) (lastLayer hL) k q)
        (fun k => (hZe p k).choose) (fun k => (hYe k q).choose)
        (fun k => (hZe p k).choose_spec) (fun k => (hYe k q).choose_spec)
        (fun k => by show readZ H r hr hL ((0 : Fin (deepestNReg H r) → ℝ), 0) (firstLayer hL) p k = 0; rw [hZ0]; rfl)
        (fun k => by show readY H r hr hL ((0 : Fin (deepestNReg H r) → ℝ), 0) (lastLayer hL) k q = 0; rw [hY0]; rfl)
      have heq : (fun r0 : Fin (deepestNReg H r) → ℝ => (readZ H r hr hL (r0, 0) (firstLayer hL)
          * readY H r hr hL (r0, 0) (lastLayer hL)) p q)
          = fun r0 => ∑ k, readZ H r hr hL (r0, 0) (firstLayer hL) p k
              * readY H r hr hL (r0, 0) (lastLayer hL) k q := by
        funext r0; rw [Matrix.mul_apply]
      rw [heq]; exact hsum
    -- The dev-block `fromBlocks 0 (X·Y) 0 (Z·Y)` ENTRY has strict deriv 0 (each block entry is `(X·Y)`/
    -- `(Z·Y)` or `0`, all deriv 0).
    have hdevb : ∀ (s : Fin r ⊕ Fin (H 0 - r)) (t : Fin r ⊕ Fin (H (Fin.last (n + 1 + 1)) - r)),
        HasStrictFDerivAt (fun r0 => Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) ℝ)
            (readX H r hr hL (r0, 0) (firstLayer hL) * readY H r hr hL (r0, 0) (lastLayer hL))
            (0 : Matrix (Fin (H 0 - r)) (Fin r) ℝ)
            (readZ H r hr hL (r0, 0) (firstLayer hL) * readY H r hr hL (r0, 0) (lastLayer hL)) s t)
          (0 : _ →L[ℝ] ℝ) 0 := by
      rintro (s | s) (t | t)
      · exact hasStrictFDerivAt_const 0 0
      · exact hXYe s t
      · exact hasStrictFDerivAt_const 0 0
      · exact hZYe s t
    -- The `D(r0)` (reindexed dev-block) entry has strict deriv 0 (it IS a dev-block entry).
    have hDentry : ∀ (s t), HasStrictFDerivAt (fun r0 => Matrix.reindex eR.symm eJsucc.symm
        (Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) ℝ)
          (readX H r hr hL (r0, 0) (firstLayer hL) * readY H r hr hL (r0, 0) (lastLayer hL))
          (0 : Matrix (Fin (H 0 - r)) (Fin r) ℝ)
          (readZ H r hr hL (r0, 0) (firstLayer hL) * readY H r hr hL (r0, 0) (lastLayer hL))) s t)
        (0 : _ →L[ℝ] ℝ) 0 := by
      intro s t
      have heq : (fun r0 => Matrix.reindex eR.symm eJsucc.symm
          (Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) ℝ)
            (readX H r hr hL (r0, 0) (firstLayer hL) * readY H r hr hL (r0, 0) (lastLayer hL))
            (0 : Matrix (Fin (H 0 - r)) (Fin r) ℝ)
            (readZ H r hr hL (r0, 0) (firstLayer hL) * readY H r hr hL (r0, 0) (lastLayer hL))) s t)
          = fun r0 => Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) ℝ)
            (readX H r hr hL (r0, 0) (firstLayer hL) * readY H r hr hL (r0, 0) (lastLayer hL))
            (0 : Matrix (Fin (H 0 - r)) (Fin r) ℝ)
            (readZ H r hr hL (r0, 0) (firstLayer hL) * readY H r hr hL (r0, 0) (lastLayer hL))
            (eR s) (eJsucc t) := by
        funext r0; rfl
      rw [heq]; exact hdevb (eR s) (eJsucc t)
    -- `quadM r0 s t = (Pf · D(r0) · Qf) (eR.symm s)(eJsucc.symm t)` = a finite sum (Leibniz) of
    -- `const · D-entry · const`, each deriv 0; the sum has deriv 0.
    have hquadM_entry : ∀ (s t), HasStrictFDerivAt (fun r0 => quadM r0 s t) (0 : _ →L[ℝ] ℝ) 0 := by
      intro s t
      have heq : (fun r0 : Fin (deepestNReg H r) → ℝ => quadM r0 s t)
          = fun r0 => ∑ l, ∑ k, Pf (firstLayer hL) (eR.symm s) k
              * Matrix.reindex eR.symm eJsucc.symm
                  (Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) ℝ)
                    (readX H r hr hL (r0, 0) (firstLayer hL) * readY H r hr hL (r0, 0) (lastLayer hL))
                    (0 : Matrix (Fin (H 0 - r)) (Fin r) ℝ)
                    (readZ H r hr hL (r0, 0) (firstLayer hL) * readY H r hr hL (r0, 0) (lastLayer hL)))
                  k l
              * Qf (lastLayer hL) l (eJsucc.symm t) := by
        funext r0
        rw [hquadM]
        simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [Matrix.mul_apply, Finset.sum_mul]
        rfl
      rw [heq]
      have hfull : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
          ∑ l, ∑ k, Pf (firstLayer hL) (eR.symm s) k
              * Matrix.reindex eR.symm eJsucc.symm
                  (Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) ℝ)
                    (readX H r hr hL (r0, 0) (firstLayer hL) * readY H r hr hL (r0, 0) (lastLayer hL))
                    (0 : Matrix (Fin (H 0 - r)) (Fin r) ℝ)
                    (readZ H r hr hL (r0, 0) (firstLayer hL) * readY H r hr hL (r0, 0) (lastLayer hL)))
                  k l
              * Qf (lastLayer hL) l (eJsucc.symm t))
          (∑ _l : Fin (H ((lastLayer hL).succ)), ∑ _k : Fin (H ((firstLayer hL).castSucc)),
            (0 : (Fin (deepestNReg H r) → ℝ) →L[ℝ] ℝ)) 0 := by
        refine HasStrictFDerivAt.fun_sum (fun l _ => HasStrictFDerivAt.fun_sum (fun k _ => ?_))
        have := ((hDentry k l).const_mul (Pf (firstLayer hL) (eR.symm s) k)).mul_const
          (Qf (lastLayer hL) l (eJsucc.symm t))
        simpa using this
      simpa using hfull
    refine hasStrictFDerivAt_pi'.2 (fun i => ?_)
    rcases hcase : regResidualPack H r hr i with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
      simp only [hquadE, hcase, ContinuousLinearMap.zero_comp]
    · exact hquadM_entry _ _
    · exact hquadM_entry _ _
    · exact hquadM_entry _ _
  -- `Fmap` is a CLE, so it has strict derivative `↑Fmap`; add the quad (deriv 0), `+ 0`.
  have hFderiv : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ => Fmap r0)
      (Fmap : (Fin (deepestNReg H r) → ℝ) →L[ℝ] (Fin (deepestNReg H r) → ℝ)) 0 :=
    Fmap.hasStrictFDerivAt
  rw [hfun]
  simpa using hFderiv.add hquadderiv

/-- **`deepestEPivot`'s derivative at `0` is the invertible SHEAR** (#120-corrected: NOT `fst`). By #91
(`d(P−B)|_0 = (Σ_s X_s, Y_L, Z_1)`, idempotent sandwich), the reg-residual's derivative reads the
reg-X + sums the gauge-X's into reg while keeping the gauge free — the unitriangular shear
`D_E = [[I, Σ],[0, I]]` on `reg×gauge → reg` (its total `regStraightenTotalCLM D_E` is `[[I,Σ],[0,I]]`
on `DeepestSplit`, det 1, invertible). Bundled: `∃ D_E (e : ≃L), HasStrictFDerivAt deepestEPivot D_E 0
∧ (e : →L) = regStraightenTotalCLM D_E`. ASSEMBLED from `_contdiff` (→ `D_E := fderiv`), the reg-block
identity `deepestEPivot_regSlice_fderiv_id` (the #91 crux), and the generic shear-CLE
`regStraightenTotalCLM_equiv_of_regBlock_id`. -/
theorem deepestEPivot_deriv (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂)) :
    ∃ (D_E : ((Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) →L[ℝ]
        (Fin (deepestNReg H r) → ℝ))
      (e : DeepestSplit H r (deepestNGauge H r) ≃L[ℝ] DeepestSplit H r (deepestNGauge H r)),
      HasStrictFDerivAt (deepestEPivot H r hr hL J Pf Qf) D_E 0 ∧
      (e : DeepestSplit H r (deepestNGauge H r) →L[ℝ] DeepestSplit H r (deepestNGauge H r))
        = regStraightenTotalCLM D_E := by
  -- `D_E := fderiv ℝ deepestEPivot 0` (free from `_contdiff`); its reg-block is the INVERTIBLE frame
  -- factor `F` (the #91 post-frame fact), so `regStraightenTotalCLM D_E` is the invertible shear
  -- (`regStraightenTotalCLM_equiv_of_regBlock_isUnit`).
  set D_E := fderiv ℝ (deepestEPivot H r hr hL J Pf Qf) 0 with hD_E
  have hsd : HasStrictFDerivAt (deepestEPivot H r hr hL J Pf Qf) D_E 0 :=
    (deepestEPivot_contdiff H r hr hL J Pf Qf).hasStrictFDerivAt (by simp)
  -- The reg-block: `D_E.comp regInCLM = ↑F`. The reg-slice `r ↦ deepestEPivot (r,0)` has strict
  -- derivative `D_E.comp regInCLM` (chain rule) AND `↑F` (#91 frame factor), so they agree.
  obtain ⟨F, hF⟩ := deepestEPivot_regSlice_fderiv H r hr hL hL2 J Pf Qf hPf hQf hQf0 hPfL hQf22
  have hregIn : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ => ((r0, 0) :
      (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)))
      (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ]
        (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) 0 := by
    have := (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ]
      (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)).hasStrictFDerivAt (x := 0)
    simpa [regInCLM] using this
  have hcomp : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
      deepestEPivot H r hr hL J Pf Qf (r0, 0)) (D_E.comp regInCLM) 0 := by
    have hsd0 : HasStrictFDerivAt (deepestEPivot H r hr hL J Pf Qf) D_E
        (((0 : Fin (deepestNReg H r) → ℝ), (0 : Fin (deepestNGauge H r) → ℝ))) := hsd
    exact hsd0.comp (x := (0 : Fin (deepestNReg H r) → ℝ)) hregIn
  -- `D_E.comp regInCLM = ↑F` (fderiv uniqueness against `hF`).
  have hblock : D_E.comp (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ]
      (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
      = (F : (Fin (deepestNReg H r) → ℝ) →L[ℝ] (Fin (deepestNReg H r) → ℝ)) := by
    have h1 := hcomp.hasFDerivAt.fderiv
    have h2 := hF.hasFDerivAt.fderiv
    rw [← h1, ← h2]
  obtain ⟨e, he⟩ := regStraightenTotalCLM_equiv_of_regBlock_isUnit
    (C := Fin (flatDim (deepestM H r)) → ℝ) D_E F hblock.symm
  exact ⟨D_E, e, hsd, he⟩

theorem deepestEPivot_base (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
    deepestEPivot H r hr hL J Pf Qf 0 = 0 := by
  -- At the origin slot, `∏(framedParamsRegPivot 0)` reindexed by the pivot outer split is the corner
  -- `fromBlocks 1 0 0 0` (banked `reindex_prodAux_framedParamsRegPivot_zero`).
  funext i
  -- The matrix `P` defining the coordinates is the pivot-reindexed corner.
  have hP : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (prod H (framedParamsRegPivot H r hr hL J Pf Qf 0)))
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 :=
    reindex_prodAux_framedParamsRegPivot_zero H r hr hL hL2 J Pf Qf
  -- Each coordinate reads a block of `P`; all blocks of `fromBlocks 1 0 0 0` give `0` in the residual.
  simp only [deepestEPivot, hP, Pi.zero_apply]
  rcases regResidualPack H r hr i with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
    simp only [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.sub_apply,
      Matrix.of_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, sub_self]

/-- **The reg-residual energy IS the block energy** (the #80 Φ-reg identification, BLOCK-LEVEL). The sum
of squares of `deepestEPivot p` over `Fin nReg` equals the three residual-block energies of
`P = reindex(prod(framedParamsReg p))` — `∑(P11−1)² + ∑P12² + ∑P21²`. Via `regResidualPack` as a SUMMING
bijection (`Equiv.sum_comp`) + `Fintype.sum_sum_type`/`Fintype.sum_prod_type`: NO per-coordinate value of
`regResidualPack` is used (only its bijectivity), so this is STABLE under the #120 value-changing swap
(`regResidualPack := regPivotFinEquiv`) — the sum is the same for any bijection of the same type. -/
theorem deepestEPivot_sq_sum_eq_blocks (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) :
    (∑ i, (deepestEPivot H r hr hL J Pf Qf p i) ^ 2)
      = (∑ a, ∑ b, (((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (prod H (framedParamsRegPivot H r hr hL J Pf Qf p))).toBlocks₁₁ - 1) a b) ^ 2)
        + ((∑ a, ∑ b, ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (prod H (framedParamsRegPivot H r hr hL J Pf Qf p))).toBlocks₁₂ a b) ^ 2)
          + (∑ a, ∑ b, ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (prod H (framedParamsRegPivot H r hr hL J Pf Qf p))).toBlocks₂₁ a b) ^ 2)) := by
  -- Reindex the `Fin nReg` sum along `regResidualPack` (a bijection — value-irrelevant), then split the
  -- NESTED sum-type `blk1 ⊕ (blk2 ⊕ blk3)` (`Fintype.sum_sum_type` twice + `Fintype.sum_prod_type`).
  rw [← Equiv.sum_comp (regResidualPack H r hr).symm
      (fun i => (deepestEPivot H r hr hL J Pf Qf p i) ^ 2),
    Fintype.sum_sum_type]
  congr 1
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    simp only [deepestEPivot, Equiv.apply_symm_apply]
  · rw [Fintype.sum_sum_type]
    congr 1 <;>
      (rw [Fintype.sum_prod_type]
       refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
       simp only [deepestEPivot, Equiv.apply_symm_apply])

/-- **The frame-bridge cert** (#80, ruling (b) — the ONE geometric input of the loss squeeze). Packages
the constant endpoint frames `P0, QL` (with inverses `Pi, Qi`, `Pi·P0 = 1 ∧ QL·Qi = 1`) and a `leak`
charge constant `t`, and a neighborhood `U` of the deepest point where for each `w ∈ U` the loss matrix
`N = ∏(paramsSymm w) − B`, conjugated by the endpoint frames and reindexed to `r ⊕ M` block shape, is
the framed-block form `fromBlocks (P00−1) P01 P10 P11`, with the regular blocks `(P00, P01, P10)` IDENTIFIED
with the `framedParamsReg` product blocks `Preg = reindex(∏(framedParamsReg (split w).reg, (split w).spec))`
(the `deepestEPivot` source), the Schur leak charged `∑leak² ≤ t²·∑E²`, and the CORE COMPARABILITY
`∑(P11 − P10⅟P00 P01)² ≍ deepestCoreF (coreAbsorb (split w)).2.1` (TWO-SIDED, not an equality: the
full-product Schur core leaks into the regular blocks — g156 — so it agrees with the absorbed per-layer
core only modulo regular leakage, folded into `c₁/c₂`; the RLCT value stays exact).

This is cobuild's OWN cert (a DIFFERENT object from deriv-fm's #120 reg-slice-of-`deepestEPivot`): it
is built on `split`/`deepestRoleIndexEquiv` + the core + the gauge, via `endpoint_telescoping`
(`deepestPoint_frame` boundary frames + interior-interface vanishing) and the `framedParams`/`framedParamsReg`
identification.

**STATEMENT STRENGTHENED (L2-PIN2, 2026-06-25):** the cert now takes `hsplit : ∀ w, split w =
deepestSplit … w` (the concrete reindex witness, `DeepestSplitConcrete`). Without it the conclusion is
NOT derivable — the block `P00/P01/P10` are read off `framedParamsRegPivot (split w)`, whose tie to
`paramsEquivFlat.symm w` runs through the round-trip `readX/Y/Z (split w) = raw-deviation block`, which
is provable ONLY for the concrete `deepestSplit` (the index-decode lemmas are stated against it). For a
generic homeomorphism `split` the statement is unprovable (under-hypothesized). The caller
`deepest_gauge_construction` now supplies the concrete `deepestSplit`, so `hsplit := fun _ => rfl`.

**Isolated `sorry` (route-first):** the cert is the g164 boundary-frame extraction + the split-reg-half
structured-equiv (the `regBoundaryEmbed` technique). The remaining geometry (with `hsplit` in hand) is
the readX/Y/Z→raw block-decode (3 arms) + the entry-wise `reindex(fromBlocks readX readY readZ Tcore) =
(paramsEquivFlat.symm w − deepestPoint)_s` + `framedLayer = P_s·(paramsSymm w)_s·Q_s`
(`deepestPoint_frame_normal`) + `endpoint_telescoping` + the J-dependent `reindex(P0·B·QL) = fromBlocks
1 0 0 0` (`exists_deepest_lastLayer_pivotFrame`) + `core_comparability_squeeze` — ~200-300 LoC of glue
(Codex `xhigh` decorrelated, 2026-06-25), beyond a single-leaf tide. -/
theorem framedParams_split_eq_frame_raw (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w) :
    ∃ (P0 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
      (QL : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ)
      (Pi : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
      (Qi : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ)
      (t γ₁ γ₂ : ℝ),
      Pi * P0 = 1 ∧ QL * Qi = 1 ∧ 0 < γ₁ ∧ 0 < γ₂ ∧
      0 < (∑ i, ∑ k, (P0 i k) ^ 2) * (∑ j, ∑ k, (QL k j) ^ 2) ∧
      0 < (∑ i, ∑ k, (Pi i k) ^ 2) * (∑ j, ∑ k, (Qi k j) ^ 2) ∧
      ∃ U ∈ 𝓝 ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
        ∀ w ∈ U,
          ∃ (P00 : Matrix (Fin r) (Fin r) ℝ)
            (P01 : Matrix (Fin r) (Fin (H (Fin.last L) - r)) ℝ)
            (P10 : Matrix (Fin (H 0 - r)) (Fin r) ℝ)
            (P11 : Matrix (Fin (H 0 - r)) (Fin (H (Fin.last L) - r)) ℝ)
            (_hP00 : Invertible P00),
            letI : Invertible P00 := _hP00
            (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)
              = Matrix.fromBlocks (P00 - 1) P01 P10 P11)
            ∧ (P00 = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (prod H (framedParamsRegPivot H r hr hL J Pf Qf ((split w).1, (split w).2.2)))).toBlocks₁₁)
            ∧ (P01 = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (prod H (framedParamsRegPivot H r hr hL J Pf Qf ((split w).1, (split w).2.2)))).toBlocks₁₂)
            ∧ (P10 = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (prod H (framedParamsRegPivot H r hr hL J Pf Qf ((split w).1, (split w).2.2)))).toBlocks₂₁)
            ∧ ((∑ i, ∑ j, ((P10 * ⅟P00 * P01) i j) ^ 2)
                ≤ t ^ 2 * (((∑ i, ∑ j, ((P00 - 1) i j) ^ 2) + (∑ i, ∑ j, (P01 i j) ^ 2))
                    + (∑ i, ∑ j, (P10 i j) ^ 2)))
            ∧ ((∑ i, ∑ j, ((P11 - P10 * ⅟P00 * P01) i j) ^ 2)
                ≤ γ₂ * deepestCoreF H r (deepestCoreAbsorb H r hr hL (split w)).2.1)
            ∧ (deepestCoreF H r (deepestCoreAbsorb H r hr hL (split w)).2.1
                ≤ γ₁ * (∑ i, ∑ j, ((P11 - P10 * ⅟P00 * P01) i j) ^ 2)) := by
  -- FRAME-WIRING DONE (the design call, implemented): `framedLayer` now reconstructs the raw layer
  -- `reindex(fromBlocks X Y Z T)` and frame-conjugates it `P_s · raw · Q_s` (added to the corM base),
  -- so `framedParamsReg`'s blocks (here instantiated with `deepestPoint_frame`) are the FRAME-CONJUGATED
  -- product's regular blocks — matching `reindex(P0·N·QL)`'s telescoped form. `split` stays frameless/MP.
  --
  -- REMAINING (the genuine geometric content): close this cert via
  --   (1) the round-trip `framedParams(split w) s = P_s · (paramsSymm w)_s · Q_s` — needs
  --       `readX/Y/Z (split w)` = the raw-deviation block of `(paramsSymm w − deepestPoint)_s` (the
  --       `regGaugeSlotEquiv ∘ regGaugeIdxSplit ∘ roleSplitIdx ∘ paramsEquivFlat` cancellation through
  --       `subRight deepestFlat`) + `deepestPoint_frame_normal` (`P·deepestPoint·Q = corM`);
  --   (2) `endpoint_telescoping` on `deepestPoint_frame` (interior interfaces vanish) →
  --       `prod(framedParams(split w)) = P0 · prod(paramsSymm w) · QL`;
  --   (3) `reindex(P0·B·QL) = fromBlocks 1 0 0 0` (B gauge-normalised at rank r) ⟹ the `fromBlocks
  --       (P00−1) P01 P10 P11` shape; (4) `core_comparability_squeeze` (#54) for the core comparability.
  --
  -- UNBLOCKED by the refined frame (prior tide): step (2)'s `endpoint_telescoping` `hinterface` is now
  -- dischargeable at `2 ≤ L` — interior frames `= 1` (`deepestPoint_interior_frame_id`), boundary-inner
  -- `Qf first = 1` / `Pf last = 1` (`deepestPoint_frame_Qf/Pf_eq_one`), so all adjacent interfaces
  -- `Q_s = 1 ∧ P_{s+1} = 1` collapse.
  --
  -- ENUMERATION MISMATCH FIXED (this tide, 2026-06-24, Codex `xhigh` decorrelated): `deepestRoleIndexEquiv`
  -- now routes its reg/gauge half through `regGaugeIdxSplit` (was the OPAQUE `Fintype.equivFin`), the SAME
  -- explicit split `regGaugeSlotEquiv` un-flattens through (`DeepestSplitReindex`). So the step-(1)
  -- round-trip `readX/Y/Z (deepestSplit w) = raw-deviation block of (w − flatDeepest)` is now
  -- DEFINITIONALLY reachable (the two enumerations cancel; before, with `Fintype.equivFin`, that
  -- cancellation was not definitional and the round-trip could not be proved). The whole downstream chain
  -- (incl. `deepestSplit_exists`) still builds green after the swap.
  --
  -- BANKED sorry-free (this tide, 2026-06-24): the round-trip INDEX HALF (`DeepestSplitConcrete`) PLUS
  -- the two J-INDEPENDENT step-(1) atoms (`DeepestFrameRaw`, axiom-clean `[propext, Classical.choice,
  -- Quot.sound]`, NO sorryAx — these were the highest-risk index/cast lemmas):
  --   • `deepestSplit` + `deepestSplit_mp_basepoint`; `regGaugeSlotEquiv_deepestSplit`;
  --     `readX/Y/Z_deepestSplit` (the X/Y/Z-arm index round-trip).
  --   • `deepestRoleIndexEquiv_symm_recombine` (the index identity, generic over `a : RegGaugeIdx`):
  --       `deepestRoleIndexEquiv.symm (regGaugeRecombine (regGaugeIdxSplit a))
  --        = Fintype.equivFin (FlatIdx H) (roleSplitIdx.symm (Sum.inl a))` — the two `regGaugeIdxSplit`
  --       enumerations cancel; the core `Fintype.equivFin (FlatIdx M)` never appears (recombine image is
  --       the reg/gauge summand only). Proof: `Equiv.symm_apply_eq` + `conv_rhs => erw [trans_apply …]`
  --       (the keyed `rw`/`simp` matcher MISSES the EquivLike-coercion form at v4.29 — `erw` is required)
  --       + per-arm `sumCongr`/`sumAssoc`/`sumComm`-apply.
  --   • `paramsEquivFlat_apply_equivFin`: `paramsEquivFlat H A (Fintype.equivFin (FlatIdx H) idx)
  --       = A idx.1.1 idx.1.2 idx.2` (the `arrowCongr'`/`piCurry`/`Sigma.uncurry` decode).
  --   • `rThresholdSplit_symm_inl/inr`: the per-vertex threshold-split inverse (`castLE` / `r + ·`),
  --       the cast atom for the `roleSplitIdx.symm` block-position decode (probed tractable via `Fin.ext`).
  --
  -- SUB-BLOCKER (precise; remaining content). The J-INDEPENDENT readX/Y/Z → raw-entry chain is now
  -- mechanically reachable from the banked atoms: `readX_deepestSplit` ▸ `deepestRoleIndexEquiv_symm_recombine`
  -- ▸ `(w − wstar) f = w f − wstar f` ▸ (`w f = paramsEquivFlat (paramsEquivFlat.symm w) f`)
  -- `paramsEquivFlat_apply_equivFin` — leaving the `roleSplitIdx.symm (inl ⟨s, X/Y/Z-arm⟩)` block-position
  -- decode (a sigma-trans `.symm` chase through `layerEntrySplit`/`rThresholdSplit_symm_*`, ~30–50 lines/arm,
  -- probed convergent), then the entry-wise `reindex(fromBlocks readX readY readZ Tcore) =
  -- (paramsEquivFlat.symm w − deepestPoint) s` (`Matrix.ext` + 4-way `rThresholdSplit` split; T-arm via the
  -- core-half decode), then `framedLayer (frame) … = P_s·(paramsEquivFlat.symm w)_s·Q_s` via
  -- `deepestPoint_frame_normal` + additive split, then `endpoint_telescoping` (interfaces collapse at 2≤L —
  -- `deepestPoint_interior_frame_id` / `_frame_Qf_eq_one` / `_frame_Pf_eq_one`, banked). Coupling: thread a
  -- `hsplit : ∀ w, split w = deepestSplit … (paramsEquivFlat (deepestPoint)) w` hyp (cert + `deepest_loss_squeeze`)
  -- and inline the concrete `deepestSplit` at the `deepest_gauge_construction` site so `hsplit := rfl`
  -- (Codex `xhigh` verdict A; lowest churn).
  --
  -- *** SHARED-J RECONCILIATION (the J-DEPENDENT tail — do NOT pick an independent column-split here). ***
  -- The final step `reindex(P0·(prod(paramsSymm w) − B)·QL) = fromBlocks (P00−1) P01 P10 P11` and the
  -- `h00/h01/h10` energy-block identification both USE the boundary frame `P0, QL`. PIN1's re-architecture
  -- determines the last-layer frame by a B-pivot column-split permutation Π_J (pivot columns to front so
  -- B22 is invertible). The `reindex(P0·B·QL) = fromBlocks 1 0 0 0` normalisation MUST use the SAME pivot
  -- set J as PIN1's frame, else they misalign (controller coupling alert, 2026-06-24). So this step is
  -- LEFT for the shared-J reconciliation: parametrize on the PIN1 boundary frame / J rather than choosing one.
  -- core comparability is `core_comparability_squeeze` (#54, banked, J-independent).
  --
  -- BEDROCK BANKED (the l2-pin tide): the shared `J` AND the FULL frame fact are now banked in
  -- `DeepestPivotFrame` (axiom-clean `[propext, Classical.choice, Quot.sound]`):
  --   `exists_deepest_lastLayer_pivotFrame H r B hB hr hL hL2` produces `⟨J, Q, IsUnit Q,
  --    IsUnit ((reindex (pivotThresholdSplit r (H last) J)² Q)₂₂),
  --    reindex (rThresholdSplit r (H last)) (pivotThresholdSplit r (H last) J)
  --        (deepestPoint … (lastLayer) · Q) = fromBlocks 1 0 0 0⟩`.
  -- This is the SINGLE shared object to thread to BOTH PIN1 (the last-layer frame + `deepestEPivot` split)
  -- and here (step (3) column reindex of B). The shared-J reconciliation = pass the SAME `J`, `Q` to both;
  -- pivot(B)=pivot(V) (`B = U·V`, `U` injective ⟹ `rank(B_J)=rank(V_J)=r`) makes the SAME `J` valid for the
  -- target normalization. The `reindex(P0·B·QL)=fromBlocks 1 0 0 0` step uses the SAME
  -- `pivotThresholdSplit r (H last) J`. Threading a single `J` from `deepest_gauge_construction` to both
  -- makes divergence a compile-time tripwire (`hSreg_eq`'s `rw [h01]` fails to typecheck if the column
  -- index types differ). NOTE the frame `Q` is now the EXPLICIT pivot-aligned frame (corrected from the
  -- unsound generic-corM route — see PIN1 note (A)); the deepest-point frame's last-layer arm must adopt it.
  -- REMAINING (the genuine geometric content, NOT yet written): the J-independent readX/Y/Z→raw block chain
  -- (the sigma-trans `.symm` chase, ~30-50 LoC/arm, only "probed convergent" — see the SUB-BLOCKER above) +
  -- the entry-wise `reindex(fromBlocks readX readY readZ Tcore) = (paramsEquivFlat.symm w − deepestPoint) s`
  -- + `endpoint_telescoping` + the J-dependent `reindex(P0·B·QL)=fromBlocks 1 0 0 0` (uses the new `J`) +
  -- `core_comparability_squeeze` (banked). This is several hundred lines of unwritten geometry, not a thread-J.
  --
  -- ARCHITECTURE VALIDATED (l2-pin-migration tide, 2026-06-24): the codomain-split convention is the
  -- LOCALIZED "last-layer-only" pivot twist — see the PIN1 note (`deepestEPivot_regSlice_fderiv`) for the
  -- L1-vs-L2 verdict (L2 is UNSOUND) + the discriminating identity + the cast caveat (`finCongr
  -- (H_lastLayer_succ H hL)` bridges `J` from `Fin (H ((lastLayer hL).succ))` to `Fin (H (Fin.last L))`).
  -- The `h00/h01/h10` block identifications here MUST read the product through the SAME
  -- `eLast := pivotThresholdSplit r (H last) J` (matching `deepestEPivot_sq_sum_eq_blocks`'s codomain
  -- split), and step (3) `reindex(P0·B·QL)=fromBlocks 1 0 0 0` uses the SAME `eLast` from the frame fact
  -- `exists_deepest_lastLayer_pivotFrame` — divergence is a typecheck tripwire (`hSreg_eq`'s `rw [h01]`).
  sorry

/-- **PIN 2 — the loss squeeze** (the geometric heart). Near the deepest point (flat coords), the loss
is two-sidedly bounded by `Φ = ∑ (regStraighten (split w)).1² + deepestCoreF (coreAbsorb (split w)).2.1`.
The matrix-block reduction `∏C − blockNormal → P11 = leak + Rcore` (g164 boundary frames) feeding the
banked `core_comparability_squeeze` (#54: leak ∈ ideal(reg), charged to `∑E²`). `regStraighten` is the
(C)-fallback total continuous fn; the squeeze is the local `∃ U` germ where `(regStraighten w).1 = E`.
**Takes the concrete-map defining identities** (`hregval`: reg-output is the pivot residual
`deepestEPivot`; `hcoreabs`: `coreAbsorb` is the cutoff Schur shear) — without them the maps are
arbitrary and the bound is unprovable (the g161-class confound). -/
theorem deepest_loss_squeeze (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (coreAbsorb : DeepestSplit H r (deepestNGauge H r) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (hsplit_base : split ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) = 0)
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (hregval : ∀ q : DeepestSplit H r (deepestNGauge H r),
      (regStraighten q).1 = deepestEPivot H r hr hL J Pf Qf (q.1, q.2.2))
    (hcoreabs : coreAbsorb = deepestCoreAbsorb H r hr hL) :
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
  -- **ASSEMBLY (B), Codex-designed (loss-squeeze-wire-answer, option iii).** The frame-bridge cert
  -- `framedParams_split_eq_frame_raw` is the ONE geometric input; the wiring below is sorry-free.
  classical
  obtain ⟨P0, QL, Pi, Qi, t, γ₁, γ₂, hP, hQ, hγ₁, hγ₂, hKP_pos, hKi_pos, U, hU, hbr⟩ :=
    framedParams_split_eq_frame_raw H r B hB hr hL J Pf Qf split hsplit
  -- Endpoint-frame energies (the conjugation constants). `KP = ∑P0²·∑QL²`, `Ki = ∑Pi²·∑Qi²`.
  set KP := (∑ i, ∑ k, (P0 i k) ^ 2) * (∑ j, ∑ k, (QL k j) ^ 2) with hKP
  set Ki := (∑ i, ∑ k, (Pi i k) ^ 2) * (∑ j, ∑ k, (Qi k j) ^ 2) with hKi
  -- `Klo = 2(1+t²)·KP`, `Kup = Ki·(2+2t²)`; both positive (the cert supplies `0 < KP`, `0 < Ki`).
  set Klo := 2 * (1 + t ^ 2) * KP with hKlo
  set Kup := Ki * (2 + 2 * t ^ 2) with hKup
  have hKlo_pos : 0 < Klo := by rw [hKlo]; positivity
  have hKup_pos : 0 < Kup := by rw [hKup]; positivity
  have hKup_nonneg : 0 ≤ Kup := le_of_lt hKup_pos
  -- The two squeeze constants (Codex's, fixed up for the comparability-not-equality core).
  refine ⟨((1 + γ₁) * Klo)⁻¹, Kup * (1 + γ₂), ?_, ?_, U, hU, ?_⟩
  · positivity
  · positivity
  -- Per-`w` bound.
  intro w hw
  obtain ⟨P00, P01, P10, P11, hP00, hconj, h00, h01, h10, hleak, hcore_le, hcore_ge⟩ := hbr w hw
  letI : Invertible P00 := hP00
  -- The framed two-sided loss bound on `N = ∏(paramsSymm w) − B` (the banked leaf core).
  obtain ⟨hlo, hhi⟩ := dlnLoss_two_sided_of_frame
    (prod H ((paramsEquivFlat H).symm w) - B) P0 QL Pi Qi hP hQ
    (rThresholdSplit r (H 0) (hr 0)) (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
    P00 P01 P10 P11 t hconj hleak
  -- Name the energies. `Sreg` = the three regular blocks; `Score` = the Schur core; `NN` = loss.
  set Sreg := ((∑ i, ∑ j, ((P00 - 1) i j) ^ 2) + (∑ i, ∑ j, (P01 i j) ^ 2))
      + (∑ i, ∑ j, (P10 i j) ^ 2)
    with hSreg
  set Score := (∑ i, ∑ j, ((P11 - P10 * ⅟P00 * P01) i j) ^ 2) with hScore
  set NN := ∑ i, ∑ j, ((prod H ((paramsEquivFlat H).symm w) - B) i j) ^ 2 with hNN
  -- `dlnLoss = NN` (def-unfold).
  have hloss_eq : dlnLoss H B ((paramsEquivFlat H).symm w) = NN := rfl
  -- `Sreg = ∑ i, (regStraighten (split w)).1 i ^ 2` (the Φ-reg identification): via `hregval` →
  -- `deepestEPivot_sq_sum_eq_blocks` → the block identifications `h00/h01/h10`.
  have hSreg_eq : Sreg = ∑ i, (regStraighten (split w)).1 i ^ 2 := by
    rw [hregval (split w)]
    rw [deepestEPivot_sq_sum_eq_blocks H r hr hL J Pf Qf ((split w).1, (split w).2.2)]
    rw [hSreg, h00, h01, h10]; ring
  -- The core-comparability + leak bound fold into the squeeze. `coreΦ = deepestCoreF (coreAbsorb)`.
  rw [hcoreabs]
  set coreΦ := deepestCoreF H r (deepestCoreAbsorb H r hr hL (split w)).2.1 with hcoreΦ
  -- Nonnegativity facts.
  have hSreg_nn : 0 ≤ Sreg := by
    rw [hSreg]; positivity
  have hScore_nn : 0 ≤ Score := by rw [hScore]; positivity
  have hcoreΦ_nn : 0 ≤ coreΦ := by rw [hcoreΦ]; exact dlnLoss_nonneg _ _ _
  -- `cleanE = Sreg + Score`; the leaf bounds are `cleanE ≤ Klo·NN` and `NN ≤ Kup·cleanE`.
  -- (the leaf lemma states them with the explicit constants; identify them with Klo/Kup.)
  have hlo' : Sreg + Score ≤ Klo * NN := by
    rw [hKlo, hKP]; exact hlo
  have hhi' : NN ≤ Kup * (Sreg + Score) := by
    rw [hKup, hKi, mul_assoc]; exact hhi
  -- The target Φ for this `w`.
  set Φ := (∑ i, (regStraighten (split w)).1 i ^ 2) + coreΦ with hΦ
  have hΦ_nn : 0 ≤ Φ := by
    rw [hΦ]; refine add_nonneg ?_ hcoreΦ_nn
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  -- `Sreg = ∑(regStraighten …)²`, so `Φ = Sreg + coreΦ`.
  have hΦ_eq : Φ = Sreg + coreΦ := by rw [hΦ, hSreg_eq]
  refine ⟨hΦ_nn, ?_, ?_⟩
  · -- LOWER: `c₁·Φ ≤ dlnLoss = NN`. `Φ = Sreg + coreΦ ≤ Sreg + γ₁·Score ≤ (1+γ₁)(Sreg+Score)
    -- ≤ (1+γ₁)·Klo·NN`. So `((1+γ₁)Klo)⁻¹·Φ ≤ NN`.
    rw [hloss_eq]
    have hstep1 : Φ ≤ Sreg + γ₁ * Score := by
      rw [hΦ_eq]; linarith [hcore_ge]
    have hstep2 : Sreg + γ₁ * Score ≤ (1 + γ₁) * (Sreg + Score) := by
      have hexp : (1 + γ₁) * (Sreg + Score) - (Sreg + γ₁ * Score) = γ₁ * Sreg + Score := by ring
      have hpos : 0 ≤ γ₁ * Sreg + Score :=
        add_nonneg (mul_nonneg (le_of_lt hγ₁) hSreg_nn) hScore_nn
      linarith [hexp, hpos]
    have hstep3 : (1 + γ₁) * (Sreg + Score) ≤ (1 + γ₁) * (Klo * NN) :=
      mul_le_mul_of_nonneg_left hlo' (by positivity)
    have hΦle : Φ ≤ (1 + γ₁) * Klo * NN := by
      calc Φ ≤ Sreg + γ₁ * Score := hstep1
        _ ≤ (1 + γ₁) * (Sreg + Score) := hstep2
        _ ≤ (1 + γ₁) * (Klo * NN) := hstep3
        _ = (1 + γ₁) * Klo * NN := by ring
    -- multiply `hΦle : Φ ≤ (1+γ₁)·Klo·NN` by `c₁ = ((1+γ₁)·Klo)⁻¹ ≥ 0`; `c₁·((1+γ₁)·Klo) = 1`.
    have hden_pos : 0 < (1 + γ₁) * Klo := by positivity
    have hc₁ := mul_le_mul_of_nonneg_left hΦle (le_of_lt (inv_pos.mpr hden_pos))
    rw [show ((1 + γ₁) * Klo)⁻¹ * ((1 + γ₁) * Klo * NN) = NN from by
      field_simp] at hc₁
    exact hc₁
  · -- UPPER: `dlnLoss = NN ≤ Kup·(Sreg + Score) ≤ Kup·(Sreg + γ₂·coreΦ) ≤ Kup·(1+γ₂)·Φ`.
    rw [hloss_eq]
    have hstep1 : Sreg + Score ≤ Sreg + γ₂ * coreΦ := by linarith [hcore_le]
    have hstep2 : Sreg + γ₂ * coreΦ ≤ (1 + γ₂) * Φ := by
      rw [hΦ_eq]
      have hexp : (1 + γ₂) * (Sreg + coreΦ) - (Sreg + γ₂ * coreΦ) = γ₂ * Sreg + coreΦ := by ring
      have hpos : 0 ≤ γ₂ * Sreg + coreΦ :=
        add_nonneg (mul_nonneg (le_of_lt hγ₂) hSreg_nn) hcoreΦ_nn
      linarith [hexp, hpos]
    calc NN ≤ Kup * (Sreg + Score) := hhi'
      _ ≤ Kup * (Sreg + γ₂ * coreΦ) := mul_le_mul_of_nonneg_left hstep1 hKup_nonneg
      _ ≤ Kup * ((1 + γ₂) * Φ) := mul_le_mul_of_nonneg_left hstep2 hKup_nonneg
      _ = Kup * (1 + γ₂) * Φ := by ring

/-- **The bundled gauge-slice construction** (#44c sub-3, the COUPLED obligation, `2 ≤ L`). Assembles
the `split` (`deepestSplit_exists`, MP reindex), `coreAbsorb` (`deepest_coreAbsorb_exists`, PIN 0),
`regAbsorb` (`deepest_regAbsorb_exists`, PIN 1), and the `loss_squeeze` (`deepest_loss_squeeze`,
PIN 2) into the bundled existence the structure consumes. The `2 ≤ L` hypothesis makes the two
boundary layers distinct, so the deepest point's layer-0 right-frame and layer-(L−1) left-frame are
the identity (`deepestPoint_frame_Qf_eq_one` / `_Pf_eq_one`) — the boundary-triviality the
`endpoint_telescoping` interface-collapse needs. (The gauge chart straightens a product of `≥ 2`
matrices; `L = 1` is the separate smooth base case.) -/
theorem deepest_gauge_construction (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L) :
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
  obtain ⟨Jb, Pf, Qf, hPunit, hQunit, hQf0, hPfL, hNF, hQf22b, hcorner⟩ :=
    deepestPoint_frame_pivot_exists H r B hB hr hL hL2
  -- The outer-reindex pivot embedding lives on `Fin (H (Fin.last L))`; `Jb` on `Fin (H (lastLayer).succ)`.
  -- The cast bridge (`H_lastLayer_succ`); `pivotJSucc J = Jb` (the two `finCongr` round-trip).
  set J : Fin r ↪ Fin (H (Fin.last L)) :=
    Jb.trans (finCongr (H_lastLayer_succ H hL)).toEmbedding with hJ
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
  -- PIN 1: `regStraighten` (the (C)-fallback total-fn E-straightening) + its props (against `coreAbsorb`).
  -- The reg-output is the shared `deepestEPivot` (the PIN1↔PIN2 coupling object); its three analytic
  -- props feed PIN 1's IFT peel, its concrete value feeds PIN 2's squeeze.
  obtain ⟨D_E, eShear, hEp_deriv, he_shear⟩ :=
    deepestEPivot_deriv H r hr hL hL2 J Pf Qf hPf hQf hQf0 hPfL hQf22
  obtain ⟨regStraighten, hra_cont, hra_base, hra_core, hra_spec, hra_regval, hra_rlct⟩ :=
    deepest_regAbsorb_exists H r B hB hr hL (deepestNGauge H r) coreAbsorb
      (deepestCoreAbsorb_mp H r hr hL) hca_base hca_reg hca_spec
      (deepestEPivot H r hr hL J Pf Qf) (deepestEPivot_contdiff H r hr hL J Pf Qf)
      D_E hEp_deriv eShear he_shear (deepestEPivot_base H r hr hL hL2 J Pf Qf)
  -- PIN 2: the loss squeeze (consuming the concrete `coreAbsorb` + `regStraighten`'s defining identities).
  obtain ⟨c₁, c₂, hc₁, hc₂, U, hU, hsq⟩ :=
    deepest_loss_squeeze H r B hB hr hL J Pf Qf split coreAbsorb regStraighten hsplit_base hsplit
      hra_regval hca_def
  exact ⟨deepestNGauge H r, split, coreAbsorb, regStraighten, hsplit_mp, hsplit_base,
    hca_base, hca_reg, hca_spec, hca_rlct, hra_cont, hra_base, hra_core, hra_spec, hra_rlct,
    c₁, c₂, hc₁, hc₂, U, hU, hsq⟩

/-- **The `DeepestGaugeChart` instance** (#44c sub-3, `deepest_gauge_squeeze_exists`, `2 ≤ L`).
Destructures the bundled construction into the structure. The `2 ≤ L` hypothesis (distinct boundary
layers) is what `deepest_gauge_construction` needs for the endpoint-frame triviality; crux2 wires
`deepest_gauge_squeeze_exists := this` on the `2 ≤ L` branch (`L = 1` is the smooth base case). -/
theorem deepest_gauge_chart_construct (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L) :
    Nonempty (DeepestGaugeChart H r B hB hr hL) := by
  obtain ⟨nGauge, split, coreAbsorb, regStraighten, hsplit_mp, hsplit_base, hca_base, hca_reg,
    hca_spec, hca_rlct, hra_cont, hra_base, hra_core, hra_spec, hra_rlct, hsq⟩ :=
    deepest_gauge_construction H r B hB hr hL hL2
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
