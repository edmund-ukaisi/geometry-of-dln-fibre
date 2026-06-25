import DLNFibre.DLN.RLCT.Validate.DeepestGaugeChart
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeBlocks
import DLNFibre.DLN.RLCT.Validate.DeepestSplitReindex
import DLNFibre.DLN.RLCT.Validate.DeepestFrameRaw
import DLNFibre.DLN.RLCT.Validate.DeepestFrame
import DLNFibre.DLN.RLCT.Validate.DeepestFramedProduct
import DLNFibre.DLN.RLCT.Validate.DeepestTelescoping
import DLNFibre.DLN.RLCT.Validate.DeepestSchurShift
import DLNFibre.DLN.RLCT.Validate.DeepestSchurSmooth
import DLNFibre.DLN.RLCT.Validate.DeepestRegAbsorbIFT
import DLNFibre.DLN.RLCT.Validate.DeepestRegSliceFderiv
import DLNFibre.DLN.RLCT.Validate.DeepestRegBlockInvertible
import DLNFibre.DLN.RLCT.Validate.DeepestFramedProductPivot
import DLNFibre.DLN.RLCT.Validate.DeepestRegSliceFderivPivot
import DLNFibre.DLN.RLCT.Validate.DeepestPivotFrame
import DLNFibre.DLN.RLCT.Foundations.CoreShearMP
import DLNFibre.DLN.RLCT.Foundations.DeepestSplitHaar
import DLNFibre.DLN.RLCT.Validate.DeepestSchurComparability
import DLNFibre.DLN.RLCT.Validate.FrontPivotProducer

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
    -- **L2-PIN2 (full-reg):** the reg output `E_full` reads ALL THREE slots (incl. the core leak), so the
    -- squeeze's reg energy matches the loss's `Sreg` (thread 31). `regStraighten = regStraightenOf2 E_full`.
    (E_full : DeepestSplit H r nGauge → (Fin (deepestNReg H r) → ℝ))
    (hEp_contdiff : ContDiff ℝ (⊤ : ℕ∞) E_full)
    (hEp_base : E_full 0 = 0)
    -- The peel input: `π̃ := regStraightenOf2 (E_full ∘ coreAbsorb.symm)` (the `coreAbsorb.symm`-conjugated
    -- straightening, Codex option D) is a local diffeo at `0` — ContDiff + invertible strict-deriv. Its
    -- reg-block is `F ∘ D(coreAbsorb.symm)`'s reg part; invertibility uses `∂E_full/∂core(0)=0` (the
    -- degree-2 core-block-vanishing) so the reg-reg block stays PIN1's `F`. Supplied by the producer.
    (eTilde : DeepestSplit H r nGauge ≃L[ℝ] DeepestSplit H r nGauge)
    (hTilde_contdiff : ContDiff ℝ (⊤ : ℕ∞)
      (regStraightenOf2 (fun q => E_full (coreAbsorb.symm q))))
    (hTilde_deriv : HasStrictFDerivAt (regStraightenOf2 (fun q => E_full (coreAbsorb.symm q)))
      (eTilde : DeepestSplit H r nGauge →L[ℝ] DeepestSplit H r nGauge) 0) :
    ∃ regStraighten : DeepestSplit H r nGauge → DeepestSplit H r nGauge,
      Continuous regStraighten ∧
      regStraighten 0 = 0 ∧
      (∀ q : DeepestSplit H r nGauge, (regStraighten q).2.1 = q.2.1) ∧
      (∀ q : DeepestSplit H r nGauge, (regStraighten q).2.2 = q.2.2) ∧
      -- The reg-output IS the FULL residual `E_full` (the defining identity PIN 2's `loss_squeeze` needs).
      (∀ q : DeepestSplit H r nGauge, (regStraighten q).1 = E_full q) ∧
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
  refine ⟨regStraightenOf2 E_full,
    continuous_regStraightenOf2 E_full hEp_contdiff.continuous,
    regStraightenOf2_basepoint E_full hEp_base,
    fun q => (rfl : (regStraightenOf2 E_full q).2.1 = q.2.1),
    fun q => (rfl : (regStraightenOf2 E_full q).2.2 = q.2.2),
    fun q => regStraightenOf2_fst E_full q, ?_⟩
  -- `regAbsorb_rlct`: the CORE-DEPENDENT reduce (`reduce2`, Codex option D) — conjugate by
  -- `coreAbsorb.symm`, baking it into `π̃`, then peel `π̃` via the IFT local-diffeo adapter.
  have hpeel :
      rlctAtOn (fun q : DeepestSplit H r nGauge =>
          (∑ i, (E_full (coreAbsorb.symm q)) i ^ 2) + deepestCoreF H r q.2.1) 0
        = rlctAtOn (fun q : DeepestSplit H r nGauge =>
          (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1) 0 := by
    -- `F0 ∘ π̃ q = ∑ (E_full (coreAbsorb.symm q))² + coreF q.2.1` (`π̃ = regStraightenOf2 (E_full ∘ symm)`,
    -- so `(π̃ q).1 = E_full (coreAbsorb.symm q)`, `(π̃ q).2.1 = q.2.1`).
    have hkey := rlctAtOn_comp_localDiffeo
      (fun q : DeepestSplit H r nGauge => (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
      (0 : DeepestSplit H r nGauge)
      (regStraightenOf2 (fun q => E_full (coreAbsorb.symm q))) eTilde hTilde_contdiff hTilde_deriv
      (regStraightenOf2_basepoint (fun q => E_full (coreAbsorb.symm q)) (by
        show E_full (coreAbsorb.symm 0) = 0
        have hsymm0 : coreAbsorb.symm 0 = 0 := by
          conv_lhs => rw [← hca_base]; rw [coreAbsorb.symm_apply_apply]
        rw [hsymm0, hEp_base]))
    -- `(fun q => F0 (π̃ q)) = fun q => ∑(E_full (symm q))² + coreF q.2.1` (the carried `.2.1 = q.2.1`).
    have hfun : (fun q : DeepestSplit H r nGauge =>
          (∑ i, (regStraightenOf2 (fun q => E_full (coreAbsorb.symm q)) q).1 i ^ 2)
            + deepestCoreF H r (regStraightenOf2 (fun q => E_full (coreAbsorb.symm q)) q).2.1)
        = fun q : DeepestSplit H r nGauge =>
          (∑ i, (E_full (coreAbsorb.symm q)) i ^ 2) + deepestCoreF H r q.2.1 := by
      funext q; rfl
    rw [hfun] at hkey
    exact hkey
  exact rlctAtOn_regAbsorb_reduce2 coreAbsorb E_full
    (fun rg : Fin (deepestNReg H r) → ℝ => ∑ i, rg i ^ 2) (deepestCoreF H r)
    hca_mp hca_base hca_reg hpeel

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

/-- **The FULL regular residual blocks** `(P00 − I, P01, P10)` of the FULL framed product `∏C`
(`framedParamsPivot`, core block = the core slot read — NOT the T=0 `framedParamsRegPivot`), packed
into `Fin nReg → ℝ` via `regResidualPack`. This is the L2-PIN2 repair object: its reg energy is the
FULL product's `Sreg` — what the loss sees — so the squeeze's reg term reads the core leak (thread 31).
At the zero core slot it collapses to `deepestEPivot` (the bridge `deepestEFull_coreZero` re-using
PIN1's invertible reg-slice derivative `F` verbatim). -/
noncomputable def deepestEFull (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
    DeepestSplit H r (deepestNGauge H r) → (Fin (deepestNReg H r) → ℝ) :=
  fun q =>
    let P := Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
      (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
      (prod H (framedParamsPivot H r hr hL J Pf Qf q))
    fun i => match regResidualPack H r hr i with
      | Sum.inl (a, b) => (P.toBlocks₁₁ - 1) a b
      | Sum.inr (Sum.inl (a, b)) => P.toBlocks₁₂ a b
      | Sum.inr (Sum.inr (a, b)) => P.toBlocks₂₁ a b

/-- **The core-zero bridge** `deepestEFull (reg, 0, spec) = deepestEPivot (reg, spec)`: at the zero
core slot the FULL framed product collapses to the T=0 one (`framedParamsPivot_coreZero`), so the FULL
reg residual equals the pivot residual. Re-uses PIN1's reg-slice derivative `F` verbatim (the squeeze
reads `deepestEFull`, but its reg-slice — core = 0, spec = 0 — IS `deepestEPivot`). -/
theorem deepestEFull_coreZero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (reg : Fin (deepestNReg H r) → ℝ) (spec : Fin (deepestNGauge H r) → ℝ) :
    deepestEFull H r hr hL J Pf Qf (reg, 0, spec) = deepestEPivot H r hr hL J Pf Qf (reg, spec) := by
  simp only [deepestEFull, deepestEPivot,
    framedParamsPivot_coreZero H r hr hL J Pf Qf reg spec]

/-- `deepestEFull` is `ContDiff ⊤` (each coordinate is a reindexed `prod`-entry of the full pivot
framed product, `contDiff_framedParamsPivot_entry` → `contDiff_prod_entry`). Mirrors
`deepestEPivot_contdiff` over the full `DeepestSplit` domain. -/
theorem deepestEFull_contdiff (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (deepestEFull H r hr hL J Pf Qf) := by
  have hlayer : ∀ (s : Fin L) (a : Fin (H s.castSucc)) (b : Fin (H s.succ)),
      ContDiff ℝ (⊤ : ℕ∞) (fun q => framedParamsPivot H r hr hL J Pf Qf q s a b) :=
    contDiff_framedParamsPivot_entry H r hr hL J Pf Qf
  have hprod : ∀ (a : Fin (H 0)) (b : Fin (H (Fin.last L))),
      ContDiff ℝ (⊤ : ℕ∞) (fun q => prod H (framedParamsPivot H r hr hL J Pf Qf q) a b) :=
    fun a b => contDiff_prod_entry H (framedParamsPivot H r hr hL J Pf Qf) hlayer a b
  refine contDiff_pi.2 (fun i => ?_)
  have hcoord : (fun q => deepestEFull H r hr hL J Pf Qf q i)
      = fun q =>
        let P := Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (prod H (framedParamsPivot H r hr hL J Pf Qf q))
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

/-- **`deepestEFull`'s derivative at `0` is the core-reading invertible SHEAR** (the L2-PIN2 analogue
of `deepestEPivot_deriv`, using the `W`-unsplit `regStraightenTotalCLM2`). The reg-block of `D_E :=
fderiv deepestEFull 0` reads ONLY the reg-in direction `(r0, 0)` (core = 0, spec = 0); there
`deepestEFull (r0, 0) = deepestEPivot (r0, 0)` (the core-zero bridge), so the reg-block IS PIN1's
invertible frame factor `F` — RE-USED VERBATIM. Invertibility of the total shear needs only `F`
invertible (the core-in / spec-in blocks live inside `D_E(0, w')`, subtracted by the inverse). -/
theorem deepestEFull_deriv (H : Fin (L + 1) → ℕ) (r : ℕ)
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
    ∃ (D_E : DeepestSplit H r (deepestNGauge H r) →L[ℝ] (Fin (deepestNReg H r) → ℝ))
      (e : DeepestSplit H r (deepestNGauge H r) ≃L[ℝ] DeepestSplit H r (deepestNGauge H r)),
      HasStrictFDerivAt (deepestEFull H r hr hL J Pf Qf) D_E 0 ∧
      (e : DeepestSplit H r (deepestNGauge H r) →L[ℝ] DeepestSplit H r (deepestNGauge H r))
        = regStraightenTotalCLM2 D_E := by
  -- `D_E := fderiv deepestEFull 0` (free from `_contdiff`); its reg-block reads `(r0, 0)` (core=spec=0),
  -- where `deepestEFull = deepestEPivot` (bridge), so it is PIN1's invertible `F`.
  set D_E := fderiv ℝ (deepestEFull H r hr hL J Pf Qf) 0 with hD_E
  have hsd : HasStrictFDerivAt (deepestEFull H r hr hL J Pf Qf) D_E 0 :=
    (deepestEFull_contdiff H r hr hL J Pf Qf).hasStrictFDerivAt (by simp)
  obtain ⟨F, hF⟩ := deepestEPivot_regSlice_fderiv H r hr hL hL2 J Pf Qf hPf hQf hQf0 hPfL hQf22
  -- The reg-in embedding `r0 ↦ (r0, 0)` into `DeepestSplit = R × (C × S)` (core + spec held 0).
  have hregIn : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
      ((r0, 0) : DeepestSplit H r (deepestNGauge H r)))
      (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ] DeepestSplit H r (deepestNGauge H r)) 0 := by
    have := (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ]
      DeepestSplit H r (deepestNGauge H r)).hasStrictFDerivAt (x := 0)
    simpa [regInCLM] using this
  -- The reg-slice of `deepestEFull` IS `deepestEPivot`'s reg-slice (the core-zero bridge), with deriv `F`.
  have hregslice : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
      deepestEFull H r hr hL J Pf Qf (r0, 0))
      (F : (Fin (deepestNReg H r) → ℝ) →L[ℝ] (Fin (deepestNReg H r) → ℝ)) 0 := by
    have hbridge : (fun r0 : Fin (deepestNReg H r) → ℝ => deepestEFull H r hr hL J Pf Qf (r0, 0))
        = fun r0 : Fin (deepestNReg H r) → ℝ => deepestEPivot H r hr hL J Pf Qf (r0, 0) := by
      funext r0
      exact deepestEFull_coreZero H r hr hL J Pf Qf r0 0
    rw [hbridge]; exact hF
  -- Chain rule: the reg-slice deriv is `D_E.comp regInCLM`; fderiv uniqueness ⟹ `= F`.
  have hcomp : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
      deepestEFull H r hr hL J Pf Qf (r0, 0)) (D_E.comp regInCLM) 0 := by
    have hsd0 : HasStrictFDerivAt (deepestEFull H r hr hL J Pf Qf) D_E
        (((0 : Fin (deepestNReg H r) → ℝ), (0 : (Fin (flatDim (deepestM H r)) → ℝ)
          × (Fin (deepestNGauge H r) → ℝ)))) := hsd
    exact hsd0.comp (x := (0 : Fin (deepestNReg H r) → ℝ)) hregIn
  have hblock : D_E.comp (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ]
      DeepestSplit H r (deepestNGauge H r))
      = (F : (Fin (deepestNReg H r) → ℝ) →L[ℝ] (Fin (deepestNReg H r) → ℝ)) := by
    have h1 := hcomp.hasFDerivAt.fderiv
    have h2 := hregslice.hasFDerivAt.fderiv
    rw [← h1, ← h2]
  obtain ⟨e, he⟩ := regStraightenTotalCLM2_equiv_of_regBlock_isUnit
    (W := (Fin (flatDim (deepestM H r)) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) D_E F hblock.symm
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

/-- `deepestEFull 0 = 0` — at the origin the core slot is `0`, so `deepestEFull 0 = deepestEPivot (0,0)
= 0` via the core-zero bridge + `deepestEPivot_base`. -/
theorem deepestEFull_base (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
    deepestEFull H r hr hL J Pf Qf 0 = 0 := by
  rw [show (0 : DeepestSplit H r (deepestNGauge H r))
      = ((0 : Fin (deepestNReg H r) → ℝ), (0 : Fin (flatDim (deepestM H r)) → ℝ),
        (0 : Fin (deepestNGauge H r) → ℝ)) from rfl,
    deepestEFull_coreZero H r hr hL J Pf Qf 0 0]
  exact deepestEPivot_base H r hr hL hL2 J Pf Qf

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

/-- **The FULL reg-residual energy IS the FULL block energy** (the `deepestEFull` analogue of
`deepestEPivot_sq_sum_eq_blocks`). The sum of squares of `deepestEFull q` over `Fin nReg` equals the
three residual-block energies of `P = reindex(prod(framedParamsPivot q))` — `∑(P11−1)² + ∑P12² +
∑P21²`. Same `regResidualPack`-as-summing-bijection argument; only the framed product changes
(`framedParamsPivot` for `framedParamsRegPivot`). The block-level identity the producer's (b)-conjunct
reads. -/
theorem deepestEFull_sq_sum_eq_blocks (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    (∑ i, (deepestEFull H r hr hL J Pf Qf q i) ^ 2)
      = (∑ a, ∑ b, (((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (prod H (framedParamsPivot H r hr hL J Pf Qf q))).toBlocks₁₁ - 1) a b) ^ 2)
        + ((∑ a, ∑ b, ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (prod H (framedParamsPivot H r hr hL J Pf Qf q))).toBlocks₁₂ a b) ^ 2)
          + (∑ a, ∑ b, ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (prod H (framedParamsPivot H r hr hL J Pf Qf q))).toBlocks₂₁ a b) ^ 2)) := by
  rw [← Equiv.sum_comp (regResidualPack H r hr).symm
      (fun i => (deepestEFull H r hr hL J Pf Qf q i) ^ 2),
    Fintype.sum_sum_type]
  congr 1
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    simp only [deepestEFull, Equiv.apply_symm_apply]
  · rw [Fintype.sum_sum_type]
    congr 1 <;>
      (rw [Fintype.sum_prod_type]
       refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
       simp only [deepestEFull, Equiv.apply_symm_apply])

/-- The left endpoint frame at first layer, cast to the endpoint width `Fin (H 0)`. The canonical
witness of the endpoint telescoping (independent of the product being telescoped). -/
noncomputable def endpointP0 (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L)
    (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ) :
    Matrix (Fin (H 0)) (Fin (H 0)) ℝ :=
  (show (⟨0, by omega⟩ : Fin L).castSucc = (0 : Fin (L + 1)) from Fin.ext (by simp [Fin.castSucc]))
    ▸ P ⟨0, by omega⟩

/-- The right endpoint frame at last layer, cast to the endpoint width `Fin (H (Fin.last L))`. -/
noncomputable def endpointQL (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L)
    (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
    Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ :=
  (show (⟨L - 1, by omega⟩ : Fin L).succ = Fin.last L from Fin.ext (by simp [Fin.succ, Fin.last]; omega))
    ▸ Q ⟨L - 1, by omega⟩

/-- Transporting `IsUnit` of a square matrix along a `Fin (L+1)`-index equality (the `▸` type-cast,
matching the motive `fun x => Matrix (Fin (H x)) (Fin (H x)) ℝ` of `endpointP0`/`endpointQL`). -/
private theorem isUnit_index_cast (H : Fin (L + 1) → ℕ) {a b : Fin (L + 1)} (h : a = b)
    (M : Matrix (Fin (H a)) (Fin (H a)) ℝ) (hM : IsUnit M) :
    IsUnit (h ▸ M) := by
  subst h; exact hM

/-- `endpointP0` is a unit when the first-layer frame `P (firstLayer)` is (a type-cast preserves units). -/
theorem isUnit_endpointP0 (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L)
    (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (hP : IsUnit (P (firstLayer hL))) : IsUnit (endpointP0 H hL P) := by
  have hfl : (⟨0, by omega⟩ : Fin L) = firstLayer hL := Fin.ext (by simp [firstLayer])
  rw [endpointP0]
  exact isUnit_index_cast H
    (show (⟨0, by omega⟩ : Fin L).castSucc = (0 : Fin (L + 1)) from Fin.ext (by simp [Fin.castSucc]))
    (P ⟨0, by omega⟩) (by rw [hfl]; exact hP)

/-- `endpointQL` is a unit when the last-layer frame `Q (lastLayer)` is (a type-cast preserves units). -/
theorem isUnit_endpointQL (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L)
    (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hQ : IsUnit (Q (lastLayer hL))) : IsUnit (endpointQL H hL Q) := by
  have hll : (⟨L - 1, by omega⟩ : Fin L) = lastLayer hL := Fin.ext (by simp [lastLayer])
  rw [endpointQL]
  exact isUnit_index_cast H
    (show (⟨L - 1, by omega⟩ : Fin L).succ = Fin.last L from
      Fin.ext (by simp [Fin.succ, Fin.last]; omega))
    (Q ⟨L - 1, by omega⟩) (by rw [hll]; exact hQ)

/-- **Witnessed endpoint telescoping** (the witness-exposing variant of `endpoint_telescoping`, thread
31): the product equation with the CANONICAL endpoint frames `endpointP0`/`endpointQL` (independent of
the telescoped product). This is the existential telescope's content with the witnesses spelled out, so
the SAME endpoints serve every `w`. Proof: the same cast-heavy `prodAux` induction as
`endpoint_telescoping` (copied — the banked telescope is off-tide), targeting the explicit equality. -/
theorem endpoint_telescoping_eq (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L) (A C : Params H)
    (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hframe : ∀ s : Fin L, C s = P s * A s * Q s)
    (hinterface : ∀ (s : Fin L) (hs : (s : ℕ) + 1 < L),
      Q s = (1 : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) ∧
        P ⟨(s : ℕ) + 1, by omega⟩ = (1 : Matrix _ _ ℝ)) :
    prod H C = endpointP0 H hL P * prod H A * endpointQL H hL Q := by
  obtain ⟨Lm, rfl⟩ : ∃ Lm, L = Lm + 1 := ⟨L - 1, by omega⟩
  have hPid : ∀ s : Fin (Lm + 1), 1 ≤ (s : ℕ) →
      P s = (1 : Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ) := by
    intro s hs1
    obtain ⟨t', ht'⟩ : ∃ t', (s : ℕ) = t' + 1 := ⟨(s : ℕ) - 1, by omega⟩
    have hslt : ((⟨t', by omega⟩ : Fin (Lm + 1)) : ℕ) + 1 < Lm + 1 := by simp; omega
    have heq : (⟨t' + 1, by omega⟩ : Fin (Lm + 1)) = s := by apply Fin.ext; simp [ht']
    have := (hinterface ⟨t', by omega⟩ hslt).2
    rw [heq] at this; exact this
  have hQid : ∀ s : Fin (Lm + 1), (s : ℕ) + 1 < Lm + 1 →
      Q s = (1 : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :=
    fun s hs => (hinterface s hs).1
  have hCAint : ∀ s : Fin (Lm + 1), 1 ≤ (s : ℕ) → (s : ℕ) + 1 < Lm + 1 → C s = A s := by
    intro s hs1 hslt
    rw [hframe s, hPid s hs1, hQid s hslt, Matrix.one_mul, Matrix.mul_one]
  have h0cs : (⟨0, by omega⟩ : Fin (Lm + 1)).castSucc = (0 : Fin (Lm + 2)) := by
    apply Fin.ext; simp [Fin.castSucc]
  have hLs : (⟨Lm, by omega⟩ : Fin (Lm + 1)).succ = Fin.last (Lm + 1) := by
    apply Fin.ext; simp [Fin.succ, Fin.last]
  have hinv : ∀ (k : ℕ) (hk : k < Lm + 2), 1 ≤ k → k ≤ Lm →
      prodAux H C k hk = (h0cs ▸ P ⟨0, by omega⟩) * prodAux H A k hk := by
    intro k
    induction k with
    | zero => intro _ hk0; exact absurd hk0 (by norm_num)
    | succ k ih =>
        intro hsucc _ hkLm
        have e1 : H (⟨k, Nat.lt_of_succ_lt hsucc⟩ : Fin (Lm + 2))
            = H ((⟨k, Nat.lt_of_succ_lt_succ hsucc⟩ : Fin (Lm + 1)).castSucc) := rfl
        have e2 : H (⟨k + 1, hsucc⟩ : Fin (Lm + 2))
            = H ((⟨k, Nat.lt_of_succ_lt_succ hsucc⟩ : Fin (Lm + 1)).succ) := rfl
        rw [prodAux_succ H C k hsucc e1 e2, prodAux_succ H A k hsucc e1 e2]
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0
          set hkL' := Nat.lt_of_succ_lt_succ hsucc with hkL'def
          have hC0 : C ⟨0, hkL'⟩ = P ⟨0, hkL'⟩ * A ⟨0, hkL'⟩ := by
            rw [hframe ⟨0, _⟩, hQid ⟨0, _⟩ (by simp; omega), Matrix.mul_one]
          simp only [show prodAux H C 0 (Nat.lt_of_succ_lt hsucc)
              = (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) from rfl,
            show prodAux H A 0 (Nat.lt_of_succ_lt hsucc)
              = (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) from rfl, hC0]
          rw [reindex_mul_distrib_left (P ⟨0, hkL'⟩) (A ⟨0, hkL'⟩)
            (finCongr e1.symm) (finCongr e2.symm)]
          show (1 : Matrix (Fin (H (⟨0, hkL'⟩ : Fin (Lm + 1)).castSucc))
                (Fin (H (⟨0, hkL'⟩ : Fin (Lm + 1)).castSucc)) ℝ)
              * (P ⟨0, hkL'⟩ * A ⟨0, hkL'⟩)
            = P ⟨0, hkL'⟩ * ((1 : Matrix (Fin (H (⟨0, hkL'⟩ : Fin (Lm + 1)).castSucc))
                  (Fin (H (⟨0, hkL'⟩ : Fin (Lm + 1)).castSucc)) ℝ)
                * A ⟨0, hkL'⟩)
          rw [Matrix.one_mul, Matrix.one_mul]
        · rw [hCAint ⟨k, Nat.lt_of_succ_lt_succ hsucc⟩ (by simpa using hkpos) (by simp; omega),
            ih (Nat.lt_of_succ_lt hsucc) hkpos (by omega), Matrix.mul_assoc]
  -- FINAL: spell the endpoints. `endpointP0/QL` are defeq to the casts `h0cs ▸ P⟨0⟩`, `hLs ▸ Q⟨Lm⟩`.
  -- The endpoint defs are defeq to the internal casts (`⟨Lm+1-1,_⟩` reduces to `⟨Lm,_⟩`; proofs
  -- proof-irrelevant). Pin via `Fin.ext` index-congruence + `cast`/`▸` proof-irrelevance.
  have hP0eq : endpointP0 H hL P = (h0cs ▸ P ⟨0, by omega⟩ :
      Matrix (Fin (H 0)) (Fin (H 0)) ℝ) := by
    rw [endpointP0]
  have hQLeq : endpointQL H hL Q = (hLs ▸ Q ⟨Lm, by omega⟩ :
      Matrix (Fin (H (Fin.last (Lm + 1)))) (Fin (H (Fin.last (Lm + 1)))) ℝ) := rfl
  rw [hP0eq, hQLeq]
  have hLm1 : Lm + 1 < Lm + 1 + 1 := Nat.lt_succ_self (Lm + 1)
  have hLmL : Lm < Lm + 1 := Nat.lt_succ_self _
  have e1L : H (⟨Lm, Nat.lt_of_succ_lt hLm1⟩ : Fin (Lm + 1 + 1))
      = H ((⟨Lm, hLmL⟩ : Fin (Lm + 1)).castSucc) := rfl
  have e2L : H (⟨Lm + 1, hLm1⟩ : Fin (Lm + 1 + 1))
      = H ((⟨Lm, hLmL⟩ : Fin (Lm + 1)).succ) := rfl
  show prod H C = _
  simp only [prod]
  rw [prodAux_succ H C Lm hLm1 e1L e2L, prodAux_succ H A Lm hLm1 e1L e2L]
  rcases Nat.eq_zero_or_pos Lm with hLm0 | hLmpos
  · subst hLm0
    have hC0 : C ⟨0, hLmL⟩ = P ⟨0, hLmL⟩ * A ⟨0, hLmL⟩ * Q ⟨0, hLmL⟩ := hframe ⟨0, hLmL⟩
    rw [show prodAux H C 0 (Nat.lt_of_succ_lt hLm1) = (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) from rfl,
      show prodAux H A 0 (Nat.lt_of_succ_lt hLm1) = (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) from rfl,
      hC0,
      reindex_mul_distrib_right (P ⟨0, hLmL⟩ * A ⟨0, hLmL⟩) (Q ⟨0, hLmL⟩) (finCongr e1L.symm)
        (finCongr e2L.symm),
      reindex_mul_distrib_left (P ⟨0, hLmL⟩) (A ⟨0, hLmL⟩) (finCongr e1L.symm) (finCongr e2L.symm)]
    rw [show (finCongr e1L.symm) = Equiv.refl _ from finCongr_refl _,
      show (finCongr e2L.symm) = Equiv.refl _ from finCongr_refl _]
    show (1 : Matrix (Fin (H (⟨0, hLmL⟩ : Fin (0+1)).castSucc))
          (Fin (H (⟨0, hLmL⟩ : Fin (0+1)).castSucc)) ℝ)
        * (P ⟨0, hLmL⟩ * A ⟨0, hLmL⟩ * Q ⟨0, hLmL⟩)
      = P ⟨0, hLmL⟩ * ((1 : Matrix (Fin (H (⟨0, hLmL⟩ : Fin (0+1)).castSucc))
            (Fin (H (⟨0, hLmL⟩ : Fin (0+1)).castSucc)) ℝ) * A ⟨0, hLmL⟩) * Q ⟨0, hLmL⟩
    rw [Matrix.one_mul, Matrix.one_mul]
  · rw [hinv Lm (Nat.lt_of_succ_lt hLm1) hLmpos (le_refl _)]
    have hCLm : C ⟨Lm, hLmL⟩ = A ⟨Lm, hLmL⟩ * Q ⟨Lm, hLmL⟩ := by
      rw [hframe ⟨Lm, hLmL⟩, hPid ⟨Lm, hLmL⟩ (by simpa using hLmpos), Matrix.one_mul]
    rw [hCLm, reindex_mul_distrib_right (A ⟨Lm, hLmL⟩) (Q ⟨Lm, hLmL⟩)
      (finCongr e1L.symm) (finCongr e2L.symm),
      show Matrix.reindex (finCongr e2L.symm) (finCongr e2L.symm) (Q ⟨Lm, hLmL⟩)
        = (hLs ▸ Q ⟨Lm, by omega⟩ :
            Matrix (Fin (H (Fin.last (Lm + 1)))) (Fin (H (Fin.last (Lm + 1)))) ℝ) from by
      rw [show (finCongr e2L.symm) = Equiv.refl _ from finCongr_refl _]; rfl]
    exact mul_four_reassoc _ _ _ _

/-- **The threshold corner is the `corM` shape.** Reindexing `fromBlocks 1 0 0 0` by the inverse
`r`-threshold split on both sides yields the block-normal corner `fun i j => if i = j ∧ i < r then 1
else 0` — the RHS of `hNF`/`deepestPoint_frame_normal`. The same 4-arm `ext` as the read-decode atom,
with the `(1,1)`-block diagonal collapsing to `if i = j` (under `i, j < r`). -/
private theorem reindex_fromBlocks_one_eq_corM (r a b : ℕ) (ha : r ≤ a) (hb : r ≤ b) :
    Matrix.reindex (rThresholdSplit r a ha).symm (rThresholdSplit r b hb).symm
        (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
      = Matrix.of (fun (i : Fin a) (j : Fin b) =>
          if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.symm_symm]
  rcases hi : (rThresholdSplit r a ha) i with p | p <;>
    rcases hj : (rThresholdSplit r b hb) j with q | q
  · -- (inl, inl): the `(1,1)` block, `1 p q = if p = q then 1 else 0`; recover `i = castLE p`,
    -- `j = castLE q` so `i.val = p.val < r`, `j.val = q.val < r`, and `i.val = j.val ↔ p = q`.
    rw [Matrix.fromBlocks_apply₁₁]
    have hip : i = p.castLE ha := by rw [← rThresholdSplit_symm_inl r a ha p, ← hi, Equiv.symm_apply_apply]
    have hjq : j = q.castLE hb := by rw [← rThresholdSplit_symm_inl r b hb q, ← hj, Equiv.symm_apply_apply]
    simp only [Matrix.one_apply, Matrix.of_apply, hip, hjq, Fin.coe_castLE]
    by_cases hpq : p = q
    · subst hpq; simp [p.isLt]
    · rw [if_neg hpq, if_neg]
      rintro ⟨hval, _⟩
      exact hpq (Fin.ext hval)
  · rw [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    have hjq : j = ⟨r + q, by omega⟩ := by
      rw [← rThresholdSplit_symm_inr r b hb q, ← hj, Equiv.symm_apply_apply]
    have hip : i = p.castLE ha := by rw [← rThresholdSplit_symm_inl r a ha p, ← hi, Equiv.symm_apply_apply]
    simp only [Matrix.of_apply, hip, hjq, Fin.coe_castLE]
    rw [if_neg]; rintro ⟨hval, hlt⟩; omega
  · rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    have hip : i = ⟨r + p, by omega⟩ := by
      rw [← rThresholdSplit_symm_inr r a ha p, ← hi, Equiv.symm_apply_apply]
    simp only [Matrix.of_apply, hip]
    rw [if_neg]; rintro ⟨_, hlt⟩; simp at hlt
  · rw [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
    have hip : i = ⟨r + p, by omega⟩ := by
      rw [← rThresholdSplit_symm_inr r a ha p, ← hi, Equiv.symm_apply_apply]
    simp only [Matrix.of_apply, hip]
    rw [if_neg]; rintro ⟨_, hlt⟩; simp at hlt

/-- A square matrix over a nonempty index with a sum-of-squared-entries `= 0` is the zero matrix. -/
private theorem frob_sq_sum_eq_zero_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ k, (M i k) ^ 2) = 0 ↔ M = 0 := by
  constructor
  · intro h
    have hentry : ∀ i k, (M i k) ^ 2 = 0 := by
      have h1 : ∀ i ∈ Finset.univ, (∑ k, (M i k) ^ 2) = 0 := by
        refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp h
        exact fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _
      intro i k
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => sq_nonneg (M i k))).mp (h1 i (Finset.mem_univ i)) k (Finset.mem_univ k)
      exact h2
    ext i k
    have := hentry i k
    simpa [pow_eq_zero_iff] using this
  · intro h; subst h; simp

/-- The Frobenius sum-of-squares is `> 0` for a nonzero square matrix over a nonempty index. -/
private theorem frob_sq_sum_pos_of_ne_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ≠ 0) :
    0 < (∑ i, ∑ k, (M i k) ^ 2) := by
  rcases lt_or_eq_of_le (show (0 : ℝ) ≤ ∑ i, ∑ k, (M i k) ^ 2 from
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _) with h | h
  · exact h
  · exact absurd ((frob_sq_sum_eq_zero_iff M).mp h.symm) hM

/-- The identity matrix over a nonempty index is nonzero (its `(0,0)` entry is `1`). -/
private theorem matrix_one_ne_zero {n : ℕ} (hn : 0 < n) :
    (1 : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  intro h
  have := congrFun (congrFun h ⟨0, hn⟩) ⟨0, hn⟩
  simp [Matrix.one_apply] at this

/-- A left-invertible square matrix over a nonempty index is nonzero (`1 ≠ 0` there). -/
private theorem ne_zero_of_mul_eq_one_left {n : ℕ} (hn : 0 < n)
    (Pi M : Matrix (Fin n) (Fin n) ℝ) (h : Pi * M = 1) : M ≠ 0 := by
  intro hM
  rw [hM, Matrix.mul_zero] at h
  exact matrix_one_ne_zero hn h.symm

/-- A right-invertible square matrix over a nonempty index is nonzero (`1 ≠ 0` there). -/
private theorem ne_zero_of_mul_eq_one_right {n : ℕ} (hn : 0 < n)
    (M Qi : Matrix (Fin n) (Fin n) ℝ) (h : M * Qi = 1) : M ≠ 0 := by
  intro hM
  rw [hM, Matrix.zero_mul] at h
  exact matrix_one_ne_zero hn h.symm

/-- The layer partial-product matrix is continuous in the parameters (local copy; the
`FrontPivotProducer` / `LossContinuity` copies are private / collide with `DeepestGaugeChart`'s
`continuous_dlnLoss`). Induction on the chain length: base `prodAux 0 = 1` constant; step
`prodAux (k+1) = prodAux k * layer k`, the cast-transported layer normalised to the plain projection,
then `Continuous.matrix_mul`. -/
private theorem continuous_prodAux_loc (H : Fin (L + 1) → ℕ) (k : ℕ) (hk : k < L + 1) :
    Continuous (fun A : Params H => prodAux H A k hk) := by
  revert hk
  induction k with
  | zero =>
      intro hk
      simpa [prodAux] using
        (continuous_const :
          Continuous (fun _ : Params H => (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)))
  | succ k ih =>
      intro hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      let layer : Params H → Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ :=
        fun A => ((by rw [e1, e2]; exact A ⟨k, hkL⟩) :
          Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)
      have hLayer : Continuous layer := by
        dsimp [layer]
        simpa only [e1, e2, eq_mpr_eq_cast, cast_eq] using
          (continuous_apply (⟨k, hkL⟩ : Fin L) :
            Continuous (fun A : Params H => A ⟨k, hkL⟩))
      have hMul : Continuous (fun A : Params H => prodAux H A k hk' * layer A) :=
        (ih hk').matrix_mul hLayer
      exact hMul.congr fun A => by dsimp [layer]; rfl

/-- `w ↦ prod H ((paramsEquivFlat).symm w)` is continuous (the CLE `symm` is continuous;
`continuous_prodAux_loc` at `k = L`). -/
private theorem continuous_prod_symm (H : Fin (L + 1) → ℕ) :
    Continuous (fun w : Fin (flatDim H) → ℝ => prod H ((paramsEquivFlat H).symm w)) := by
  have hsymmcoe : ⇑(paramsEquivFlatCLE H).symm = ⇑(paramsEquivFlat H).symm := by
    funext y
    apply (paramsEquivFlat H).injective
    rw [(paramsEquivFlat H).apply_symm_apply]
    have hcle : (paramsEquivFlat H) ((paramsEquivFlatCLE H).symm y)
        = (paramsEquivFlatCLE H) ((paramsEquivFlatCLE H).symm y) := by
      rw [← paramsEquivFlatCLE_coe H]
    rw [hcle, ContinuousLinearEquiv.apply_symm_apply]
  have hsymm : Continuous fun w : Fin (flatDim H) → ℝ => (paramsEquivFlat H).symm w := by
    rw [← hsymmcoe]; exact (paramsEquivFlatCLE H).symm.continuous
  exact (continuous_prodAux_loc H L (Nat.lt_succ_self L)).comp hsymm

/-- `w ↦ reindex e₁ e₂ (P0·(prod((symm) w) − B)·QL)` is continuous (the conjugated residual,
`continuous_prod_symm` + matrix algebra). The continuity input to the S5b leak smallness. -/
private theorem continuous_Mw (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ)
    (P0 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
    (QL : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ)
    (e₁ : Fin (H 0) ≃ Fin r ⊕ Fin (H 0 - r))
    (e₂ : Fin (H (Fin.last L)) ≃ Fin r ⊕ Fin (H (Fin.last L) - r)) :
    Continuous fun w : Fin (flatDim H) → ℝ =>
      Matrix.reindex e₁ e₂ (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL) := by
  have hconj : Continuous fun w : Fin (flatDim H) → ℝ =>
      P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL :=
    (continuous_const.matrix_mul (((continuous_prod_symm H)).sub continuous_const)).matrix_mul
      continuous_const
  exact hconj.matrix_reindex e₁ e₂

/-- **S5b — the eventual leak bound** (`hproducer` conjunct (c), pivot-agnostic). With
`M w := reindex e₁ e₂ (P0·(prod((symm) w) − B)·QL)` and the producer blocks `P00 := M.toBlocks₁₁ + 1`,
`P01 := M.toBlocks₁₂`, `P10 := M.toBlocks₂₁`, the Schur leak `P10·(P00)⁻¹·P01` has squared-Frobenius
energy `≤ 1·Sreg` on a `𝓝` of `w0`, where `Sreg := (∑(P00−1)² + ∑P01²) + ∑P10² = frobSq M₁₁ + frobSq
M₁₂ + frobSq M₂₁`. At `w0`, `prod = B`, `M = 0`, so `P01 = P10 = 0`, `P00 = 1`, and `(P00)⁻¹·P01 = 0`.
Proof: `w ↦ ∑((P00 w)⁻¹·P01 w)²` is `ContinuousAt w0` (matrix inverse continuous at the unit `P00 w0 =
1` via `continuousAt_matrix_inv` + `continuousAt_inv₀` on the scalar det, composed with `continuous_Mw`)
with value `0 < 1`, so `≤ 1` eventually; then `leak_frobenius_bound` + `∑P10² ≤ Sreg`. Constant `t = 1`
is uniform; `U` is the smallness `𝓝`. -/
private theorem eventually_leak (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (P0 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
    (QL : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ)
    (e₁ : Fin (H 0) ≃ Fin r ⊕ Fin (H 0 - r))
    (e₂ : Fin (H (Fin.last L)) ≃ Fin r ⊕ Fin (H (Fin.last L) - r)) :
    ∀ᶠ w in 𝓝 ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
      (∑ i, ∑ j, (((Matrix.reindex e₁ e₂
              (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₂₁
            * ((Matrix.reindex e₁ e₂
                (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₁ + 1)⁻¹
            * (Matrix.reindex e₁ e₂
                (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₂) i j) ^ 2)
        ≤ (1 : ℝ) ^ 2
          * (((∑ i, ∑ j, (((Matrix.reindex e₁ e₂
                  (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₁) i j) ^ 2)
              + (∑ i, ∑ j, (((Matrix.reindex e₁ e₂
                  (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₂) i j) ^ 2))
            + (∑ i, ∑ j, (((Matrix.reindex e₁ e₂
                  (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₂₁) i j) ^ 2)) := by
  set w0 := (paramsEquivFlat H) (deepestPoint H r B hB hr hL) with hw0
  set Mfn : (Fin (flatDim H) → ℝ) →
      Matrix (Fin r ⊕ Fin (H 0 - r)) (Fin r ⊕ Fin (H (Fin.last L) - r)) ℝ :=
    fun w => Matrix.reindex e₁ e₂ (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL) with hMfn
  -- M w0 = 0 (residual prod − B = 0 at the deepest point).
  have hM0 : Mfn w0 = 0 := by
    have hsymm0 : (paramsEquivFlat H).symm w0 = deepestPoint H r B hB hr hL := by
      rw [hw0]; exact (paramsEquivFlat H).symm_apply_apply _
    have hprod0 : prod H (deepestPoint H r B hB hr hL) = B :=
      (deepestPoint_isDeep H r B hB hr hL).1
    simp only [hMfn, hsymm0, hprod0, sub_self, Matrix.mul_zero, Matrix.zero_mul]
    ext i j
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  -- Continuity of M, hence of each block and of (M₁₁+1)⁻¹·M₁₂.
  have hMcont : Continuous Mfn := continuous_Mw H r B P0 QL e₁ e₂
  have h11 : Continuous fun w => (Mfn w).toBlocks₁₁ := hMcont.matrix_submatrix _ _
  have h12 : Continuous fun w => (Mfn w).toBlocks₁₂ := hMcont.matrix_submatrix _ _
  have h21 : Continuous fun w => (Mfn w).toBlocks₂₁ := hMcont.matrix_submatrix _ _
  -- `P00 w := M₁₁ w + 1`, continuous, `= 1` at `w0` (`M w0 = 0`).
  have hP00cont : Continuous fun w => (Mfn w).toBlocks₁₁ + (1 : Matrix (Fin r) (Fin r) ℝ) :=
    h11.add continuous_const
  have hP00_0 : (Mfn w0).toBlocks₁₁ + (1 : Matrix (Fin r) (Fin r) ℝ) = 1 := by
    rw [hM0]; ext i j; simp [Matrix.toBlocks₁₁]
  -- `(P00 w)⁻¹` is `ContinuousAt w0` (`det (P00 w0) = det 1 = 1 ≠ 0`).
  have hdet0 : ((Mfn w0).toBlocks₁₁ + (1 : Matrix (Fin r) (Fin r) ℝ)).det ≠ 0 := by
    rw [hP00_0]; simp
  have hinvAt : ContinuousAt (fun w => ((Mfn w).toBlocks₁₁
      + (1 : Matrix (Fin r) (Fin r) ℝ))⁻¹) w0 := by
    have hinvdet : ContinuousAt Ring.inverse
        ((Mfn w0).toBlocks₁₁ + (1 : Matrix (Fin r) (Fin r) ℝ)).det := by
      rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet0
    have houter : ContinuousAt Inv.inv ((Mfn w0).toBlocks₁₁ + (1 : Matrix (Fin r) (Fin r) ℝ)) :=
      continuousAt_matrix_inv _ hinvdet
    exact ContinuousAt.comp (g := Inv.inv)
      (f := fun w => (Mfn w).toBlocks₁₁ + (1 : Matrix (Fin r) (Fin r) ℝ))
      houter hP00cont.continuousAt
  -- `g w := ∑ (((P00 w)⁻¹ · M₁₂ w) i j)²`, the global functional `Φ(A,B) := frobSq (A·B)` composed
  -- with the `ContinuousAt` pair `w ↦ ((P00 w)⁻¹, M₁₂ w)`. `Φ` is globally continuous.
  set Φ : Matrix (Fin r) (Fin r) ℝ × Matrix (Fin r) (Fin (H (Fin.last L) - r)) ℝ → ℝ :=
    fun p => ∑ i, ∑ j, ((p.1 * p.2) i j) ^ 2 with hΦ
  have hΦcont : Continuous Φ := by
    rw [hΦ]
    refine continuous_finset_sum _ (fun i _ => continuous_finset_sum _ (fun j _ => ?_))
    exact (((continuous_fst.matrix_mul continuous_snd).matrix_elem i j).pow 2)
  set g : (Fin (flatDim H) → ℝ) → ℝ :=
    fun w => Φ (((Mfn w).toBlocks₁₁ + (1 : Matrix (Fin r) (Fin r) ℝ))⁻¹, (Mfn w).toBlocks₁₂)
    with hg
  have hpairAt : ContinuousAt (fun w => (((Mfn w).toBlocks₁₁
      + (1 : Matrix (Fin r) (Fin r) ℝ))⁻¹, (Mfn w).toBlocks₁₂)) w0 :=
    hinvAt.prodMk h12.continuousAt
  have hgAt : ContinuousAt g w0 := hΦcont.continuousAt.comp hpairAt
  have hg0 : g w0 = 0 := by
    simp only [hg, hΦ]
    rw [hM0]
    have h120 : ((0 : Matrix (Fin r ⊕ Fin (H 0 - r))
        (Fin r ⊕ Fin (H (Fin.last L) - r)) ℝ).toBlocks₁₂) = 0 := by
      ext i j; simp [Matrix.toBlocks₁₂]
    simp only [h120, Matrix.mul_zero]; simp
  -- `g ≤ 1` eventually: `g` `ContinuousAt w0` with `g w0 = 0 < 1`.
  have hgsmall : ∀ᶠ w in 𝓝 w0, g w ≤ 1 :=
    Filter.Tendsto.eventually_le_const (u := (1 : ℝ)) (v := g w0)
      (by rw [hg0]; exact zero_lt_one) hgAt
  filter_upwards [hgsmall] with w hgw
  -- The leak chain on `w`: `∑(P10·N·P01)² ≤ (∑P10²)·(∑(N·P01)²) ≤ Sreg·1`.
  set N := ((Mfn w).toBlocks₁₁ + (1 : Matrix (Fin r) (Fin r) ℝ))⁻¹ with hN
  set P01b := (Mfn w).toBlocks₁₂ with hP01b
  set P10b := (Mfn w).toBlocks₂₁ with hP10b
  have hleak := leak_frobenius_bound N P01b P10b
  -- `∑(N·P01)² ≤ 1` is `g w ≤ 1` after column-major ↔ row-major (`Finset.sum_comm`).
  have hgw' : (∑ j, ∑ k, ((N * P01b) k j) ^ 2) ≤ 1 := by
    have hgwΦ : (∑ i, ∑ j, ((N * P01b) i j) ^ 2) ≤ 1 := by
      have hgeq : g w = ∑ i, ∑ j, ((N * P01b) i j) ^ 2 := by rw [hg, hΦ, hN, hP01b]
      rw [← hgeq]; exact hgw
    rw [Finset.sum_comm]; exact hgwΦ
  have hP10nn : (0 : ℝ) ≤ ∑ i, ∑ k, (P10b i k) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- `∑P10² ≤ Sreg` (it is the third summand; the other two summands are nonneg).
  have hSreg : (∑ i, ∑ k, (P10b i k) ^ 2)
      ≤ (((∑ i, ∑ j, ((Mfn w).toBlocks₁₁ i j) ^ 2)
            + (∑ i, ∑ j, ((Mfn w).toBlocks₁₂ i j) ^ 2))
          + (∑ i, ∑ j, ((Mfn w).toBlocks₂₁ i j) ^ 2)) := by
    have hnn1 : (0 : ℝ) ≤ ((∑ i, ∑ j, ((Mfn w).toBlocks₁₁ i j) ^ 2)
        + (∑ i, ∑ j, ((Mfn w).toBlocks₁₂ i j) ^ 2)) :=
      add_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    rw [hP10b]; linarith
  calc (∑ i, ∑ j, ((P10b * N * P01b) i j) ^ 2)
      ≤ (∑ i, ∑ k, (P10b i k) ^ 2) * (∑ j, ∑ k, ((N * P01b) k j) ^ 2) := hleak
    _ ≤ (((∑ i, ∑ j, ((Mfn w).toBlocks₁₁ i j) ^ 2)
            + (∑ i, ∑ j, ((Mfn w).toBlocks₁₂ i j) ^ 2))
          + (∑ i, ∑ j, ((Mfn w).toBlocks₂₁ i j) ^ 2)) * 1 := by
        apply mul_le_mul hSreg hgw' (Finset.sum_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ => sq_nonneg _)
        exact le_trans hP10nn hSreg
    _ = (1 : ℝ) ^ 2 * (((∑ i, ∑ j, ((Mfn w).toBlocks₁₁ i j) ^ 2)
            + (∑ i, ∑ j, ((Mfn w).toBlocks₁₂ i j) ^ 2))
          + (∑ i, ∑ j, ((Mfn w).toBlocks₂₁ i j) ^ 2)) := by ring

/-- **(d')/(e') lemma 1 — the core decode** (cert Q3, "routine"). On the inner ball (`χ = 1`, where
`deepestCoreAbsorb`'s cutoff Schur shift equals the honest raw correction), the absorbed-core energy
`deepestCoreF (deepestCoreAbsorb q).2.1` equals the squared-Frobenius energy of the product of the
per-layer Schur cores `S_s = T_s − Z_s(1+X_s)⁻¹Y_s` (with `T_s` the raw core read of `q.2.1`,
`(X_s,Y_s,Z_s)` the reg+spec reads). Decode chain: `coreShearHomeo` ADD-form +
`schurCutoffShift = schurShiftRaw` (χ=1) + `paramsEquivFlat (deepestM)` additivity/round-trip
(`schurShiftRaw = paramsEquivFlat (schurCorrection)`) + `dlnLoss M 0 A = frobSq (prod M A)`. EXACT. -/
theorem deepestCoreF_coreAbsorb_eq_prodSchur (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hq : q ∈ Metric.closedBall (0 : DeepestSplit H r (deepestNGauge H r))
      ((cutoffBump H r hr hL).rIn)) :
    deepestCoreF H r (deepestCoreAbsorb H r hr hL q).2.1
      = frobSq (prod (deepestM H r)
          (fun s => (paramsEquivFlat (deepestM H r)).symm q.2.1 s
            + schurCorrection H r hr hL (q.1, q.2.2) s)) := by
  -- The absorbed core slot: `coreShearHomeo` ADD-form `(coreAbsorb q).2.1 = q.2.1 + shift (q.1, q.2.2)`.
  have hcore : (deepestCoreAbsorb H r hr hL q).2.1
      = q.2.1 + schurCutoffShift H r hr hL (q.1, q.2.2) := rfl
  -- On the inner ball the cutoff shift equals the honest raw Schur shift.
  have hraw : schurCutoffShift H r hr hL (q.1, q.2.2)
      = schurShiftRaw H r hr hL (q.1, q.2.2) := by
    apply schurCutoffShift_eq_raw_of_mem_closedBall
    -- `(q.1, q.2.2)` lies in the inner ball whenever `q` does (the gauge slot is a projection,
    -- distance-nonincreasing).
    rw [Metric.mem_closedBall, dist_zero_right] at hq ⊢
    refine le_trans ?_ hq
    -- `‖(q.1, q.2.2)‖ = max ‖q.1‖ ‖q.2.2‖ ≤ max ‖q.1‖ (max ‖q.2.1‖ ‖q.2.2‖) = ‖q‖`.
    have h1 : ‖q.1‖ ≤ ‖q‖ := by rw [Prod.norm_def q]; exact le_max_left _ _
    have h2 : ‖q.2.2‖ ≤ ‖q‖ := by
      rw [Prod.norm_def q, Prod.norm_def q.2]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    rw [Prod.norm_def (q.1, q.2.2)]
    exact max_le h1 h2
  -- `schurShiftRaw = paramsEquivFlat (schurCorrection)`.
  have hsr : schurShiftRaw H r hr hL (q.1, q.2.2)
      = paramsEquivFlat (deepestM H r) (schurCorrection H r hr hL (q.1, q.2.2)) := rfl
  -- The decoded core tuple: `paramsEquivFlat.symm (q.2.1 + paramsEquivFlat (schurCorrection))`
  -- `= paramsEquivFlat.symm q.2.1 + schurCorrection` (additivity of `.symm` + round-trip).
  have hdecode : (paramsEquivFlat (deepestM H r)).symm ((deepestCoreAbsorb H r hr hL q).2.1)
      = (fun s => (paramsEquivFlat (deepestM H r)).symm q.2.1 s
          + schurCorrection H r hr hL (q.1, q.2.2) s) := by
    rw [hcore, hraw, hsr]
    -- `.symm` agrees with the linear `.symm` (`paramsEquivFlatLinear`), hence additive.
    have hsymmL : ∀ y, (paramsEquivFlat (deepestM H r)).symm y
        = (paramsEquivFlatLinear (deepestM H r)).symm y := by
      intro y
      apply (paramsEquivFlatLinear (deepestM H r)).injective
      rw [(paramsEquivFlatLinear (deepestM H r)).apply_symm_apply,
        show (paramsEquivFlatLinear (deepestM H r)) ((paramsEquivFlat (deepestM H r)).symm y)
          = (paramsEquivFlat (deepestM H r)) ((paramsEquivFlat (deepestM H r)).symm y) from
          congrFun (paramsEquivFlatLinear_coe (deepestM H r)) _,
        (paramsEquivFlat (deepestM H r)).apply_symm_apply]
    -- The second summand round-trips: `linear.symm (paramsEquivFlat (schurCorrection)) = schurCorrection`.
    have hrt : (paramsEquivFlatLinear (deepestM H r)).symm
        (paramsEquivFlat (deepestM H r) (schurCorrection H r hr hL (q.1, q.2.2)))
          = schurCorrection H r hr hL (q.1, q.2.2) := by
      rw [show (paramsEquivFlat (deepestM H r)) (schurCorrection H r hr hL (q.1, q.2.2))
          = (paramsEquivFlatLinear (deepestM H r)) (schurCorrection H r hr hL (q.1, q.2.2)) from
          (congrFun (paramsEquivFlatLinear_coe (deepestM H r)) _).symm,
        (paramsEquivFlatLinear (deepestM H r)).symm_apply_apply]
    -- Rewrite the LHS argument of `.symm` to the linear form, apply additivity + round-trip.
    rw [hsymmL (q.2.1 + paramsEquivFlat (deepestM H r) (schurCorrection H r hr hL (q.1, q.2.2))),
      map_add, hrt, ← hsymmL q.2.1]
    rfl
  -- Assemble: `deepestCoreF = dlnLoss M 0 (paramsEquivFlat.symm core) = frobSq (prod M core)`.
  show dlnLoss (deepestM H r)
      (0 : Matrix (Fin (deepestM H r 0)) (Fin (deepestM H r (Fin.last L))) ℝ)
      ((paramsEquivFlat (deepestM H r)).symm (deepestCoreAbsorb H r hr hL q).2.1)
    = frobSq _
  rw [hdecode]
  simp only [dlnLoss, frobSq, sub_zero]

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
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    -- **STRICT width positivity** (thread 31, 2026-06-25): the endpoint conjugation constants
    -- `KP = ∑P0²·∑QL²`, `Ki = ∑Pi²·∑Qi²` are STRICTLY positive only when the boundary widths are
    -- nonempty — a unit matrix over an empty index is `0` with zero energy. `hpos` (the strict reduced-
    -- width positivity `0 < M s ⟺ r < H s` the headline already carries) gives `0 < H 0`, `0 < H (last L)`.
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    -- **FRONT-PIVOT HYPOTHESIS (B (front-pivot WLOG) route, b-wlog-spec, 2026-06-25).** The pivot
    -- embedding is the FRONT embedding `k ↦ k` (`frontEmbed`), so its column pivots are `{0,…,r−1}`
    -- and `pivotThresholdSplit … J = rThresholdSplit …` (banked `pivotThresholdSplit_frontEmbed`).
    -- This is what makes the (b)-conjunct an EXACT equality `∑deepestEFull² = Sreg` (NOT the refuted
    -- two-sided comparability): for a front pivot the last-layer column-permutation `π_J` is the
    -- identity, the per-`w` telescope `prod (F w) = P0·prod(A w)·QL` is CLEAN for every `w` (not just
    -- `w0`), so the framed-product block reads coincide with the loss `Sreg` blocks entrywise. The
    -- caller discharges it by running the chart at `B·Π` (the column permutation bringing `B`'s rank-`r`
    -- pivots to the front), where the headline's `⨅ optimalSet` form is invariant (b-wlog-spec lemmas
    -- 1-5). The earlier non-front statement carried `δ₁, δ₂` comparability + an UNBUILT germ/Taylor atom.
    (hfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    -- **FRAME HYPOTHESES (added 2026-06-25, thread 31).** The cert was UNDER-HYPOTHESIZED: with bare
    -- `Pf, Qf, J` the conclusion is FALSE (`P0 = Pf first` need not be a unit, so `Pi·P0 = 1` fails;
    -- the corner need not normalize; `P00` need not be invertible). These seven facts are exactly the
    -- components of the `deepestPoint_frame_pivot_exists` bundle the caller already holds; they make
    -- the statement TRUE. `hcorner` is in the bundle's native last-layer typing (`(lastLayer).succ`
    -- column width + `pivotJSucc J`) so it matches `framedParamsPivot_last`'s reindex without a cast.
    (hPunit : ∀ s : Fin L, IsUnit (Pf s)) (hQunit : ∀ s : Fin L, IsUnit (Qf s))
    (hQf0 : Qf (firstLayer hL)
      = (1 : Matrix (Fin (H (firstLayer hL).succ)) (Fin (H (firstLayer hL).succ)) ℝ))
    (hPfL : Pf (lastLayer hL)
      = (1 : Matrix (Fin (H (lastLayer hL).castSucc)) (Fin (H (lastLayer hL).castSucc)) ℝ))
    (hNF : ∀ s : Fin L, (s : ℕ) + 1 ≠ L →
      Pf s * (deepestPoint H r B hB hr hL s) * Qf s
        = Matrix.of (fun (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) =>
            if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0))
    (hcorner : Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        ((deepestPoint H r B hB hr hL (lastLayer hL)) * Qf (lastLayer hL))
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    -- **INTERIOR-FRAME TRIVIALITY** (the `endpoint_telescoping` interface-collapse input, thread 31).
    -- Every strictly-interior interface `(Qf s, Pf (s+1))` is `(1, 1)`. At `L = 2` the single interface
    -- `s = 0` is `(Qf (firstLayer) = 1, Pf (lastLayer) = 1) = (hQf0, hPfL)`; for `L ≥ 3` the strict-
    -- interior frames are likewise trivial (the deepest interior layer IS the corner). Stated as a
    -- hypothesis (the generic rank-normal-form frame `deepestPoint_frame` need not be the identity on the
    -- interior even though the layer is the corner; the caller supplies the identity-interior choice).
    (hinterface : ∀ (s : Fin L) (_ : (s : ℕ) + 1 < L),
      Qf s = (1 : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) ∧
        Pf ⟨(s : ℕ) + 1, by omega⟩ = (1 : Matrix (Fin (H (⟨(s : ℕ) + 1, by omega⟩ : Fin L).castSucc))
          (Fin (H (⟨(s : ℕ) + 1, by omega⟩ : Fin L).castSucc)) ℝ)) :
    ∃ (P0 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
      (QL : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ)
      (Pi : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
      (Qi : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ)
      (t γ₁ γ₂ δ₁ δ₂ : ℝ),
      Pi * P0 = 1 ∧ QL * Qi = 1 ∧ 0 < γ₁ ∧ 0 < γ₂ ∧ 0 < δ₁ ∧ 0 < δ₂ ∧
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
            -- **L2-PIN2 (2026-06-25), conjunct (b) — COMPARABILITY (thread 31 r2-frontpivot-cert + a
            -- DECORRELATED Codex `xhigh` germ re-derivation, 2026-06-25).** The earlier candidate EQUALITY
            -- `∑deepestEFull² = Sreg` is FALSE for a non-front pivot `J` (the last layer carries the column
            -- permutation `π_J`; numeric witness `17.98 ≠ 23.65`). What HOLDS is the two-sided
            -- COMPARABILITY `δ₁·Sreg ≤ ∑deepestEFull² ≤ δ₂·Sreg` with `Sreg = ∑(P00−1)² + ∑P01² + ∑P10²`:
            -- both `∑deepestEFull²(split w)` and `Sreg(w)` are continuous, vanish at `w0`
            -- (`deepestEFull_base`), and have the SAME leading quadratic form in the deviation up to the
            -- invertible column map `π_J·QL` — so they are uniformly comparable on a small `U`. This is the
            -- shape `deepest_loss_squeeze` folds (it absorbs `δ₁, δ₂` into its endpoint-frame constants; it
            -- never needed the equality). The germ/Taylor derivation of `δ₁, δ₂` is the genuine open
            -- content (`deepestEFull_sq_comparable_Sreg`, the named atom). **CAVEAT (Codex `xhigh`, decorr.,
            -- 2026-06-25): the cert's "via banked invertible-conjugation machinery" route is over-optimistic
            -- — the pivot-read summand sits INSIDE the product, so this is NOT a clean pointwise
            -- `conjugation_frobenius_comparable`; it needs an `fderiv` quadratic-form comparison + Taylor
            -- remainder absorption (an unbanked germ argument), still open.**
            ∧ (δ₁ * (((∑ i, ∑ j, ((P00 - 1) i j) ^ 2) + (∑ i, ∑ j, (P01 i j) ^ 2))
                    + (∑ i, ∑ j, (P10 i j) ^ 2))
                ≤ (∑ i, (deepestEFull H r hr hL J Pf Qf (split w)) i ^ 2))
            ∧ ((∑ i, (deepestEFull H r hr hL J Pf Qf (split w)) i ^ 2)
                ≤ δ₂ * (((∑ i, ∑ j, ((P00 - 1) i j) ^ 2) + (∑ i, ∑ j, (P01 i j) ^ 2))
                    + (∑ i, ∑ j, (P10 i j) ^ 2)))
            ∧ ((∑ i, ∑ j, ((P10 * ⅟P00 * P01) i j) ^ 2)
                ≤ t ^ 2 * (((∑ i, ∑ j, ((P00 - 1) i j) ^ 2) + (∑ i, ∑ j, (P01 i j) ^ 2))
                    + (∑ i, ∑ j, (P10 i j) ^ 2)))
            -- **FOLDED CORE COMPARABILITY (L2-PIN2 corrected, thread 31, 2026-06-25).** The earlier
            -- UNIFORM two-sided MULTIPLICATIVE form `∑Rcore² ≤ γ₂·coreΦ ∧ coreΦ ≤ γ₁·∑Rcore²` is
            -- **FALSE for M > 1** (decorrelated Codex `xhigh` + numeric witness `s5c_germ_counterex.py`:
            -- the germ path `W = I+η·E₁₂`, `S0 = ε·e₁(e₁ᵀ−η·e₂ᵀ)`, `S1 = ε·e₂e₁ᵀ` gives `Rcore = 0`
            -- but `∏S = −ε²η·E₁₁ ≠ 0`, so `coreΦ ≤ γ₁·0` is violated arbitrarily near the deepest point).
            -- The TRUE germ form is the **regular-energy-FOLDED** comparability `Sreg + ∑Rcore² ≍
            -- Sreg + coreΦ` (the `core_comparability_squeeze` shape, via the built S5c germ atom
            -- `schur_core_germ_comparability` + the `|∑Rcore² − coreΦ| ≤ C·Sreg` charge): with
            -- `Sreg := ∑(P00−1)² + ∑P01² + ∑P10²` and `Score := ∑Rcore²`, both sides fold `Sreg`.
            ∧ ((((∑ i, ∑ j, ((P00 - 1) i j) ^ 2) + (∑ i, ∑ j, (P01 i j) ^ 2))
                    + (∑ i, ∑ j, (P10 i j) ^ 2))
                  + (∑ i, ∑ j, ((P11 - P10 * ⅟P00 * P01) i j) ^ 2)
                ≤ γ₂ * (((((∑ i, ∑ j, ((P00 - 1) i j) ^ 2) + (∑ i, ∑ j, (P01 i j) ^ 2))
                    + (∑ i, ∑ j, (P10 i j) ^ 2)))
                  + deepestCoreF H r (deepestCoreAbsorb H r hr hL (split w)).2.1))
            ∧ (((((∑ i, ∑ j, ((P00 - 1) i j) ^ 2) + (∑ i, ∑ j, (P01 i j) ^ 2))
                    + (∑ i, ∑ j, (P10 i j) ^ 2)))
                  + deepestCoreF H r (deepestCoreAbsorb H r hr hL (split w)).2.1
                ≤ γ₁ * ((((∑ i, ∑ j, ((P00 - 1) i j) ^ 2) + (∑ i, ∑ j, (P01 i j) ^ 2))
                    + (∑ i, ∑ j, (P10 i j) ^ 2))
                  + (∑ i, ∑ j, ((P11 - P10 * ⅟P00 * P01) i j) ^ 2))) := by
  -- **ASSEMBLY (B (front-pivot WLOG) route, 2026-06-25, thread 31; partial — 2 named `sorry`s left).**
  -- The cert is stated TRUE (the frame hypotheses + `hfront` + `hL2`/`hpos`/`hinterface`). Under the
  -- FRONT pivot (`hfront : J = frontEmbed`), `pivotThr J = rThr`, so the last-layer column-permutation
  -- `π_J` is the identity. **LANDED this tide:** the endpoint-frame units + `Pi·P0 = 1`/`QL·Qi = 1`; the
  -- Frobenius positivity `hKP_pos`/`hKi_pos`; S1 (non-last round-trip); the CLEAN last-layer frame
  -- `hS1'_front` (front pivot, `reindex_fromBlocks_reads_eq_deviation` applies); the CLEAN per-`w`
  -- telescope `hS2_front : prod (F w) = P0·prod(A w)·QL` (every `w`, via `endpoint_telescoping_eq`); the
  -- per-`w` block split `hRegBlocks` (`reindex(prod (F w)) = fromBlocks 1 0 0 0 + reindex(P0·(prod−B)·QL)`
  -- via `hS3b`); the `hproducer` conjuncts (a) `hconj` (`fromBlocks_toBlocks`), (b) the EXACT reg energy
  -- `∑deepestEFull² = Sreg` (`hbexact`, via `deepestEFull_sq_sum_eq_blocks` — `δ₁ = δ₂ = 1`), S5a
  -- `Invertible P00` (banked `eventually_P00_invertible`), AND (c) the leak `∑(P10⅟P00 P01)² ≤ Sreg`
  -- (S5b `eventually_leak`, landed this tide — continuity of `(P00)⁻¹` at the unit `P00 w0 = 1` +
  -- `leak_frobenius_bound` + `∑P10² ≤ Sreg`, `t = 1`), with the coupled `U := S5a-set ∩ S5b-set`
  -- (`Filter.inter_mem`). **STILL OPEN (2 named `sorry`s in `hproducer`, CORRECT statements,
  -- pivot-AGNOSTIC):** the folded core (d')/(e') (the per-layer↔global Schur charge — the structural
  -- bridge `Rcore = P11 − P10⅟P00 P01 ↔ deepestCoreF (deepestCoreAbsorb (split w)).2.1` via the
  -- block-LDU `Rcore = (∏ core)·(1−K)·(…)`, UNBUILT; with the additive charge
  -- `|frobSq Rcore − coreΦ| ≤ C·Sreg` from the BANKED `schur_core_germ_comparability` it closes at
  -- `γ₁ = γ₂ = 1+C`). (`hS1'`, `hframe0`, `hS2_w0` are kept as the subsumed basepoint path feeding
  -- `hS3b`.)
  classical
  set w0 := (paramsEquivFlat H) (deepestPoint H r B hB hr hL) with hw0
  -- The raw (un-framed) parameter tuple at `w` and the full framed reconstruction of `split w`.
  set A : (Fin (flatDim H) → ℝ) → Params H := fun w => (paramsEquivFlat H).symm w with hA
  set F : (Fin (flatDim H) → ℝ) → Params H :=
    fun w => framedParamsPivot H r hr hL J Pf Qf (split w) with hF
  -- **Affine bridge** (`symm (w − w0) = symm w − deepest`, per layer): `paramsEquivFlat.symm` is
  -- ℝ-linear (`paramsEquivFlatLinear`), so it preserves subtraction; `symm w0 = deepest` (round-trip).
  have haffine : ∀ w (s : Fin L),
      ((paramsEquivFlat H).symm (w - w0)) s
        = ((paramsEquivFlat H).symm w) s - (deepestPoint H r B hB hr hL) s := by
    -- `paramsEquivFlat.symm` agrees with the ℝ-linear `paramsEquivFlatLinear.symm` (same forward fn).
    have hsymm : ∀ y, (paramsEquivFlat H).symm y = (paramsEquivFlatLinear H).symm y := by
      intro y
      apply (paramsEquivFlatLinear H).injective
      rw [(paramsEquivFlatLinear H).apply_symm_apply,
        show (paramsEquivFlatLinear H) ((paramsEquivFlat H).symm y)
          = (paramsEquivFlat H) ((paramsEquivFlat H).symm y) from
          congrFun (paramsEquivFlatLinear_coe H) _,
        (paramsEquivFlat H).apply_symm_apply]
    intro w s
    have hsub : (paramsEquivFlat H).symm (w - w0)
        = (paramsEquivFlat H).symm w - (paramsEquivFlat H).symm w0 := by
      rw [hsymm (w - w0), hsymm w, hsymm w0]; exact map_sub (paramsEquivFlatLinear H).symm w w0
    have hw0symm : (paramsEquivFlat H).symm w0 = deepestPoint H r B hB hr hL := by
      rw [hw0]; exact (paramsEquivFlat H).symm_apply_apply _
    rw [hsub, hw0symm]; rfl
  -- **S1 — per-layer round-trip, NON-last layers**: `framedParamsPivot_of_ne_last` ▸ `framedParams`/
  -- `framedLayer` def ▸ the threshold corner is the `corM` shape (`reindex_fromBlocks_one_eq_corM`) =
  -- `Pf·deepest·Qf` (`hNF`) ▸ the reg/core read block reindex is the raw deviation
  -- (`reindex_fromBlocks_reads_eq_deviation`, via `hsplit : split w = deepestSplit w0 w`) ▸ the affine
  -- bridge ▸ distribute `Pf · (deepest + (symm(w−w0))) · Qf = Pf · symm w · Qf`.
  have hS1 : ∀ w (s : Fin L), s ≠ lastLayer hL →
      F w s = Pf s * (A w) s * Qf s := by
    intro w s hs
    have hsne : (s : ℕ) + 1 ≠ L := by
      intro h; exact hs (Fin.ext (by simp only [lastLayer]; omega))
    -- `F w s = framedLayer s (Pf s) (Qf s) (readX) (readY) (readZ) (coreRead)`.
    have hFs : F w s
        = Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
              (rThresholdSplit r (H s.succ) (hr s.succ)).symm
              (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
            + Pf s * Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
                (rThresholdSplit r (H s.succ) (hr s.succ)).symm
                (Matrix.fromBlocks (readX H r hr hL ((split w).1, (split w).2.2) s)
                  (readY H r hr hL ((split w).1, (split w).2.2) s)
                  (readZ H r hr hL ((split w).1, (split w).2.2) s)
                  ((paramsEquivFlat (deepestM H r)).symm (split w).2.1 s)) * Qf s := by
      rw [hF]; simp only
      rw [framedParamsPivot_of_ne_last H r hr hL J Pf Qf (split w) s hs, framedParams, framedLayer]
    rw [hFs]
    -- Corner term `= Pf s · deepest_s · Qf s` (`reindex_fromBlocks_one_eq_corM` ▸ `hNF`).
    rw [reindex_fromBlocks_one_eq_corM r (H s.castSucc) (H s.succ) (hr s.castSucc) (hr s.succ),
      ← hNF s hsne]
    -- Read block `= raw deviation (symm (w − w0))_s` (`reindex_fromBlocks_reads_eq_deviation`, hsplit).
    rw [show ((split w).1, (split w).2.2)
          = ((deepestSplit H r hr hL w0 w).1, (deepestSplit H r hr hL w0 w).2.2) by rw [hsplit w],
      show (split w).2.1 = (deepestSplit H r hr hL w0 w).2.1 by rw [hsplit w],
      reindex_fromBlocks_reads_eq_deviation H r hr hL w0 w s]
    -- Distribute + affine bridge: `Pf·deepest·Qf + Pf·(symm(w−w0))·Qf = Pf · symm w · Qf`.
    rw [hA]; simp only [haffine w s, Matrix.mul_sub, Matrix.sub_mul]
    abel
  -- **S1' — last-layer pivot-column variant.** **REFUTED AS ORIGINALLY STATED (thread 31, pen-and-paper
  -- + decorrelated Codex, 2026-06-25; `hs1prime-verdict.md`).** `framedParamsPivot`'s last layer reindexes
  -- the COLUMN side by the PIVOT split `pivotThresholdSplit … J`, but the gauge reads are J-INDEPENDENT
  -- threshold-column decodes (`readY/readT_deepestSplit_raw` land block-col `inr q ↦` deviation col
  -- `r+q`). So the reads term equals the deviation `(symm(w−w0)) last` with its columns PERMUTED by
  -- `π_J(j) = (rThr).symm (pivotThr J · j)` — NOT the raw deviation. The clean `F last = Pf·(symm w)·Qf`
  -- is FALSE for a non-front pivot `J` (counterexample `H=(1,1,2)`, `J 0 = 1`: columns swapped). The
  -- TRUE statement is the permuted form below. (The cert's option-α premise — "the role index is split-
  -- independent so the decoders agree per-entry" — is the error: the reads ARE threshold, but
  -- `framedParamsPivot_last` PLACES them at pivot columns.) The fix (verdict option A) is to fold the
  -- orthogonal column-permutation `Pπ` (`colPerm_J M = M·Pπ`) into the endpoint `QL` + the `B`-pivot
  -- normalization — it should cancel against the SAME outer `reindex(rThr, pivotThr J)` carried on BOTH
  -- the energy (`deepestEFull`) and loss (`Sreg`) sides; that cancellation is genuine new design work
  -- (verify BEFORE re-stating), so this stays a precisely-stated `sorry`.
  have hS1' : ∀ w, F w (lastLayer hL)
      = Pf (lastLayer hL) * (deepestPoint H r B hB hr hL (lastLayer hL)) * Qf (lastLayer hL)
        + Pf (lastLayer hL)
          * (Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
              (pivotThresholdSplit r (H (lastLayer hL).succ) (hr _) (pivotJSucc H r hL J)).symm
              (Matrix.fromBlocks
                (readX H r hr hL ((split w).1, (split w).2.2) (lastLayer hL))
                (readY H r hr hL ((split w).1, (split w).2.2) (lastLayer hL))
                (readZ H r hr hL ((split w).1, (split w).2.2) (lastLayer hL))
                ((paramsEquivFlat (deepestM H r)).symm (split w).2.1 (lastLayer hL))))
          * Qf (lastLayer hL) := by
    intro w
    -- `F w last = framedParamsPivot (split w) last`, unfolded by `framedParamsPivot_last` into the
    -- raw corner `reindex(fromBlocks 1 0 0 0)` plus the pivot-reindexed reads `Pf·reads·Qf`.
    rw [hF]; simp only
    rw [framedParamsPivot_last H r hr hL J Pf Qf (split w)]
    -- The raw corner `reindex(rThr.symm, pivotThr.symm)(fromBlocks 1 0 0 0)` equals `deepest_last · Qf`
    -- by inverting `hcorner`, and `Pf_last = 1` (`hPfL`) makes it `Pf_last · deepest_last · Qf_last`.
    have hcornerInv : Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
          (pivotThresholdSplit r (H (lastLayer hL).succ) (hr _) (pivotJSucc H r hL J)).symm
          (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
        = deepestPoint H r B hB hr hL (lastLayer hL) * Qf (lastLayer hL) := by
      rw [← hcorner, ← Matrix.reindex_symm, Equiv.symm_apply_apply]
    rw [hcornerInv]
    simp only [hPfL, Matrix.one_mul]
  -- **S1'-FRONT — the CLEAN last-layer frame** (B (front-pivot WLOG), b-wlog-spec, 2026-06-25). Under
  -- the front pivot `hfront : J = frontEmbed`, the last-layer column reindex `pivotThr (pivotJSucc J)`
  -- IS `rThr` (`pivotThresholdSplit_pivotJSucc_frontEmbed`), so the pivot reindex of the reads in `hS1'`
  -- collapses to the THRESHOLD reindex, and the SAME `reindex_fromBlocks_reads_eq_deviation` (last
  -- layer) the non-last `hS1` uses applies — the reads = the raw deviation `(symm(w−w0)) last`. The
  -- column-permutation `π_J` that refutes the general-`J` clean frame is the identity here. The result
  -- is the clean frame `F w last = Pf last · (A w) last · Qf last` for EVERY `w` (not just `w0`).
  have hS1'_front : ∀ w, F w (lastLayer hL)
      = Pf (lastLayer hL) * (A w) (lastLayer hL) * Qf (lastLayer hL) := by
    intro w
    -- The front-pivot collapse `pivotThr (pivotJSucc J) = rThr` on the last-layer column width.
    have hsplit_eq : pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J)
        = rThresholdSplit r (H ((lastLayer hL).succ)) (hr _) := by
      rw [hfront]; exact pivotThresholdSplit_pivotJSucc_frontEmbed H r hr hL
    rw [hS1' w, hsplit_eq]
    -- `H ((lastLayer).succ) = H (Fin.last L)`, so `(lastLayer).succ = Fin.last L` as the layer index;
    -- the read reindex matches `reindex_fromBlocks_reads_eq_deviation` at `s = lastLayer hL`.
    rw [show ((split w).1, (split w).2.2)
          = ((deepestSplit H r hr hL w0 w).1, (deepestSplit H r hr hL w0 w).2.2) by rw [hsplit w],
      show (split w).2.1 = (deepestSplit H r hr hL w0 w).2.1 by rw [hsplit w],
      reindex_fromBlocks_reads_eq_deviation H r hr hL w0 w (lastLayer hL)]
    -- Distribute + affine bridge (identical to `hS1`'s closing step).
    rw [hA]; simp only [haffine w (lastLayer hL), Matrix.mul_sub, Matrix.sub_mul]
    abel
  -- The CLEAN per-`w` frame for EVERY layer (front-pivot): non-last via `hS1`, last via `hS1'_front`.
  have hframe_front : ∀ w (s : Fin L), F w s = Pf s * (A w) s * Qf s := by
    intro w s
    by_cases hs : s = lastLayer hL
    · rw [hs]; exact hS1'_front w
    · exact hS1 w s hs
  -- **S0/interface — adjacent interior frames are identity** (`framedbody-cert.md` S0/S2): the telescope
  -- `hinterface` input is now a hypothesis (see the signature) — every strictly-interior interface
  -- `(Qf s, Pf (s+1))` is `(1, 1)`, the input `endpoint_telescoping_eq` consumes for the interface collapse.
  -- **S2 — telescope** (`endpoint_telescoping_eq`, the WITNESSED variant). The boundary frames are the
  -- CANONICAL endpoint casts `endpointP0 H hL Pf`, `endpointQL H hL Qf` — they depend only on `Pf, Qf`
  -- (NOT on `A`/`C`), so the SAME `P0, QL` serve every `w`.
  set P0 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ := endpointP0 H hL Pf with hP0def
  set QL : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ := endpointQL H hL Qf with hQLdef
  -- `P0, QL` are units: a type-cast of `Pf (firstLayer)`/`Qf (lastLayer)`, units (`hPunit`/`hQunit`).
  have hP0unit : IsUnit P0 := by rw [hP0def]; exact isUnit_endpointP0 H hL Pf (hPunit _)
  have hQLunit : IsUnit QL := by rw [hQLdef]; exact isUnit_endpointQL H hL Qf (hQunit _)
  -- **`hframe` AT THE DEEPEST GAUGE `w0` ONLY** (SOUND): at `w0` the deviation is `0` (`split w0 = 0`),
  -- so the refuted column-permutation `π_J` acts trivially (`colPerm_J 0 = 0`), and `F w0 s = Pf s ·
  -- deepest s · Qf s` for EVERY layer (last layer via the corner `hcorner` + `hPfL`, non-last via S1).
  -- The general-`w` `hframe` is FALSE on the last layer (hS1'); only the `w0` instance is needed below
  -- (`hS3b` is a basepoint fact, and the general-`w` energy identity is the `hproducer` `sorry`).
  have hAw0 : A w0 = deepestPoint H r B hB hr hL := by
    rw [hA]; simp only; rw [hw0]; exact (paramsEquivFlat H).symm_apply_apply _
  have hsplit0 : split w0 = 0 := by
    rw [hsplit w0, hw0]
    exact (deepestSplit_mp_basepoint H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL))).2
  have hframe0 : ∀ s : Fin L, F w0 s = Pf s * (A w0) s * Qf s := by
    intro s
    by_cases hs : s = lastLayer hL
    · -- last layer at `w0`: `split w0 = 0` ⟹ `F w0 last = framedParamsRegPivot 0 last = corner`
      -- (`framedParamsPivot_coreZero` ▸ `framedParamsRegPivot_zero_last`), and the corner
      -- `reindex(rThr.symm, pivotThr.symm)(fromBlocks 1 0 0 0) = deepest_last · Qf_last` (`hcorner`,
      -- reindex.symm-cancel), with `Pf_last = 1` (`hPfL`) and `A w0 last = deepest_last`.
      subst hs
      rw [hF]; simp only
      rw [hsplit0,
        show ((0 : DeepestSplit H r (deepestNGauge H r)))
          = (((0 : Fin (deepestNReg H r) → ℝ), (0 : Fin (flatDim (deepestM H r)) → ℝ),
              (0 : Fin (deepestNGauge H r) → ℝ)) : DeepestSplit H r (deepestNGauge H r)) from rfl,
        framedParamsPivot_coreZero H r hr hL J Pf Qf 0 0,
        show (((0 : Fin (deepestNReg H r) → ℝ), (0 : Fin (deepestNGauge H r) → ℝ))
            : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
          = (0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) from rfl,
        framedParamsRegPivot_zero_last H r hr hL J Pf Qf]
      -- corner term `reindex(rThr.symm, pivotThr.symm)(fromBlocks 1 0 0 0) = deepest_last · Qf_last`.
      have hcornerInv : Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
            (pivotThresholdSplit r (H (lastLayer hL).succ) (hr _) (pivotJSucc H r hL J)).symm
            (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
          = deepestPoint H r B hB hr hL (lastLayer hL) * Qf (lastLayer hL) := by
        rw [← hcorner, ← Matrix.reindex_symm, Equiv.symm_apply_apply]
      rw [hcornerInv, hAw0, hPfL, Matrix.one_mul]
    · -- non-last layer at `w0`: `S1` gives `F w0 s = Pf s · (A w0) s · Qf s` directly.
      exact hS1 w0 s hs
  have hS2_w0 : prod H (F w0) = P0 * prod H (A w0) * QL := by
    rw [hP0def, hQLdef]
    exact endpoint_telescoping_eq H hL (A w0) (F w0) Pf Qf hframe0 hinterface
  -- **S3b — B-normalization** (`framedbody-cert.md` S3b): `reindex(P0·B·QL) = fromBlocks 1 0 0 0`, via
  -- `B = prod(deepestPoint)` ▸ telescope-of-deepest at `w0` (`hS2_w0`, the SOUND basepoint instance) ▸
  -- `F w0 = framedParamsPivot (split w0)` with `split w0 = 0` collapses to `framedParamsRegPivot 0`
  -- (`framedParamsPivot_coreZero`) ▸ product-of-corners (`reindex_prodAux_framedParamsRegPivot_zero`).
  have hS3b : Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (P0 * B * QL)
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 := by
    -- `B = prod(deepest)` (the fibre membership `IsDeepLayers.1`).
    have hBprod : B = prod H (deepestPoint H r B hB hr hL) :=
      (deepestPoint_isDeep H r B hB hr hL).1.symm
    -- `P0·B·QL = P0·prod(deepest)·QL = P0·prod(A w0)·QL = prod (F w0)` (hS2_w0, reversed).
    have hstep : P0 * B * QL = prod H (F w0) := by
      rw [hBprod, ← hAw0, ← hS2_w0]
    rw [hstep, hF]; simp only
    -- `F w0 = framedParamsPivot (split w0) = framedParamsPivot 0 = framedParamsRegPivot 0`.
    rw [hsplit0,
      show ((0 : DeepestSplit H r (deepestNGauge H r)))
        = (((0 : Fin (deepestNReg H r) → ℝ), (0 : Fin (flatDim (deepestM H r)) → ℝ),
            (0 : Fin (deepestNGauge H r) → ℝ)) : DeepestSplit H r (deepestNGauge H r)) from rfl,
      framedParamsPivot_coreZero H r hr hL J Pf Qf 0 0,
      show (((0 : Fin (deepestNReg H r) → ℝ), (0 : Fin (deepestNGauge H r) → ℝ))
          : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
        = (0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) from rfl]
    exact reindex_prodAux_framedParamsRegPivot_zero H r hr hL hL2 J Pf Qf
  -- **S2-FRONT — the CLEAN per-`w` telescope** (B (front-pivot WLOG), 2026-06-25). Under the front
  -- pivot the per-layer frame `hframe_front` is clean for EVERY layer (last via `hS1'_front`), so the
  -- WITNESSED endpoint telescope holds for every `w` (not just `w0`): `prod (F w) = P0·prod(A w)·QL`.
  -- This is exactly what makes the (b)-conjunct EXACT (the framed-product block reads = the loss blocks).
  have hS2_front : ∀ w, prod H (F w) = P0 * prod H (A w) * QL := by
    intro w
    rw [hP0def, hQLdef]
    exact endpoint_telescoping_eq H hL (A w) (F w) Pf Qf (hframe_front w) hinterface
  -- **The per-`w` reg-block identity** (the (b)-EXACT bridge): the reindexed framed product splits as
  -- the corner `fromBlocks 1 0 0 0` plus the reindexed conjugated residual `P0·(prod(A w)−B)·QL`. From
  -- the clean telescope `hS2_front` + `P0·prod(A w)·QL = P0·B·QL + P0·(prod(A w)−B)·QL` + `hS3b`.
  have hRegBlocks : ∀ w, Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (prod H (F w))
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0
        + Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (P0 * (prod H (A w) - B) * QL) := by
    intro w
    -- `P0·prod(A w)·QL = P0·B·QL + P0·(prod(A w)−B)·QL` (distribute; `prod(A w) = B + (prod(A w)−B)`).
    have hsplitprod : P0 * prod H (A w) * QL
        = P0 * B * QL + P0 * (prod H (A w) - B) * QL := by
      rw [Matrix.mul_sub, Matrix.sub_mul, add_sub_cancel]
    rw [hS2_front w, hsplitprod]
    -- `reindex` is additive (`reindex_apply` = `submatrix .symm .symm`, `submatrix_add`); the corner
    -- summand `reindex(P0·B·QL) = fromBlocks 1 0 0 0` (hS3b), the deviation summand matches the RHS.
    have hadd : Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (P0 * B * QL + P0 * (prod H (A w) - B) * QL)
          = Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (P0 * B * QL)
            + Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (P0 * (prod H (A w) - B) * QL) := by
      ext i j
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply]
    rw [hadd, hS3b]
  -- The inverses `Pi, Qi` from the units `hP0unit`, `hQLunit`. `Pi := P0⁻¹` (the unit's inverse),
  -- `Pi · P0 = 1`; similarly `Qi := QL⁻¹`, `QL · Qi = 1`.
  obtain ⟨P0u, hP0u⟩ := hP0unit
  obtain ⟨QLu, hQLu⟩ := hQLunit
  set Pi : Matrix (Fin (H 0)) (Fin (H 0)) ℝ := (↑P0u⁻¹ : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) with hPidef
  set Qi : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ :=
    (↑QLu⁻¹ : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ) with hQidef
  have hPP : Pi * P0 = 1 := by
    rw [hPidef, ← hP0u]; exact (Units.inv_mul P0u)
  have hQQ : QL * Qi = 1 := by
    rw [hQidef, ← hQLu]; exact (Units.mul_inv QLu)
  -- Frobenius positivity of the endpoint conjugation constants: `P0, QL` (and their inverses `Pi, Qi`)
  -- are units, hence `≠ 0`, so their squared-Frobenius energies are strictly positive — over a NONEMPTY
  -- boundary index (`0 < H 0`, `0 < H (last L)` from `hpos`). `P0`/`Qi` are right factors of a `· = 1`
  -- product, `Pi`/`QL` left factors; all four are nonzero (`1 ≠ 0` over the nonempty index).
  have h0pos : 0 < H 0 := lt_of_le_of_lt (Nat.zero_le r) (hpos 0)
  have hLpos : 0 < H (Fin.last L) := lt_of_le_of_lt (Nat.zero_le r) (hpos (Fin.last L))
  -- The endpoint `QL/Qi` factors enter the constant column-major (`∑ j ∑ k (· k j)²`); the row-major
  -- positivity transfers by `Finset.sum_comm` (the double sum is symmetric in the two index orders).
  have hswap : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ),
      (∑ j, ∑ k, (M k j) ^ 2) = (∑ i, ∑ k, (M i k) ^ 2) := by
    intro n M; rw [Finset.sum_comm]
  have hKP_pos : 0 < (∑ i, ∑ k, (P0 i k) ^ 2) * (∑ j, ∑ k, (QL k j) ^ 2) := by
    have hP0ne : P0 ≠ 0 := ne_zero_of_mul_eq_one_left h0pos Pi P0 hPP
    have hQLne : QL ≠ 0 := ne_zero_of_mul_eq_one_right hLpos QL Qi hQQ
    rw [hswap QL]
    exact mul_pos (frob_sq_sum_pos_of_ne_zero P0 hP0ne) (frob_sq_sum_pos_of_ne_zero QL hQLne)
  have hKi_pos : 0 < (∑ i, ∑ k, (Pi i k) ^ 2) * (∑ j, ∑ k, (Qi k j) ^ 2) := by
    have hPine : Pi ≠ 0 := ne_zero_of_mul_eq_one_right h0pos Pi P0 hPP
    have hQine : Qi ≠ 0 := ne_zero_of_mul_eq_one_left hLpos QL Qi hQQ
    rw [hswap Qi]
    exact mul_pos (frob_sq_sum_pos_of_ne_zero Pi hPine) (frob_sq_sum_pos_of_ne_zero Qi hQine)
  -- **PER-`w` PRODUCER** (`framedbody-cert.md` S4/S5): the leak constant `t` (S5b) and the core
  -- comparability constants `γ₁, γ₂` (S5c) are UNIFORM over the neighborhood `U`, so they are chosen
  -- here (BEFORE the `∀ w`), together with `U ∈ 𝓝 w0` and the per-`w` block witnesses. The `𝓝 w0` set
  -- `U` is the intersection of S5a's `det P00 ≠ 0` open set, S5b's leak-smallness nbhd, and S5c's
  -- germ-comparability nbhd; for each `w ∈ U` the 4 blocks are the `toBlocks` of
  -- `reindex(P0·(prod(A w) − B)·QL)`, `hconj` is `Matrix.fromBlocks_toBlocks`, the reg-energy (S4) packs
  -- via `regResidualPack` (`deepestEPivot_sq_sum_eq_blocks` for `deepestEFull`), and the leak/core are
  -- the banked S5b/S5c estimates. GENUINE new content (the `𝓝` construction + S4/S5a/S5b/S5c geometry).
  -- **PIVOT-PERMUTATION CAVEAT (thread 31, `hs1prime-verdict.md`):** the S4 reg-energy identity
  -- `∑deepestEFull² = Sreg` (conjunct (b)) presupposes the per-`w` telescope `prod(F w) = P0·prod(A w)·QL`
  -- which is FALSE on the last layer for a non-front pivot `J` — the last factor carries the column-
  -- permutation `π_J` (refuted hS1'). The FINAL identity is expected to survive (the SAME outer
  -- `reindex(rThr, pivotThr J)` is on BOTH `deepestEFull` and `Sreg`, so `π_J` should cancel), but the
  -- producer's S4 step must thread that cancellation (verdict option A: fold the orthogonal `Pπ` into
  -- `QL`/the `B`-pivot normalization). This is the genuine open design (verify the cancellation).
  --
  -- **S5c STATUS — the abstract germ atom is BUILT** (`DeepestSchurComparability.lean`,
  -- `schur_core_germ_comparability`): the exact remainder identity `Rcore − ∏S = −S0·K·S1`, the
  -- Frobenius sub-multiplicative remainder bound `frobSq(Rcore−∏S) ≤ frobSq S0·frobSq K·frobSq S1`, and
  -- the difference-of-squared-Frobenius split `frobSq Rcore = frobSq ∏S + 2·⟨∏S, Rcore−∏S⟩ +
  -- frobSq(Rcore−∏S)` with the cross term Cauchy–Schwarz-bounded. All network-free, axiom-clean.
  --
  -- **KILL-CONDITION FOUND (thread 31, 2026-06-25; decorrelated Codex `xhigh` + numeric witness
  -- `/tmp/s5c_germ_counterex.py`):** conjuncts (d)/(e) BELOW — the UNIFORM two-sided MULTIPLICATIVE
  -- comparability `∑Rcore² ≤ γ₂·coreΦ` AND `coreΦ ≤ γ₁·∑Rcore²` over a fixed `U` — are **FALSE for
  -- M > 1** (the matrix core). GERM counterexample (all deviations → 0): `W = I + η·E₁₂` (a TILTED
  -- kernel, realizable by `Z1 = √η·e₁`, `Y0 = −√η·e₂ᵀ`, both `O(√η) → 0`, with `A = a0a1 = I`),
  -- `S1 = ε·e₂e₁ᵀ`, `S0 = ε·e₁(e₁ᵀ − η·e₂ᵀ)`: then `Rcore = S0·W·S1 = 0` EXACTLY while
  -- `∏S = S0·S1 = −ε²η·E₁₁ ≠ 0`, so `coreΦ = ε⁴η² > 0` but `∑Rcore² = 0` — conjunct (e)
  -- `coreΦ ≤ γ₁·0` is violated for every finite `γ₁`, arbitrarily close to the deepest point. (My first
  -- random-direction numerics MISSED this — the witness is a measure-zero aligned `S0 ⟂ W·S1` direction;
  -- the empty generic hunt is not a proof. The cert's `W[k,k]=0` witness is off-germ, but this
  -- tilted-kernel one is a genuine germ path.)
  --
  -- **RESTATED (thread 31, 2026-06-25):** the multiplicative (d)/(e) are now REPLACED by the FOLDED
  -- germ form `Sreg + ∑Rcore² ≤ γ₂·(Sreg + coreΦ)` and `Sreg + coreΦ ≤ γ₁·(Sreg + ∑Rcore²)` (matching
  -- the parent cert's restated conclusion + `deepest_loss_squeeze`'s rewired squeeze). The folded form is
  -- the `core_comparability_squeeze` shape, derivable from the built S5c germ atom
  -- `schur_core_germ_comparability` + the `|∑Rcore² − coreΦ| ≤ C·Sreg` charge (`Y0,Z1 ≤ √Sreg`).
  --
  -- **CONJUNCT (b) — EXACT under the FRONT pivot (B (front-pivot WLOG) route, this tide, 2026-06-25).**
  -- The earlier candidate EQUALITY `∑deepestEFull² = Sreg` is FALSE for a non-front pivot `J` (the last
  -- layer carries the column-permutation `π_J`; numeric `17.98 ≠ 23.65`). With the front pivot
  -- (`hfront : J = frontEmbed`), `pivotThr J = rThr` and `π_J = id`, so the per-`w` telescope
  -- `prod (F w) = P0·prod(A w)·QL` is CLEAN for every `w` (`hframe_front`/`hS2_front`), and the
  -- reindexed framed product splits as `fromBlocks 1 0 0 0 + reindex(P0·(prod(A w)−B)·QL)`
  -- (`hRegBlocks`, via `hS3b`). Hence `∑deepestEFull(split w)² = Sreg(w)` EXACTLY (`hbexact` below,
  -- via `deepestEFull_sq_sum_eq_blocks`) — `δ₁ = δ₂ = 1`. No comparability, no `π_J`-cancellation, no
  -- germ/Taylor `fderiv` machinery (the unbanked content the non-front route needed). The WLOG transfer
  -- to a general (non-front) `B` is via `B·Π` at the headline (b-wlog-spec lemmas 1-5), where the
  -- `⨅ optimalSet` form is invariant.
  --
  -- **CLOSED this tide (front pivot):** (a) `hconj` (block decomposition, `fromBlocks_toBlocks`); (b)
  -- the EXACT reg energy (`hbexact`); S5a `Invertible P00` (banked `eventually_P00_invertible`); AND
  -- (c) the leak `∑(P10⅟P00 P01)² ≤ Sreg` (S5b `eventually_leak`, landed this tide: `P01 w0 = P10 w0
  -- = 0`, `(P00)⁻¹` continuous at the unit `P00 w0 = 1` — a continuity+sub-multiplicativity bound,
  -- `t = 1`). The `𝓝 w0` set `U` is the coupled `S5a-set ∩ S5b-set` (`Filter.inter_mem`).
  -- **REMAINING (2 precisely-named `sorry`s, the genuine unbuilt geometry, pivot-AGNOSTIC):** the
  -- folded core (d')/(e') (the per-layer↔global Schur charge to `Sreg` via the BANKED
  -- `schur_core_germ_comparability` + `deepestCoreAbsorb` — needs the UNBUILT structural bridge
  -- `Rcore = P11 − P10⅟P00 P01 ↔ deepestCoreF (deepestCoreAbsorb (split w)).2.1`).
  have hproducer :
      ∃ (t γ₁ γ₂ δ₁ δ₂ : ℝ), 0 < γ₁ ∧ 0 < γ₂ ∧ 0 < δ₁ ∧ 0 < δ₂ ∧
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
              ∧ (δ₁ * (((∑ i, ∑ j, ((P00 - 1) i j) ^ 2) + (∑ i, ∑ j, (P01 i j) ^ 2))
                      + (∑ i, ∑ j, (P10 i j) ^ 2))
                  ≤ (∑ i, (deepestEFull H r hr hL J Pf Qf (split w)) i ^ 2))
              ∧ ((∑ i, (deepestEFull H r hr hL J Pf Qf (split w)) i ^ 2)
                  ≤ δ₂ * (((∑ i, ∑ j, ((P00 - 1) i j) ^ 2) + (∑ i, ∑ j, (P01 i j) ^ 2))
                      + (∑ i, ∑ j, (P10 i j) ^ 2)))
              ∧ ((∑ i, ∑ j, ((P10 * ⅟P00 * P01) i j) ^ 2)
                  ≤ t ^ 2 * (((∑ i, ∑ j, ((P00 - 1) i j) ^ 2) + (∑ i, ∑ j, (P01 i j) ^ 2))
                      + (∑ i, ∑ j, (P10 i j) ^ 2)))
              ∧ ((((∑ i, ∑ j, ((P00 - 1) i j) ^ 2) + (∑ i, ∑ j, (P01 i j) ^ 2))
                      + (∑ i, ∑ j, (P10 i j) ^ 2))
                    + (∑ i, ∑ j, ((P11 - P10 * ⅟P00 * P01) i j) ^ 2)
                  ≤ γ₂ * (((((∑ i, ∑ j, ((P00 - 1) i j) ^ 2) + (∑ i, ∑ j, (P01 i j) ^ 2))
                      + (∑ i, ∑ j, (P10 i j) ^ 2)))
                    + deepestCoreF H r (deepestCoreAbsorb H r hr hL (split w)).2.1))
              ∧ (((((∑ i, ∑ j, ((P00 - 1) i j) ^ 2) + (∑ i, ∑ j, (P01 i j) ^ 2))
                      + (∑ i, ∑ j, (P10 i j) ^ 2)))
                    + deepestCoreF H r (deepestCoreAbsorb H r hr hL (split w)).2.1
                  ≤ γ₁ * ((((∑ i, ∑ j, ((P00 - 1) i j) ^ 2) + (∑ i, ∑ j, (P01 i j) ^ 2))
                      + (∑ i, ∑ j, (P10 i j) ^ 2))
                    + (∑ i, ∑ j, ((P11 - P10 * ⅟P00 * P01) i j) ^ 2))) := by
    -- **FRONT-PIVOT PRODUCER (B route, this tide, 2026-06-25).** With the front pivot, conjuncts (a)
    -- (`hconj`, `fromBlocks_toBlocks`), (b) (`∑deepestEFull² = Sreg`, EXACT via `hRegBlocks` +
    -- `deepestEFull_sq_sum_eq_blocks` — so `δ₁ = δ₂ = 1`), S5a (`eventually_P00_invertible`, banked)
    -- AND (c) the leak (`eventually_leak`, banked this tide, `t = 1`) are CLOSED. The block witnesses
    -- are the `toBlocks` of `M w := reindex(P0·(prod(symm w)−B)·QL)` (with `P00 := M.toBlocks₁₁ + 1`,
    -- so `P00 − 1 = M.toBlocks₁₁`); `U := S5a-set ∩ S5b-set` (`Filter.inter_mem`). **REMAINING
    -- (2 named `sorry`s):** the folded core (d')/(e') (the per-layer↔global Schur charge to `Sreg`
    -- via the banked `schur_core_germ_comparability` + `deepestCoreAbsorb`, needing the UNBUILT
    -- structural bridge `Rcore ↔ deepestCoreF (deepestCoreAbsorb (split w)).2.1`) — pivot-agnostic.
    classical
    -- **(b)-EXACT** (front pivot): `∑deepestEFull(split w)² = Sreg(w)` where `Sreg(w)` is the three
    -- residual-block energies of `M w := reindex(P0·(prod(symm w)−B)·QL)`. Via the block-energy identity
    -- `deepestEFull_sq_sum_eq_blocks` (LHS = the energies of `P' := reindex(prod(framedParamsPivot)) =
    -- reindex(prod (F w))`) + the front-pivot bridge `hRegBlocks` (`P' = fromBlocks 1 0 0 0 + M w`, so
    -- `P'.toBlocks₁₁ − 1 = M.toBlocks₁₁`, `P'.toBlocks₁₂ = M.toBlocks₁₂`, `P'.toBlocks₂₁ = M.toBlocks₂₁`).
    have hbexact : ∀ w, (∑ i, (deepestEFull H r hr hL J Pf Qf (split w)) i ^ 2)
        = ((∑ a, ∑ b, ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₁ a b) ^ 2)
            + (∑ a, ∑ b, ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₂ a b) ^ 2))
          + (∑ a, ∑ b, ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₂₁ a b) ^ 2) := by
      intro w
      -- LHS = block energies of `P' := reindex(prod(framedParamsPivot(split w)))`.
      rw [deepestEFull_sq_sum_eq_blocks H r hr hL J Pf Qf (split w)]
      -- `prod(framedParamsPivot(split w)) = prod (F w)` (def `hF`), then `hRegBlocks w`:
      -- `reindex(prod (F w)) = fromBlocks 1 0 0 0 + M w`. The `toBlocks` of a `fromBlocks 1 0 0 0` sum:
      -- `toBlocks₁₁ = 1 + M.toBlocks₁₁` so `−1` cancels; `toBlocks₁₂ = M.toBlocks₁₂`; `toBlocks₂₁`.
      have hFw : prod H (framedParamsPivot H r hr hL J Pf Qf (split w)) = prod H (F w) := by
        rw [hF]
      set Mw := Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL) with hMwdef
      -- The reindexed product `P' = reindex(prod (F w)) = fromBlocks 1 0 0 0 + Mw` (front pivot).
      have hP'split : Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (prod H (framedParamsPivot H r hr hL J Pf Qf (split w)))
          = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 + Mw := by
        rw [hFw, hRegBlocks w, hMwdef]
      rw [hP'split]
      -- The three block energies of `fromBlocks 1 0 0 0 + Mw` equal those of `Mw`'s pure blocks.
      have hb11 : ∀ a b, ((Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 + Mw).toBlocks₁₁
            - 1) a b = Mw.toBlocks₁₁ a b := by
        intro a b
        simp only [Matrix.toBlocks₁₁, Matrix.add_apply, Matrix.sub_apply, Matrix.of_apply,
          Matrix.fromBlocks_apply₁₁, Matrix.one_apply]
        split <;> ring
      have hb12 : ∀ a b, (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 + Mw).toBlocks₁₂ a b
            = Mw.toBlocks₁₂ a b := by
        intro a b
        simp only [Matrix.toBlocks₁₂, Matrix.add_apply, Matrix.of_apply,
          Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_add]
      have hb21 : ∀ a b, (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 + Mw).toBlocks₂₁ a b
            = Mw.toBlocks₂₁ a b := by
        intro a b
        simp only [Matrix.toBlocks₂₁, Matrix.add_apply, Matrix.of_apply,
          Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, zero_add]
      -- The three block energies of `fromBlocks 1 0 0 0 + Mw` equal those of `Mw`'s pure blocks.
      have hs11 : (∑ a, ∑ b, (((Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 + Mw).toBlocks₁₁
            - 1) a b) ^ 2) = ∑ a, ∑ b, (Mw.toBlocks₁₁ a b) ^ 2 :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by rw [hb11 a b]))
      have hs12 : (∑ a, ∑ b, ((Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 + Mw).toBlocks₁₂
            a b) ^ 2) = ∑ a, ∑ b, (Mw.toBlocks₁₂ a b) ^ 2 :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by rw [hb12 a b]))
      have hs21 : (∑ a, ∑ b, ((Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 + Mw).toBlocks₂₁
            a b) ^ 2) = ∑ a, ∑ b, (Mw.toBlocks₂₁ a b) ^ 2 :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by rw [hb21 a b]))
      rw [hs11, hs12, hs21]
      ring
    -- S5a: the `(1,1)`-block map is eventually a unit (banked `eventually_P00_invertible`).
    -- S5a (`IsUnit P00`) and S5b (the leak smallness) are each a `𝓝 w0` member; `U` is their
    -- intersection (`Filter.inter_mem`). Each `w ∈ U` then carries BOTH facts (`hw.1`, `hw.2`).
    have hP00ev := eventually_P00_invertible H r B hB hr hL P0 QL
      (rThresholdSplit r (H 0) (hr 0)) (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
    have hleakev := eventually_leak H r B hB hr hL P0 QL
      (rThresholdSplit r (H 0) (hr 0)) (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
    -- **THE ONE REMAINING GEOMETRIC GAP (the in-sum Schur charge).** The folded-core conjuncts
    -- (d')/(e') reduce to a SINGLE GERM charge: a constant `C ≥ 0` with, EVENTUALLY in `𝓝 w0`, the
    -- in-sum bound `|frobSq Rcore(w) − coreΦ(w)| ≤ C·Sreg(w)` (`Rcore = P11 − P10·(P00)⁻¹·P01` the
    -- global Schur complement of `Mw`, `coreΦ = deepestCoreF (coreAbsorb (split w)).2.1`, `Sreg`
    -- the three regular-block energies). GERM-scoped (NOT `∀ w` — the in-sum charge is FALSE globally:
    -- where `Sreg(w) = 0` but `Rcore ≠ coreΦ`, `|…| ≤ C·0` fails; it holds only near `w0`). This is
    -- the FRAME-STRIPPING-bridge + S5c germ charge (see the per-conjunct notes below): lemma 1
    -- (`deepestCoreF_coreAbsorb_eq_prodSchur`, banked above) pins `coreΦ = frobSq (∏S)`; the verified
    -- 2-layer LDU (sympy `two-layer-ldu-verify.py`) gives `Rcore = S0·(1−K)·S1`; the banked
    -- `schur_core_germ_comparability` + Cauchy–Schwarz then bound the in-sum difference by `C·Sreg`
    -- on the germ. Stated with the TOTAL inverse `(·)⁻¹` (= `⅟P00` on the S5a set,
    -- `invOf_eq_nonsing_inv`) so the constant `C` is `w`-uniform on the germ. UNBUILT (the
    -- frame-aware identification of `Rcore` with the lemma-1 `S0,S1` despite the per-layer `Pf,Qf`
    -- frames). The germ set is folded into `U` via `Filter.inter_mem`, so `hw.2` carries it per-`w`.
    obtain ⟨C, hCnn, hcharge⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ w in 𝓝 w0,
        |(∑ i, ∑ j, (((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₂₂
            - (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₂₁
              * ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                  (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                  (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₁ + 1)⁻¹
              * (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                  (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                  (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₂) i j) ^ 2)
          - deepestCoreF H r (deepestCoreAbsorb H r hr hL (split w)).2.1|
          ≤ C * (((∑ i, ∑ j, (((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                  (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                  (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₁) i j) ^ 2)
              + (∑ i, ∑ j, (((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                  (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                  (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₂) i j) ^ 2))
            + (∑ i, ∑ j, (((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                  (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                  (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₂₁) i j) ^ 2)) := by
      sorry
    refine ⟨1, 1 + C, 1 + C, 1, 1, by positivity, by positivity, one_pos, one_pos,
      ({w | IsUnit ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₁
        + (1 : Matrix (Fin r) (Fin r) ℝ))}
      ∩ {w | (∑ i, ∑ j, (((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₂₁
            * ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₁ + 1)⁻¹
            * (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₂) i j) ^ 2)
        ≤ (1 : ℝ) ^ 2
          * (((∑ i, ∑ j, (((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                  (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                  (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₁) i j) ^ 2)
              + (∑ i, ∑ j, (((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                  (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                  (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₂) i j) ^ 2))
            + (∑ i, ∑ j, (((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                  (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                  (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₂₁) i j) ^ 2))})
      ∩ {w | |(∑ i, ∑ j, (((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₂₂
            - (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₂₁
              * ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                  (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                  (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₁ + 1)⁻¹
              * (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                  (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                  (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₂) i j) ^ 2)
          - deepestCoreF H r (deepestCoreAbsorb H r hr hL (split w)).2.1|
          ≤ C * (((∑ i, ∑ j, (((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                  (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                  (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₁) i j) ^ 2)
              + (∑ i, ∑ j, (((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                  (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                  (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₂) i j) ^ 2))
            + (∑ i, ∑ j, (((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                  (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                  (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₂₁) i j) ^ 2))},
      Filter.inter_mem (Filter.inter_mem hP00ev hleakev) hcharge, fun w hw => ?_⟩
    -- The conjugated residual `M w` and its four blocks (`P00 := M.toBlocks₁₁ + 1`).
    set Mw := Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL) with hMw
    -- S5a gives `IsUnit (M.toBlocks₁₁ + 1)`, the producer's `P00` (first intersection component).
    have hP00u : IsUnit (Mw.toBlocks₁₁ + (1 : Matrix (Fin r) (Fin r) ℝ)) := hw.1.1
    -- S5b gives the leak smallness `∑(P10·(P00)⁻¹·P01)² ≤ Sreg` (second intersection component).
    have hleakw := hw.1.2
    -- The in-sum Schur charge (third intersection component, the germ gap).
    have hchargew := hw.2
    letI : Invertible (Mw.toBlocks₁₁ + (1 : Matrix (Fin r) (Fin r) ℝ)) := hP00u.invertible
    refine ⟨Mw.toBlocks₁₁ + 1, Mw.toBlocks₁₂, Mw.toBlocks₂₁, Mw.toBlocks₂₂, this, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (a) `hconj`: `M = fromBlocks (P00−1) P01 P10 P11`. `P00 − 1 = M.toBlocks₁₁` ⟹ `fromBlocks_toBlocks`.
      rw [add_sub_cancel_right]
      exact (Matrix.fromBlocks_toBlocks Mw).symm
    · -- (b)-low: `1·Sreg ≤ ∑deepestEFull²`. EXACT (`= Sreg`), so `≤` with `δ₁ = 1`.
      rw [one_mul, add_sub_cancel_right]
      exact le_of_eq (hbexact w).symm
    · -- (b)-high: `∑deepestEFull² ≤ 1·Sreg`. EXACT, so `≤` with `δ₂ = 1`.
      rw [one_mul, add_sub_cancel_right]
      exact le_of_eq (hbexact w)
    · -- (c) leak (S5b `eventually_leak`, banked this tide). The intersection's second component
      -- `hleakw` is EXACTLY this bound with `t = 1`, modulo `⅟P00 = (P00)⁻¹` (`invOf_eq_nonsing_inv`)
      -- and `P00 − 1 = M.toBlocks₁₁` (`add_sub_cancel_right`).
      rw [add_sub_cancel_right, invOf_eq_nonsing_inv (Mw.toBlocks₁₁ + (1 : Matrix (Fin r) (Fin r) ℝ))]
      exact hleakw
    · -- (d') folded core UPPER: `Sreg + Score ≤ (1+C)·(Sreg + coreΦ)`. From the in-sum charge
      -- `hchargew` (= `hw.2`, `|Score − coreΦ| ≤ C·Sreg` — the ONE remaining germ gap above) +
      -- nonnegativity, by `nlinarith`. (The γ = 1+C fold; the earlier `1`-binding was UNSOUND —
      -- `Score = coreΦ` is FALSE for M>1.)
      have hch := hchargew
      simp only [Set.mem_setOf_eq, ← hMw] at hch
      rw [invOf_eq_nonsing_inv (Mw.toBlocks₁₁ + (1 : Matrix (Fin r) (Fin r) ℝ)), add_sub_cancel_right]
      rw [abs_sub_le_iff] at hch
      have hSreg_nn : (0 : ℝ) ≤ ((∑ i, ∑ j, ((Mw.toBlocks₁₁) i j) ^ 2)
          + (∑ i, ∑ j, ((Mw.toBlocks₁₂) i j) ^ 2)) + (∑ i, ∑ j, ((Mw.toBlocks₂₁) i j) ^ 2) := by
        positivity
      have hcore_nn : (0 : ℝ) ≤ deepestCoreF H r (deepestCoreAbsorb H r hr hL (split w)).2.1 :=
        dlnLoss_nonneg _ _ _
      nlinarith [hch.1, hch.2, hSreg_nn, hcore_nn, hCnn,
        mul_nonneg hCnn hSreg_nn]
    · -- (e') folded core LOWER: `Sreg + coreΦ ≤ (1+C)·(Sreg + Score)`. Same charge `hchargew`, the
      -- other direction, by `nlinarith`.
      have hch := hchargew
      simp only [Set.mem_setOf_eq, ← hMw] at hch
      rw [invOf_eq_nonsing_inv (Mw.toBlocks₁₁ + (1 : Matrix (Fin r) (Fin r) ℝ)), add_sub_cancel_right]
      rw [abs_sub_le_iff] at hch
      have hSreg_nn : (0 : ℝ) ≤ ((∑ i, ∑ j, ((Mw.toBlocks₁₁) i j) ^ 2)
          + (∑ i, ∑ j, ((Mw.toBlocks₁₂) i j) ^ 2)) + (∑ i, ∑ j, ((Mw.toBlocks₂₁) i j) ^ 2) := by
        positivity
      have hScore_nn : (0 : ℝ) ≤ ∑ i, ∑ j, ((Mw.toBlocks₂₂
          - Mw.toBlocks₂₁ * (Mw.toBlocks₁₁ + 1)⁻¹ * Mw.toBlocks₁₂) i j) ^ 2 := by positivity
      nlinarith [hch.1, hch.2, hSreg_nn, hScore_nn, hCnn,
        mul_nonneg hCnn hSreg_nn]
  obtain ⟨t, γ₁, γ₂, δ₁, δ₂, hγ₁, hγ₂, hδ₁, hδ₂, U, hU, hbody⟩ := hproducer
  exact ⟨P0, QL, Pi, Qi, t, γ₁, γ₂, δ₁, δ₂, hPP, hQQ, hγ₁, hγ₂, hδ₁, hδ₂, hKP_pos, hKi_pos, U, hU, hbody⟩

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
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    -- **FRONT-PIVOT HYPOTHESIS** (threaded to the frame-bridge cert, b-wlog-spec): the pivot embedding
    -- is the front embedding, making the (b)-conjunct an EXACT equality (see the cert's `hfront`).
    (hfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (coreAbsorb : DeepestSplit H r (deepestNGauge H r) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (hsplit_base : split ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) = 0)
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (hregval : ∀ q : DeepestSplit H r (deepestNGauge H r),
      (regStraighten q).1 = deepestEFull H r hr hL J Pf Qf q)
    (hcoreabs : coreAbsorb = deepestCoreAbsorb H r hr hL)
    -- The seven frame facts threaded to the (now-true) frame-bridge cert (see its signature).
    (hPunit : ∀ s : Fin L, IsUnit (Pf s)) (hQunit : ∀ s : Fin L, IsUnit (Qf s))
    (hQf0 : Qf (firstLayer hL)
      = (1 : Matrix (Fin (H (firstLayer hL).succ)) (Fin (H (firstLayer hL).succ)) ℝ))
    (hPfL : Pf (lastLayer hL)
      = (1 : Matrix (Fin (H (lastLayer hL).castSucc)) (Fin (H (lastLayer hL).castSucc)) ℝ))
    (hNF : ∀ s : Fin L, (s : ℕ) + 1 ≠ L →
      Pf s * (deepestPoint H r B hB hr hL s) * Qf s
        = Matrix.of (fun (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) =>
            if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0))
    (hcorner : Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        ((deepestPoint H r B hB hr hL (lastLayer hL)) * Qf (lastLayer hL))
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (hinterface : ∀ (s : Fin L) (_ : (s : ℕ) + 1 < L),
      Qf s = (1 : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) ∧
        Pf ⟨(s : ℕ) + 1, by omega⟩ = (1 : Matrix (Fin (H (⟨(s : ℕ) + 1, by omega⟩ : Fin L).castSucc))
          (Fin (H (⟨(s : ℕ) + 1, by omega⟩ : Fin L).castSucc)) ℝ)) :
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
  obtain ⟨P0, QL, Pi, Qi, t, γ₁, γ₂, δ₁, δ₂, hP, hQ, hγ₁, hγ₂, hδ₁, hδ₂, hKP_pos, hKi_pos, U, hU, hbr⟩ :=
    framedParams_split_eq_frame_raw H r B hB hr hL hL2 hpos J hfront Pf Qf split hsplit
      hPunit hQunit hQf0 hPfL hNF hcorner hinterface
  -- Endpoint-frame energies (the conjugation constants). `KP = ∑P0²·∑QL²`, `Ki = ∑Pi²·∑Qi²`.
  set KP := (∑ i, ∑ k, (P0 i k) ^ 2) * (∑ j, ∑ k, (QL k j) ^ 2) with hKP
  set Ki := (∑ i, ∑ k, (Pi i k) ^ 2) * (∑ j, ∑ k, (Qi k j) ^ 2) with hKi
  -- `Klo = 2(1+t²)·KP`, `Kup = Ki·(2+2t²)`; both positive (the cert supplies `0 < KP`, `0 < Ki`).
  set Klo := 2 * (1 + t ^ 2) * KP with hKlo
  set Kup := Ki * (2 + 2 * t ^ 2) with hKup
  have hKlo_pos : 0 < Klo := by rw [hKlo]; positivity
  have hKup_pos : 0 < Kup := by rw [hKup]; positivity
  have hKup_nonneg : 0 ≤ Kup := le_of_lt hKup_pos
  -- The two squeeze constants for the FOLDED comparability `Sreg + Score ≍ Sreg + coreΦ` (thread 31),
  -- with the conjunct-(b) reg comparability `δ₁·Sreg ≤ Sreg_E ≤ δ₂·Sreg` (`Sreg_E = ∑(regStraighten)²`)
  -- absorbed. `Φ = Sreg_E + coreΦ`. LOWER `c₁ = ((δ₂+1)·γ₁·Klo)⁻¹`:
  -- `Φ = Sreg_E + coreΦ ≤ δ₂·Sreg + coreΦ ≤ (δ₂+1)·(Sreg+coreΦ) ≤ (δ₂+1)·γ₁·(Sreg+Score) ≤
  --  (δ₂+1)·γ₁·Klo·NN`. UPPER `c₂ = Kup·γ₂·(δ₁⁻¹+1)`:
  -- `NN ≤ Kup·(Sreg+Score) ≤ Kup·γ₂·(Sreg+coreΦ) ≤ Kup·γ₂·(δ₁⁻¹+1)·(Sreg_E+coreΦ) = Kup·γ₂·(δ₁⁻¹+1)·Φ`.
  refine ⟨((δ₂ + 1) * γ₁ * Klo)⁻¹, Kup * γ₂ * (δ₁⁻¹ + 1), ?_, ?_, U, hU, ?_⟩
  · have : 0 < (δ₂ + 1) * γ₁ * Klo := by positivity
    positivity
  · have hd1 : 0 < δ₁⁻¹ + 1 := by positivity
    positivity
  -- Per-`w` bound.
  intro w hw
  obtain ⟨P00, P01, P10, P11, hP00, hconj, hSreg_lo, hSreg_hi, hleak, hcore_le, hcore_ge⟩ := hbr w hw
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
  -- `Sreg_E := ∑ i, (regStraighten (split w)).1 i ^ 2` (the Φ-reg energy): `regStraighten`'s reg output
  -- IS `deepestEFull` (`hregval`), so this is `∑deepestEFull²(split w)`. The conjunct-(b) COMPARABILITY
  -- `δ₁·Sreg ≤ Sreg_E ≤ δ₂·Sreg` (`hSreg_lo`/`hSreg_hi`) replaces the refuted EQUALITY — the constants
  -- `δ₁, δ₂` are absorbed into the squeeze bounds below.
  set Sreg_E := ∑ i, (regStraighten (split w)).1 i ^ 2 with hSreg_E
  have hSregE_eq : Sreg_E = ∑ i, (deepestEFull H r hr hL J Pf Qf (split w)) i ^ 2 := by
    have hpt : ∀ i, (regStraighten (split w)).1 i = deepestEFull H r hr hL J Pf Qf (split w) i :=
      fun i => congrFun (hregval (split w)) i
    rw [hSreg_E]; exact Finset.sum_congr rfl (fun i _ => by rw [hpt i])
  -- The comparability transported to `Sreg_E` (replacing `∑deepestEFull²` by `Sreg_E`).
  have hSregE_lo : δ₁ * Sreg ≤ Sreg_E := by rw [hSregE_eq]; exact hSreg_lo
  have hSregE_hi : Sreg_E ≤ δ₂ * Sreg := by rw [hSregE_eq]; exact hSreg_hi
  -- The core-comparability + leak bound fold into the squeeze. `coreΦ = deepestCoreF (coreAbsorb)`.
  rw [hcoreabs]
  set coreΦ := deepestCoreF H r (deepestCoreAbsorb H r hr hL (split w)).2.1 with hcoreΦ
  -- Nonnegativity facts.
  have hSreg_nn : 0 ≤ Sreg := by
    rw [hSreg]; positivity
  have hSregE_nn : 0 ≤ Sreg_E := by rw [hSreg_E]; positivity
  have hScore_nn : 0 ≤ Score := by rw [hScore]; positivity
  have hcoreΦ_nn : 0 ≤ coreΦ := by rw [hcoreΦ]; exact dlnLoss_nonneg _ _ _
  -- `cleanE = Sreg + Score`; the leaf bounds are `cleanE ≤ Klo·NN` and `NN ≤ Kup·cleanE`.
  -- (the leaf lemma states them with the explicit constants; identify them with Klo/Kup.)
  have hlo' : Sreg + Score ≤ Klo * NN := by
    rw [hKlo, hKP]; exact hlo
  have hhi' : NN ≤ Kup * (Sreg + Score) := by
    rw [hKup, hKi, mul_assoc]; exact hhi
  -- The target Φ for this `w` (the squeeze's public Φ, `= Sreg_E + coreΦ`).
  set Φ := (∑ i, (regStraighten (split w)).1 i ^ 2) + coreΦ with hΦ
  have hΦ_eq : Φ = Sreg_E + coreΦ := by rw [hΦ, hSreg_E]
  have hΦ_nn : 0 ≤ Φ := by rw [hΦ_eq]; exact add_nonneg hSregE_nn hcoreΦ_nn
  refine ⟨hΦ_nn, ?_, ?_⟩
  · -- LOWER: `c₁·Φ ≤ dlnLoss = NN`, `c₁ = ((δ₂+1)·γ₁·Klo)⁻¹`. Chain:
    -- `Φ = Sreg_E + coreΦ ≤ δ₂·Sreg + coreΦ ≤ (δ₂+1)·(Sreg+coreΦ) ≤ (δ₂+1)·γ₁·(Sreg+Score) ≤
    --  (δ₂+1)·γ₁·Klo·NN`. (`hcore_ge` is the folded `Sreg+coreΦ ≤ γ₁·(Sreg+Score)`.)
    rw [hloss_eq]
    -- step A: `Φ ≤ (δ₂+1)·(Sreg + coreΦ)` (absorb the reg upper comparability `Sreg_E ≤ δ₂·Sreg`).
    have hδ2_ge1 : (1 : ℝ) ≤ δ₂ + 1 := by linarith
    have hδ2_le : δ₂ ≤ δ₂ + 1 := by linarith
    have hstepA : Φ ≤ (δ₂ + 1) * (Sreg + coreΦ) := by
      rw [hΦ_eq, mul_add]
      refine add_le_add ?_ ?_
      · exact le_trans hSregE_hi (mul_le_mul_of_nonneg_right hδ2_le hSreg_nn)
      · exact le_mul_of_one_le_left hcoreΦ_nn hδ2_ge1
    have hδ2p1_nn : (0 : ℝ) ≤ δ₂ + 1 := by linarith
    -- step B: `(δ₂+1)·(Sreg+coreΦ) ≤ (δ₂+1)·γ₁·(Sreg+Score) ≤ (δ₂+1)·γ₁·Klo·NN`.
    have hstepB : (δ₂ + 1) * (Sreg + coreΦ) ≤ (δ₂ + 1) * γ₁ * Klo * NN := by
      calc (δ₂ + 1) * (Sreg + coreΦ) ≤ (δ₂ + 1) * (γ₁ * (Sreg + Score)) :=
            mul_le_mul_of_nonneg_left hcore_ge hδ2p1_nn
        _ ≤ (δ₂ + 1) * (γ₁ * (Klo * NN)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlo' (le_of_lt hγ₁)) hδ2p1_nn
        _ = (δ₂ + 1) * γ₁ * Klo * NN := by ring
    have hΦle : Φ ≤ (δ₂ + 1) * γ₁ * Klo * NN := le_trans hstepA hstepB
    -- multiply by `c₁ = ((δ₂+1)·γ₁·Klo)⁻¹ ≥ 0`; `c₁·((δ₂+1)·γ₁·Klo) = 1`.
    have hden_pos : 0 < (δ₂ + 1) * γ₁ * Klo := by positivity
    have hc₁ := mul_le_mul_of_nonneg_left hΦle (le_of_lt (inv_pos.mpr hden_pos))
    rwa [inv_mul_cancel_left₀ (ne_of_gt hden_pos)] at hc₁
  · -- UPPER: `dlnLoss = NN ≤ c₂·Φ`, `c₂ = Kup·γ₂·(δ₁⁻¹+1)`. Chain:
    -- `NN ≤ Kup·(Sreg+Score) ≤ Kup·γ₂·(Sreg+coreΦ) ≤ Kup·γ₂·(δ₁⁻¹+1)·(Sreg_E+coreΦ) = c₂·Φ`
    -- (using `Sreg ≤ δ₁⁻¹·Sreg_E` from `δ₁·Sreg ≤ Sreg_E`).
    rw [hloss_eq, hΦ_eq]
    -- `Sreg ≤ δ₁⁻¹·Sreg_E` (divide `δ₁·Sreg ≤ Sreg_E` by `δ₁ > 0`).
    have hδ1inv_nn : (0 : ℝ) ≤ δ₁⁻¹ := inv_nonneg.mpr (le_of_lt hδ₁)
    have hSreg_inv : Sreg ≤ δ₁⁻¹ * Sreg_E := by
      have := mul_le_mul_of_nonneg_left hSregE_lo hδ1inv_nn
      rwa [inv_mul_cancel_left₀ (ne_of_gt hδ₁)] at this
    -- `Sreg + coreΦ ≤ (δ₁⁻¹+1)·(Sreg_E + coreΦ)` (absorb the reg lower comparability).
    have hd1p1_ge1 : (1 : ℝ) ≤ δ₁⁻¹ + 1 := by linarith
    have hd1_le : δ₁⁻¹ ≤ δ₁⁻¹ + 1 := by linarith
    have hfold : Sreg + coreΦ ≤ (δ₁⁻¹ + 1) * (Sreg_E + coreΦ) := by
      rw [mul_add]
      refine add_le_add ?_ ?_
      · exact le_trans hSreg_inv (mul_le_mul_of_nonneg_right hd1_le hSregE_nn)
      · exact le_mul_of_one_le_left hcoreΦ_nn hd1p1_ge1
    calc NN ≤ Kup * (Sreg + Score) := hhi'
      _ ≤ Kup * (γ₂ * (Sreg + coreΦ)) := mul_le_mul_of_nonneg_left hcore_le hKup_nonneg
      _ ≤ Kup * (γ₂ * ((δ₁⁻¹ + 1) * (Sreg_E + coreΦ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hfold (le_of_lt hγ₂)) hKup_nonneg
      _ = Kup * γ₂ * (δ₁⁻¹ + 1) * (Sreg_E + coreΦ) := by ring

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
        (finCongr (H_lastLayer_succ H hL)).toEmbedding = frontEmbed H r hr) :
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
  -- Use the bundle's `.choose` for `Jb` (so the signature's `hJfront`, stated about `.choose`,
  -- connects to the body's `J`), and `.choose_spec` for the rest of the bundle.
  set Jb : Fin r ↪ Fin (H ((lastLayer hL).succ)) :=
    (deepestPoint_frame_pivot_exists H r B hB hr hL hL2).choose with hJb_def
  obtain ⟨Pf, Qf, hPunit, hQunit, hQf0, hPfL, hNF, hQf22b, hcorner⟩ :=
    (deepestPoint_frame_pivot_exists H r B hB hr hL hL2).choose_spec
  -- The outer-reindex pivot embedding lives on `Fin (H (Fin.last L))`; `Jb` on `Fin (H (lastLayer).succ)`.
  -- The cast bridge (`H_lastLayer_succ`); `pivotJSucc J = Jb` (the two `finCongr` round-trip).
  set J : Fin r ↪ Fin (H (Fin.last L)) :=
    Jb.trans (finCongr (H_lastLayer_succ H hL)).toEmbedding with hJ
  -- The body's `J` IS the front embedding (the signature's `hJfront`, via `.choose`).
  have hJfront' : J = frontEmbed H r hr := by rw [hJ, hJb_def]; exact hJfront
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
  -- PIN 2: the loss squeeze (consuming the concrete `coreAbsorb` + `regStraighten`'s defining identities).
  obtain ⟨c₁, c₂, hc₁, hc₂, U, hU, hsq⟩ :=
    deepest_loss_squeeze H r B hB hr hL hL2 hpos J hJfront' Pf Qf split coreAbsorb regStraighten
      hsplit_base hsplit hra_regval hca_def hPunit hQunit hQf0 hPfL hNF hcorner' hinterface
  exact ⟨deepestNGauge H r, split, coreAbsorb, regStraighten, hsplit_mp, hsplit_base,
    hca_base, hca_reg, hca_spec, hca_rlct, hra_cont, hra_base, hra_core, hra_spec, hra_rlct,
    c₁, c₂, hc₁, hc₂, U, hU, hsq⟩

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
        (finCongr (H_lastLayer_succ H hL)).toEmbedding = frontEmbed H r hr) :
    Nonempty (DeepestGaugeChart H r B hB hr hL) := by
  obtain ⟨nGauge, split, coreAbsorb, regStraighten, hsplit_mp, hsplit_base, hca_base, hca_reg,
    hca_spec, hca_rlct, hra_cont, hra_base, hra_core, hra_spec, hra_rlct, hsq⟩ :=
    deepest_gauge_construction H r B hB hr hL hL2 hpos hJfront
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
