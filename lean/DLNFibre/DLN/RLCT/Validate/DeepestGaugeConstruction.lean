import DLNFibre.DLN.RLCT.Validate.DeepestGaugeChart
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeBlocks
import DLNFibre.DLN.RLCT.Validate.DeepestSplitReindex
import DLNFibre.DLN.RLCT.Validate.DeepestFrame
import DLNFibre.DLN.RLCT.Validate.DeepestFramedProduct
import DLNFibre.DLN.RLCT.Validate.DeepestTelescoping
import DLNFibre.DLN.RLCT.Validate.DeepestSchurShift
import DLNFibre.DLN.RLCT.Validate.DeepestRegAbsorbIFT
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
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ) → (Fin (deepestNReg H r) → ℝ) :=
  fun p =>
    let P := Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H (Fin.last L))
      (hr (Fin.last L))) (prod H (framedParamsReg H r hr hL p))
    fun i => match regResidualPack H r hr i with
      | Sum.inl (a, b) => (P.toBlocks₁₁ - 1) a b
      | Sum.inr (Sum.inl (a, b)) => P.toBlocks₁₂ a b
      | Sum.inr (Sum.inr (a, b)) => P.toBlocks₂₁ a b

theorem deepestEPivot_contdiff (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ContDiff ℝ (⊤ : ℕ∞) (deepestEPivot H r hr hL) := by
  -- Each layer entry of `framedParamsReg` is `ContDiff` (`contDiff_framedParamsReg_entry`), so each
  -- entry of `prod H (framedParamsReg ·)` is `ContDiff` (`contDiff_prod_entry`).
  have hlayer : ∀ (s : Fin L) (a : Fin (H s.castSucc)) (b : Fin (H s.succ)),
      ContDiff ℝ (⊤ : ℕ∞) (fun p => framedParamsReg H r hr hL p s a b) :=
    contDiff_framedParamsReg_entry H r hr hL
  have hprod : ∀ (a : Fin (H 0)) (b : Fin (H (Fin.last L))),
      ContDiff ℝ (⊤ : ℕ∞) (fun p => prod H (framedParamsReg H r hr hL p) a b) :=
    fun a b => contDiff_prod_entry H (framedParamsReg H r hr hL) hlayer a b
  -- `deepestEPivot p` is a `Fin nReg → ℝ` whose each coordinate is (a `prod`-entry, reindexed) − const.
  refine contDiff_pi.2 (fun i => ?_)
  -- The `i`-coordinate selects one match-arm (independent of `p`); rewrite to that arm, then it is a
  -- reindexed `prod`-entry (minus the constant `1` on the `inl` arm).
  have hcoord : (fun p => deepestEPivot H r hr hL p i)
      = fun p =>
        let P := Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)))
          (prod H (framedParamsReg H r hr hL p))
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

/-- **`deepestEPivot`'s reg-block derivative at `0` is the IDENTITY** (the #91 analytic crux,
g213-pin1-de0). Restricted to the regular slice `r ↦ deepestEPivot (r, 0)`, the strict derivative at
`0` is `id` — the idempotent-sandwich `dP|_0 = Σ_s corner·δC_s·corner` with the gauge slot held at `0`
keeps ONLY the `(0,0)`-block `X`-pivot (which equals the reg-input on the pivot coords). This is the
single analytic obligation of `_deriv`; everything else (the product strict-derivative, the shear-CLE
packaging) is banked. **OBLIGATION:** the `regResidualPack` ↔ `(X_first, Y_last, Z_first)` pivot-coord
correspondence at the gauge-zero slice (the #91 transcription / pp2 coordinate cert). -/
theorem deepestEPivot_regSlice_fderiv_id (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
        deepestEPivot H r hr hL (r0, 0))
      (ContinuousLinearMap.id ℝ (Fin (deepestNReg H r) → ℝ)) 0 := by
  -- ATTEMPT (a), coordinate-wise: the output `Fin nReg → ℝ` derivative is `id` iff each coordinate `i`'s
  -- derivative is the `i`-th projection. `deepestEPivot (r0,0) i` = a residual block of
  -- `reindex(prod(framedParamsReg (r0,0)))` selected by `regResidualPack i`. The derivative w.r.t. `r0`
  -- of that block = the idempotent-sandwich (#91), which on the pivot coord IS `r0 i`. WALL (confirmed
  -- via g223): exposing that the `regResidualPack i` block-coord receives EXACTLY `r0 i`'s contribution
  -- needs the SEMANTIC pivot tag (X_first/Y_last/Z_first), which g223 says is the #91/g125 content NOT
  -- readable from the cardinality-split `regResidualPack`/`regGaugeSlotEquiv`. Flagged (b): thin cert.
  sorry

/-- **`deepestEPivot`'s derivative at `0` is the invertible SHEAR** (#120-corrected: NOT `fst`). By #91
(`d(P−B)|_0 = (Σ_s X_s, Y_L, Z_1)`, idempotent sandwich), the reg-residual's derivative reads the
reg-X + sums the gauge-X's into reg while keeping the gauge free — the unitriangular shear
`D_E = [[I, Σ],[0, I]]` on `reg×gauge → reg` (its total `regStraightenTotalCLM D_E` is `[[I,Σ],[0,I]]`
on `DeepestSplit`, det 1, invertible). Bundled: `∃ D_E (e : ≃L), HasStrictFDerivAt deepestEPivot D_E 0
∧ (e : →L) = regStraightenTotalCLM D_E`. ASSEMBLED from `_contdiff` (→ `D_E := fderiv`), the reg-block
identity `deepestEPivot_regSlice_fderiv_id` (the #91 crux), and the generic shear-CLE
`regStraightenTotalCLM_equiv_of_regBlock_id`. -/
theorem deepestEPivot_deriv (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ∃ (D_E : ((Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) →L[ℝ]
        (Fin (deepestNReg H r) → ℝ))
      (e : DeepestSplit H r (deepestNGauge H r) ≃L[ℝ] DeepestSplit H r (deepestNGauge H r)),
      HasStrictFDerivAt (deepestEPivot H r hr hL) D_E 0 ∧
      (e : DeepestSplit H r (deepestNGauge H r) →L[ℝ] DeepestSplit H r (deepestNGauge H r))
        = regStraightenTotalCLM D_E := by
  -- `D_E := fderiv ℝ deepestEPivot 0` (free from `_contdiff`); its reg-block is `id` (the #91 fact),
  -- so `regStraightenTotalCLM D_E` is the invertible shear (`regStraightenTotalCLM_equiv_of_regBlock_id`).
  set D_E := fderiv ℝ (deepestEPivot H r hr hL) 0 with hD_E
  have hsd : HasStrictFDerivAt (deepestEPivot H r hr hL) D_E 0 :=
    (deepestEPivot_contdiff H r hr hL).hasStrictFDerivAt (by simp)
  -- The reg-block: `D_E.comp regInCLM = id`. The reg-slice `r ↦ deepestEPivot (r,0)` has strict
  -- derivative `D_E.comp regInCLM` (chain rule) AND `id` (#91), so they agree.
  have hregIn : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ => ((r0, 0) :
      (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)))
      (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ]
        (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) 0 := by
    have := (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ]
      (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)).hasStrictFDerivAt (x := 0)
    simpa [regInCLM] using this
  have hcomp : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
      deepestEPivot H r hr hL (r0, 0)) (D_E.comp regInCLM) 0 := by
    have hsd0 : HasStrictFDerivAt (deepestEPivot H r hr hL) D_E
        (((0 : Fin (deepestNReg H r) → ℝ), (0 : Fin (deepestNGauge H r) → ℝ))) := hsd
    exact hsd0.comp (x := (0 : Fin (deepestNReg H r) → ℝ)) hregIn
  have hblock : D_E.comp (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ]
      (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
      = ContinuousLinearMap.id ℝ (Fin (deepestNReg H r) → ℝ) := by
    have h1 := hcomp.hasFDerivAt.fderiv
    have h2 := (deepestEPivot_regSlice_fderiv_id H r hr hL).hasFDerivAt.fderiv
    rw [← h1, ← h2]
  obtain ⟨e, he⟩ := regStraightenTotalCLM_equiv_of_regBlock_id (C := Fin (flatDim (deepestM H r)) → ℝ)
    D_E hblock
  exact ⟨D_E, e, hsd, he⟩

theorem deepestEPivot_base (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    deepestEPivot H r hr hL 0 = 0 := by
  -- At the origin slot, `∏(framedParamsReg 0)` is the reindexed corner `fromBlocks 1 0 0 0`
  -- (`prod_framedParamsReg_zero`); the outer `reindex` in `P` cancels it, so `P = fromBlocks 1 0 0 0`.
  funext i
  -- The matrix `P` defining the coordinates is the cancelled corner.
  have hP : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H (Fin.last L))
        (hr (Fin.last L))) (prod H (framedParamsReg H r hr hL 0)))
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 := by
    rw [prodAux_framedParamsReg_zero H r hr hL, ← Matrix.reindex_symm,
      Equiv.apply_symm_apply]
  -- Each coordinate reads a block of `P`; all blocks of `fromBlocks 1 0 0 0` give `0` in the residual.
  simp only [deepestEPivot, hP, Pi.zero_apply]
  rcases regResidualPack H r hr i with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
    simp only [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.sub_apply,
      Matrix.of_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, sub_self]

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
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (coreAbsorb : DeepestSplit H r (deepestNGauge H r) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (hsplit_base : split ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) = 0)
    (hregval : ∀ q : DeepestSplit H r (deepestNGauge H r),
      (regStraighten q).1 = deepestEPivot H r hr hL (q.1, q.2.2))
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
  -- **ASSEMBLY (B), the geometric heart — green-pending crux2's `endpoint_telescoping`.** The per-`w`
  -- two-sided bound is the banked matrix core `dlnLoss_block_squeeze` (uniform `c₁ = (2(1+t²))⁻¹`,
  -- `c₂ = 2+2t²`), once the per-`w` framed-block decomposition is supplied. That decomposition is the
  -- BRIDGE: `N_w = prod(paramsSymm w) − B` reindexed (deepest-point frame `deepestPoint_frame_exists` +
  -- crux2's `endpoint_telescoping` per-`w` conjugation + `conjugation_frobenius_comparable`) into
  -- `fromBlocks (P00−1) P01 P10 P11`, with `∑E² = ∑(regStraighten(split w)).1²` (`hregval` ⟹ reg-output is
  -- `deepestEPivot` = the E-residual) and `‖Rcore‖² = deepestCoreF (coreAbsorb(split w)).2.1` (`hcoreabs`
  -- ⟹ the cutoff-Schur core). BLOCKED on crux2's `endpoint_telescoping` interface (IsUnit P0/QL exposure
  -- requested) — wires the moment it lands; the matrix core + block-IDs are banked.
  sorry

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
  -- The reg-output is the shared `deepestEPivot` (the PIN1↔PIN2 coupling object); its three analytic
  -- props feed PIN 1's IFT peel, its concrete value feeds PIN 2's squeeze.
  obtain ⟨D_E, eShear, hEp_deriv, he_shear⟩ := deepestEPivot_deriv H r hr hL
  obtain ⟨regStraighten, hra_cont, hra_base, hra_core, hra_spec, hra_regval, hra_rlct⟩ :=
    deepest_regAbsorb_exists H r B hB hr hL (deepestNGauge H r) coreAbsorb
      (deepestCoreAbsorb_mp H r hr hL) hca_base hca_reg hca_spec
      (deepestEPivot H r hr hL) (deepestEPivot_contdiff H r hr hL)
      D_E hEp_deriv eShear he_shear (deepestEPivot_base H r hr hL)
  -- PIN 2: the loss squeeze (consuming the concrete `coreAbsorb` + `regStraighten`'s defining identities).
  obtain ⟨c₁, c₂, hc₁, hc₂, U, hU, hsq⟩ :=
    deepest_loss_squeeze H r B hB hr hL split coreAbsorb regStraighten hsplit_base
      hra_regval hca_def
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
