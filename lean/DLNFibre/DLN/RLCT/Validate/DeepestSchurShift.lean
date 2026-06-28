import DLNFibre.DLN.RLCT.Validate.DeepestSplitReindex
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeChart
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestSchurShift` — the cutoff Schur core-shift (#44c, PIN 0)

The concrete `shift : (reg, spec) → core` fed to `coreShearHomeo` to build `coreAbsorb` (PIN 0). The
honest gauge-absorption maps the raw core block `T_s` to the per-layer **Schur complement**
`S_s = T_s − Z_s(I+X_s)⁻¹Y_s` (g156/#61: the additive Schur, NOT the multiplicative unit
`T·(I−VY)⁻¹` which is `0` whenever `T=0`). The shift adds `−Z_s(I+X_s)⁻¹Y_s`, read off the gauge
blocks `(X_s, Y_s, Z_s)` living in the reg+spec slots (via `regGaugeSlotEquiv`).

## The pole problem and the cutoff (the team-lead 2026-06-22 call: BOTH absorptions stay ≃ₜ via cutoff)

`(I+X_s)⁻¹` has poles where `det(I+X_s)=0`; the honest Schur correction is NOT globally continuous.
But `coreShearHomeo` REQUIRES a GLOBALLY continuous `shift` (it is a homeomorphism, and
`rlctAtOn_squeeze` downstream needs the absorbed `Φ` GLOBALLY measurable — a local diffeo breaks it).
Resolution: a **cutoff**. Near the deepest point `det(I+X_s) = det 1 = 1 ≠ 0`, so the Schur correction
is continuous on an open neighbourhood `U ∋ 0`. Multiplying by a `ContDiffBump` `χ` with
`tsupport χ ⊆ U` (and `χ = 1` near `0`) gives a globally continuous map that vanishes off `U`, equals
the honest Schur correction on a neighbourhood of `0` (`χ = 1` there), and vanishes at `0`. Since
`rlctAtOn` is a germ at `0` and the loss-squeeze is local, the germ-at-`0` agreement is all that is
consumed — the cutoff is invisible to both PIN 0's RLCT peel and PIN 2's local squeeze.

## Status

Building (PIN 0). `schurShiftRaw` (the honest, pole-bearing correction) + its continuity on the
det-nonzero set + vanishing at `0`; then `schurCutoffShift` (the bump-cutoff) + its global continuity
+ vanishing. PIN 0's four obligations follow from `coreShear_satisfies_coreAbsorb` (shift-agnostic).
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology Matrix
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The per-layer gauge blocks read off the (reg, spec) slot

The shift's domain is `(Fin nReg → ℝ) × (Fin nGauge → ℝ)` (the reg + spectator slots after `split`).
`regGaugeSlotEquiv` un-flattens these into `RegGaugeIdx → ℝ`, from which the per-layer `(X_s, Y_s, Z_s)`
blocks are read (`gaugeSlotRead`'s inner half, here typed as a function of `(reg, spec)`). Each read is
continuous (composition of the homeomorphism `regGaugeSlotEquiv` with coordinate projections). -/

/-- The per-layer `X_s` block (`r×r`) read off the gauge `(reg, spec)` slot. -/
noncomputable def readX (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) (s : Fin L) :
    Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of (fun i j => regGaugeSlotEquiv H r hr hL p ⟨s, Sum.inl (Sum.inl (i, j))⟩)

/-- The per-layer `Y_s` block (`r×(H_{s+1}−r)`) read off the gauge `(reg, spec)` slot. -/
noncomputable def readY (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) (s : Fin L) :
    Matrix (Fin r) (Fin (H s.succ - r)) ℝ :=
  Matrix.of (fun i j => regGaugeSlotEquiv H r hr hL p ⟨s, Sum.inl (Sum.inr (i, j))⟩)

/-- The per-layer `Z_s` block (`(H_s−r)×r`) read off the gauge `(reg, spec)` slot. -/
noncomputable def readZ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) (s : Fin L) :
    Matrix (Fin (H s.castSucc - r)) (Fin r) ℝ :=
  Matrix.of (fun i j => regGaugeSlotEquiv H r hr hL p ⟨s, Sum.inr (i, j)⟩)

/-- The gauge `(reg, spec)` read is continuous: each entry is a coordinate of the homeomorphism
`regGaugeSlotEquiv` composed with `continuous_apply`. -/
theorem continuous_readX (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) :
    Continuous (fun p => readX H r hr hL p s) := by
  refine continuous_matrix (fun i j => ?_)
  simp only [readX, Matrix.of_apply]
  exact (continuous_apply _).comp (regGaugeSlotEquiv H r hr hL).continuous

theorem continuous_readY (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) :
    Continuous (fun p => readY H r hr hL p s) := by
  refine continuous_matrix (fun i j => ?_)
  simp only [readY, Matrix.of_apply]
  exact (continuous_apply _).comp (regGaugeSlotEquiv H r hr hL).continuous

theorem continuous_readZ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) :
    Continuous (fun p => readZ H r hr hL p s) := by
  refine continuous_matrix (fun i j => ?_)
  simp only [readZ, Matrix.of_apply]
  exact (continuous_apply _).comp (regGaugeSlotEquiv H r hr hL).continuous

/-- The gauge-slot un-flattening sends the zero coordinates to the zero index function (it is a
coordinate reindexing of products of `ℝ`, no scaling). The reads at the origin are therefore `0`. -/
theorem regGaugeSlotEquiv_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    regGaugeSlotEquiv H r hr hL 0 = 0 := by
  unfold regGaugeSlotEquiv
  ext idx
  change (Equiv.piCongrLeft (fun _ => ℝ) (regGaugeIdxSplit H r hr hL)).symm
      ((Equiv.sumPiEquivProdPi (fun _ => ℝ)).symm 0) idx = 0
  rw [Equiv.piCongrLeft_symm_apply]
  cases (regGaugeIdxSplit H r hr hL) idx <;> simp [Equiv.sumPiEquivProdPi]

/-- At the origin gauge slot, every block is `0` (the deepest point is the block-normal rank-`r`
chain: `X_s = Y_s = Z_s = 0`). -/
theorem readX_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) :
    readX H r hr hL 0 s = 0 := by
  ext i j
  simp only [readX, Matrix.of_apply, Matrix.zero_apply, regGaugeSlotEquiv_zero H r hr hL,
    Pi.zero_apply]

theorem readY_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) :
    readY H r hr hL 0 s = 0 := by
  ext i j
  simp only [readY, Matrix.of_apply, Matrix.zero_apply, regGaugeSlotEquiv_zero H r hr hL,
    Pi.zero_apply]

theorem readZ_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) :
    readZ H r hr hL 0 s = 0 := by
  ext i j
  simp only [readZ, Matrix.of_apply, Matrix.zero_apply, regGaugeSlotEquiv_zero H r hr hL,
    Pi.zero_apply]

/-! ## The raw (pole-bearing) per-layer Schur correction

The honest gauge-absorption maps `T_s ↦ S_s = T_s − Z_s(I+X_s)⁻¹Y_s`. The shift adds the correction
`schurCorrection p s = −Z_s·(1+X_s)⁻¹·Y_s` per layer, assembled into a `Params (deepestM H r)` tuple
and flat-encoded by `paramsEquivFlat (deepestM H r)`. `(1+X_s)⁻¹` is the Mathlib matrix inverse
(`Inv.inv`, `= 0` on singular matrices) — continuous at every point where `det(1+X_s) ≠ 0`, in
particular near the origin where `1+X_s(0) = 1`. -/

/-- The per-layer Schur correction `−Z_s·(1+X_s)⁻¹·Y_s` (a `Params (deepestM H r)` layer block). -/
noncomputable def schurCorrection (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) :
    Params (deepestM H r) :=
  fun s => -(readZ H r hr hL p s) * (1 + readX H r hr hL p s)⁻¹ * (readY H r hr hL p s)

/-- The raw Schur shift: the per-layer corrections assembled and flat-encoded into the core slot. -/
noncomputable def schurShiftRaw (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) :
    Fin (flatDim (deepestM H r)) → ℝ :=
  paramsEquivFlat (deepestM H r) (schurCorrection H r hr hL p)

/-! ## The W-a CONJUGATED per-layer Schur correction (the dict-match keystone)

The bare `schurCorrection` pivots on `1 + readX_s`, which presumes the deepest layer `(1,1)`-block is the
identity. It is NOT (deepest boundary `A11 ≠ 1`), so the bare absorbed core ≠ the Score (the W-a falsity).
The CONJUGATED correction reads the **full reindexed decode layer** `reindex(decode w)_s` — pivot the
actual `(1,1)`-block `M̄A_s + readX_s` (`M̄A_s := (reindex deepestPoint_s).toBlocks₁₁`), full off-diagonal
blocks `M̄Z_s + readZ_s` / `M̄Y_s + readY_s`. The absorbed core `decode(q).core_s + conjCorr_s` is then
exactly the `(1,1)`-Schur core of the reindexed decode layer (`conjCore`), which the standalone
`prod_deepestM_eq_schur_ldu_readback` ties to the Score. This `schurCorrectionConj` is `B`-dependent
(through `deepestPoint`). -/

/-- The reindexed deepest-layer `(1,1)`-block `M̄A_s` (the actual pivot base, `≠ 1` at the boundary). -/
noncomputable def deepBlkA (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) : Matrix (Fin r) (Fin r) ℝ :=
  (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
      (rThresholdSplit r (H s.succ) (hr s.succ)) (deepestPoint H r B hB hr hL s)).toBlocks₁₁

/-- The reindexed deepest-layer `(1,2)`-block `M̄Y_s` (deepest off-diagonal Y; `0` at layer-0 boundary). -/
noncomputable def deepBlkY (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) :
    Matrix (Fin r) (Fin (H s.succ - r)) ℝ :=
  (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
      (rThresholdSplit r (H s.succ) (hr s.succ)) (deepestPoint H r B hB hr hL s)).toBlocks₁₂

/-- The reindexed deepest-layer `(2,1)`-block `M̄Z_s` (deepest off-diagonal Z; `0` at layer-(L−1) bdry). -/
noncomputable def deepBlkZ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) :
    Matrix (Fin (H s.castSucc - r)) (Fin r) ℝ :=
  (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
      (rThresholdSplit r (H s.succ) (hr s.succ)) (deepestPoint H r B hB hr hL s)).toBlocks₂₁

/-- **The W-a conjugated Schur correction** `−(M̄Z_s + readZ_s)·(M̄A_s + readX_s)⁻¹·(M̄Y_s + readY_s)`,
read off the FULL reindexed decode layer (deepest constants + gauge deviations). -/
noncomputable def schurCorrectionConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) :
    Params (deepestM H r) :=
  fun s => -(deepBlkZ H r B hB hr hL s + readZ H r hr hL p s)
    * (deepBlkA H r B hB hr hL s + readX H r hr hL p s)⁻¹
    * (deepBlkY H r B hB hr hL s + readY H r hr hL p s)

/-- `ContinuousAt` rectangular matrix multiplication: each output entry is a finite sum of products
of entries, continuous-at by `ContinuousAt.mul` + `tendsto_finset_sum`. -/
private theorem continuousAt_matrix_mul {X mm nn pp : Type*} [TopologicalSpace X] [Fintype nn]
    {A : X → Matrix mm nn ℝ} {B : X → Matrix nn pp ℝ} {x : X}
    (hA : ContinuousAt A x) (hB : ContinuousAt B x) :
    ContinuousAt (fun q => A q * B q) x := by
  refine continuousAt_pi.mpr (fun i => continuousAt_pi.mpr (fun j => ?_))
  simp only [Matrix.mul_apply]
  have hAelem : ∀ (i' : mm) (k : nn), Continuous (fun M : Matrix mm nn ℝ => M i' k) :=
    fun i' k => (continuous_apply k).comp (continuous_apply i')
  have hBelem : ∀ (k : nn) (j' : pp), Continuous (fun M : Matrix nn pp ℝ => M k j') :=
    fun k j' => (continuous_apply j').comp (continuous_apply k)
  have hsum : ∀ k : nn, ContinuousAt (fun q => A q i k * B q k j) x := fun k =>
    ((hAelem i k).continuousAt.comp hA).mul ((hBelem k j).continuousAt.comp hB)
  have := tendsto_finset_sum (Finset.univ : Finset nn)
    (fun k _ => (hsum k : Filter.Tendsto (fun q => A q i k * B q k j) (𝓝 x) _))
  simpa [ContinuousAt] using this

/-- The matrix inverse `(1 + readX p s)⁻¹` is `ContinuousAt p` when `det(1 + readX p s) ≠ 0`. -/
theorem continuousAt_inv_one_add_readX (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
    (hdet : (1 + readX H r hr hL p s).det ≠ 0) :
    ContinuousAt (fun q => (1 + readX H r hr hL q s)⁻¹) p := by
  have hadd : ContinuousAt (fun q => (1 : Matrix (Fin r) (Fin r) ℝ) + readX H r hr hL q s) p :=
    (continuous_const.add (continuous_readX H r hr hL s)).continuousAt
  refine ContinuousAt.comp ?_ hadd
  apply continuousAt_matrix_inv
  obtain ⟨u, hu⟩ := Ne.isUnit hdet
  rw [← hu]
  exact NormedRing.inverse_continuousAt u

/-- The per-layer Schur correction is `ContinuousAt p` when `det(1 + readX p s) ≠ 0`. -/
theorem continuousAt_schurCorrection (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
    (hdet : (1 + readX H r hr hL p s).det ≠ 0) :
    ContinuousAt (fun q => schurCorrection H r hr hL q s) p := by
  unfold schurCorrection
  exact continuousAt_matrix_mul
    (continuousAt_matrix_mul ((continuous_readZ H r hr hL s).continuousAt.neg)
      (continuousAt_inv_one_add_readX H r hr hL s p hdet))
    (continuous_readY H r hr hL s).continuousAt

/-- At the origin, each per-layer Schur correction vanishes (`Z_s(0) = 0`, so `−0·…·… = 0`). -/
theorem schurCorrection_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    schurCorrection H r hr hL 0 = fun _ => 0 := by
  funext s
  simp only [schurCorrection, readZ_zero H r hr hL s, neg_zero, Matrix.zero_mul]

/-- At the origin the raw Schur shift vanishes (`paramsEquivFlat` sends the zero tuple to `0`). -/
theorem schurShiftRaw_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    schurShiftRaw H r hr hL 0 = 0 := by
  unfold schurShiftRaw
  rw [schurCorrection_zero H r hr hL]
  funext i
  show (paramsEquivFlat (deepestM H r)) (fun _ => 0) i = 0
  rfl

/-! ## The det-nonzero unit set and the cutoff

The honest Schur correction is `ContinuousAt` only on the open **unit set** `unitSet` where every
`det(1 + X_s) ≠ 0`. It contains the origin (`det(1 + 0) = det 1 = 1 ≠ 0`). A `ContDiffBump` `χ` with
`tsupport χ ⊆ unitSet` and `χ = 1` near the origin gives the **globally continuous** cutoff
`schurCutoffShift = χ • schurShiftRaw` — continuous everywhere (continuous off `tsupport χ` by
vanishing, `ContinuousAt` on `tsupport χ ⊆ unitSet` since `schurShiftRaw` is), equal to the honest
correction on the inner ball where `χ = 1`, and `0` at the origin. -/

/-- The open unit set: the gauge coords where every pivot `1 + X_s` is invertible. -/
def unitSet (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Set ((Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) :=
  {p | ∀ s : Fin L, (1 + readX H r hr hL p s).det ≠ 0}

theorem isOpen_unitSet (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    IsOpen (unitSet H r hr hL) := by
  have hrw : unitSet H r hr hL
      = ⋂ s : Fin L, {p | (1 + readX H r hr hL p s).det ≠ 0} := by
    ext p; simp [unitSet, Set.mem_iInter]
  rw [hrw]
  refine isOpen_iInter_of_finite (fun s => ?_)
  have hcont : Continuous (fun p => (1 + readX H r hr hL p s).det) :=
    (continuous_const.add (continuous_readX H r hr hL s)).matrix_det
  exact hcont.isOpen_preimage _ isOpen_ne

theorem mem_unitSet_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    (0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) ∈ unitSet H r hr hL := by
  intro s
  rw [readX_zero H r hr hL s, add_zero, Matrix.det_one]
  exact one_ne_zero

/-- An open ball radius `ε > 0` with `ball 0 ε ⊆ unitSet` (the origin's unit-neighbourhood). -/
theorem exists_ball_subset_unitSet (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ∃ ε > 0, Metric.ball (0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) ε
      ⊆ unitSet H r hr hL := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_unitSet H r hr hL) 0
    (mem_unitSet_zero H r hr hL)
  exact ⟨ε, hε, hball⟩

/-- The chosen unit-ball radius `ε > 0` (with `ball 0 ε ⊆ unitSet`). -/
noncomputable def unitRadius (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) : ℝ :=
  (exists_ball_subset_unitSet H r hr hL).choose

theorem unitRadius_pos (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) : 0 < unitRadius H r hr hL :=
  (exists_ball_subset_unitSet H r hr hL).choose_spec.1

theorem ball_unitRadius_subset (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Metric.ball (0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
        (unitRadius H r hr hL)
      ⊆ unitSet H r hr hL :=
  (exists_ball_subset_unitSet H r hr hL).choose_spec.2

/-- The cutoff bump on the gauge slot: a `ContDiffBump` at the origin with outer radius `ε/2`
(half the unit-ball radius), so its (closed) support sits inside `unitSet`, and `= 1` on the inner
ball `closedBall 0 (ε/4)`. -/
noncomputable def cutoffBump (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ContDiffBump (0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) where
  rIn := unitRadius H r hr hL / 4
  rOut := unitRadius H r hr hL / 2
  rIn_pos := by have := unitRadius_pos H r hr hL; linarith
  rIn_lt_rOut := by have := unitRadius_pos H r hr hL; linarith

/-- The raw Schur shift is `ContinuousAt p` on the unit set (every pivot invertible there): each
layer correction is `ContinuousAt`, and `paramsEquivFlat` is continuous. -/
theorem continuousAt_schurShiftRaw_of_mem_unitSet (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
    (hp : p ∈ unitSet H r hr hL) :
    ContinuousAt (schurShiftRaw H r hr hL) p := by
  unfold schurShiftRaw
  refine (continuous_paramsEquivFlat (deepestM H r)).continuousAt.comp ?_
  refine continuousAt_pi.mpr (fun s => continuousAt_schurCorrection H r hr hL s p (hp s))

/-- The (closed) support of the cutoff bump sits inside the unit set: `tsupport χ = closedBall 0
(ε/2) ⊆ ball 0 ε ⊆ unitSet`. -/
theorem tsupport_cutoffBump_subset_unitSet (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    tsupport (⇑(cutoffBump H r hr hL)) ⊆ unitSet H r hr hL := by
  rw [(cutoffBump H r hr hL).tsupport_eq]
  refine subset_trans ?_ (ball_unitRadius_subset H r hr hL)
  intro x hx
  rw [Metric.mem_closedBall] at hx
  rw [Metric.mem_ball]
  have hpos := unitRadius_pos H r hr hL
  show dist x 0 < unitRadius H r hr hL
  have : (cutoffBump H r hr hL).rOut = unitRadius H r hr hL / 2 := rfl
  rw [this] at hx
  linarith

/-! ## The cutoff Schur shift (the concrete `shift` fed to `coreShearHomeo`) -/

/-- **The cutoff Schur shift** (PIN 0's `shift`): `χ • schurShiftRaw`, the honest Schur correction
multiplied by the gauge-slot bump. Globally continuous (the bump's support sits in the unit set),
vanishing at the origin, and equal to the honest correction on the inner ball. -/
noncomputable def schurCutoffShift (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) :
    Fin (flatDim (deepestM H r)) → ℝ :=
  (cutoffBump H r hr hL p) • schurShiftRaw H r hr hL p

/-- **The cutoff Schur shift is globally continuous.** Off `tsupport χ` it vanishes (continuous);
on `tsupport χ ⊆ unitSet` the raw correction is `ContinuousAt` and `χ` continuous, so the product
is `ContinuousAt`. `continuous_of_tsupport` glues. -/
theorem continuous_schurCutoffShift (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Continuous (schurCutoffShift H r hr hL) := by
  refine continuous_of_tsupport (fun x hx => ?_)
  -- `x ∈ tsupport (χ • rawSchur) ⊆ tsupport χ ⊆ unitSet`, so `rawSchur` is `ContinuousAt x`.
  have hxsupp : x ∈ tsupport (⇑(cutoffBump H r hr hL)) := by
    refine (tsupport_smul_subset_left (⇑(cutoffBump H r hr hL)) (schurShiftRaw H r hr hL)) ?_
    exact hx
  have hxU : x ∈ unitSet H r hr hL := tsupport_cutoffBump_subset_unitSet H r hr hL hxsupp
  have hχ : ContinuousAt (⇑(cutoffBump H r hr hL)) x :=
    (cutoffBump H r hr hL).continuous.continuousAt
  have hraw : ContinuousAt (schurShiftRaw H r hr hL) x :=
    continuousAt_schurShiftRaw_of_mem_unitSet H r hr hL x hxU
  exact hχ.smul hraw

/-- **The cutoff Schur shift vanishes at the origin** (`schurShiftRaw 0 = 0`, so `χ(0) • 0 = 0`). -/
theorem schurCutoffShift_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    schurCutoffShift H r hr hL 0 = 0 := by
  simp only [schurCutoffShift, schurShiftRaw_zero H r hr hL, smul_zero]

/-- **On the inner ball the cutoff equals the honest Schur correction** (`χ = 1` there). The germ-at-0
agreement PIN 2's loss-squeeze consumes (`rlctAtOn`/the squeeze are local). -/
theorem schurCutoffShift_eq_raw_of_mem_closedBall (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
    (hp : p ∈ Metric.closedBall (0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
      ((cutoffBump H r hr hL).rIn)) :
    schurCutoffShift H r hr hL p = schurShiftRaw H r hr hL p := by
  simp only [schurCutoffShift, (cutoffBump H r hr hL).one_of_mem_closedBall hp, one_smul]

/-- The inner ball `closedBall 0 (ε/4)` is a neighbourhood of the origin (`ε > 0`). -/
theorem closedBall_rIn_mem_nhds (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Metric.closedBall (0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
        ((cutoffBump H r hr hL).rIn) ∈ 𝓝 0 :=
  Metric.closedBall_mem_nhds 0 (cutoffBump H r hr hL).rIn_pos

/-! ## The abstract regStraighten cutoff (PIN 1's (C)-fallback packaging)

The `regStraighten` field (#90 (C) fallback) is a bare TOTAL continuous self-map of `DeepestSplit`,
straightening the raw regular slot into the residual `E` near `0` and tapering to the identity outside.
Since only CONTINUITY (not a global homeomorphism) is required, the honest construction is a
**bump-interpolation** `q ↦ ((χ g)·Ereg(g) + (1−χ g)·q.1, q.2)` (`g = (q.1, q.2.2)` the gauge slot)
between the residual reg-target `Ereg` and the raw reg slot — globally continuous, core/spectator-fixing
(only `.1` moves), `= 0` at the origin (where `χ = 1` and `Ereg 0 = 0`), and `= Ereg` on the inner ball
(the germ PIN 2 consumes). Crucially `Ereg` and `χ` read only the GAUGE slot `(reg, spec)` (NOT the core
slot), so the reg-output depends only on `(q.1, q.2.2)` — the `hra_regdep` hypothesis the RLCT reduction
`rlctAtOn_regAbsorb_reduce` needs. Abstract over `Ereg` (the concrete general-L residual + its
`dE(0) = id` derivative are the producer's, supplied to `#72`); banks the cutoff half regardless. -/

/-- The bump-interpolated regular straightening: `χ·Ereg + (1−χ)·(raw reg)` on the reg slot, core +
spectator fixed. `Ereg`/`χ` read only the GAUGE slot `g = (q.1, q.2.2)` (reg + spectator), so the
reg-output is core-independent. `χ` a bump on `Reg × Spec` (`= 1` near `0`); `Ereg` the residual
reg-target reading reg + spectator. -/
noncomputable def regStraightenCutoff (H : Fin (L + 1) → ℕ) (r nGauge : ℕ)
    (Ereg : ((Fin (deepestNReg H r) → ℝ) × (Fin nGauge → ℝ)) → (Fin (deepestNReg H r) → ℝ))
    (χ : ContDiffBump (0 : (Fin (deepestNReg H r) → ℝ) × (Fin nGauge → ℝ)))
    (q : DeepestSplit H r nGauge) : DeepestSplit H r nGauge :=
  ((χ (q.1, q.2.2) • Ereg (q.1, q.2.2) + (1 - χ (q.1, q.2.2)) • q.1 :
      Fin (deepestNReg H r) → ℝ), q.2)

/-- `regStraightenCutoff` is globally continuous (`χ`, `Ereg` continuous in the gauge slot, the
core/spectator slot `q.2` carried unchanged). -/
theorem continuous_regStraightenCutoff (H : Fin (L + 1) → ℕ) (r nGauge : ℕ)
    (Ereg : ((Fin (deepestNReg H r) → ℝ) × (Fin nGauge → ℝ)) → (Fin (deepestNReg H r) → ℝ))
    (hE : Continuous Ereg)
    (χ : ContDiffBump (0 : (Fin (deepestNReg H r) → ℝ) × (Fin nGauge → ℝ))) :
    Continuous (regStraightenCutoff H r nGauge Ereg χ) := by
  have hg : Continuous fun q : DeepestSplit H r nGauge => (q.1, q.2.2) :=
    continuous_fst.prodMk (continuous_snd.comp continuous_snd)
  refine Continuous.prodMk (Continuous.add ?_ ?_) continuous_snd
  · exact (χ.continuous.comp hg).smul (hE.comp hg)
  · exact (continuous_const.sub (χ.continuous.comp hg)).smul continuous_fst

/-- `regStraightenCutoff` fixes the core slot (only the reg component is touched). -/
theorem regStraightenCutoff_core (H : Fin (L + 1) → ℕ) (r nGauge : ℕ)
    (Ereg : ((Fin (deepestNReg H r) → ℝ) × (Fin nGauge → ℝ)) → (Fin (deepestNReg H r) → ℝ))
    (χ : ContDiffBump (0 : (Fin (deepestNReg H r) → ℝ) × (Fin nGauge → ℝ)))
    (q : DeepestSplit H r nGauge) :
    (regStraightenCutoff H r nGauge Ereg χ q).2.1 = q.2.1 := rfl

/-- `regStraightenCutoff` fixes the spectator slot. -/
theorem regStraightenCutoff_spectator (H : Fin (L + 1) → ℕ) (r nGauge : ℕ)
    (Ereg : ((Fin (deepestNReg H r) → ℝ) × (Fin nGauge → ℝ)) → (Fin (deepestNReg H r) → ℝ))
    (χ : ContDiffBump (0 : (Fin (deepestNReg H r) → ℝ) × (Fin nGauge → ℝ)))
    (q : DeepestSplit H r nGauge) :
    (regStraightenCutoff H r nGauge Ereg χ q).2.2 = q.2.2 := rfl

/-- **The reg-output is core-independent** (`hra_regdep` for `rlctAtOn_regAbsorb_reduce`): the reg
component depends only on the reg + spectator slots, since `Ereg`/`χ` read only the gauge slot. -/
theorem regStraightenCutoff_regdep (H : Fin (L + 1) → ℕ) (r nGauge : ℕ)
    (Ereg : ((Fin (deepestNReg H r) → ℝ) × (Fin nGauge → ℝ)) → (Fin (deepestNReg H r) → ℝ))
    (χ : ContDiffBump (0 : (Fin (deepestNReg H r) → ℝ) × (Fin nGauge → ℝ)))
    (q q' : DeepestSplit H r nGauge) (h1 : q.1 = q'.1) (h2 : q.2.2 = q'.2.2) :
    (regStraightenCutoff H r nGauge Ereg χ q).1 = (regStraightenCutoff H r nGauge Ereg χ q').1 := by
  show χ (q.1, q.2.2) • Ereg (q.1, q.2.2) + (1 - χ (q.1, q.2.2)) • q.1
    = χ (q'.1, q'.2.2) • Ereg (q'.1, q'.2.2) + (1 - χ (q'.1, q'.2.2)) • q'.1
  rw [h1, h2]

/-- `regStraightenCutoff` fixes the origin (`χ 0 = 1`, `Ereg 0 = 0`, so the reg slot is
`1·0 + 0·0 = 0`). -/
theorem regStraightenCutoff_zero (H : Fin (L + 1) → ℕ) (r nGauge : ℕ)
    (Ereg : ((Fin (deepestNReg H r) → ℝ) × (Fin nGauge → ℝ)) → (Fin (deepestNReg H r) → ℝ))
    (hE0 : Ereg (0, 0) = 0)
    (χ : ContDiffBump (0 : (Fin (deepestNReg H r) → ℝ) × (Fin nGauge → ℝ))) :
    regStraightenCutoff H r nGauge Ereg χ 0 = 0 := by
  have hχ0 : χ 0 = 1 := χ.one_of_mem_closedBall (by simp [χ.rIn_pos.le])
  refine Prod.ext ?_ rfl
  show χ ((0 : DeepestSplit H r nGauge).1, (0 : DeepestSplit H r nGauge).2.2)
      • Ereg ((0 : DeepestSplit H r nGauge).1, (0 : DeepestSplit H r nGauge).2.2)
    + (1 - χ ((0 : DeepestSplit H r nGauge).1, (0 : DeepestSplit H r nGauge).2.2))
      • (0 : DeepestSplit H r nGauge).1 = 0
  show χ ((0 : Fin (deepestNReg H r) → ℝ), (0 : Fin nGauge → ℝ))
      • Ereg ((0 : Fin (deepestNReg H r) → ℝ), (0 : Fin nGauge → ℝ))
    + (1 - χ ((0 : Fin (deepestNReg H r) → ℝ), (0 : Fin nGauge → ℝ))) • (0 : Fin (deepestNReg H r) → ℝ)
    = 0
  rw [show ((0 : Fin (deepestNReg H r) → ℝ), (0 : Fin nGauge → ℝ))
        = (0 : (Fin (deepestNReg H r) → ℝ) × (Fin nGauge → ℝ)) from rfl, hχ0]
  simp only [one_smul, sub_self, zero_smul, add_zero]
  exact hE0

/-- On the inner ball (gauge slot) the cutoff straightening equals the honest residual reg-target
(`χ = 1` there) — the germ-at-0 agreement PIN 2's loss-squeeze consumes. -/
theorem regStraightenCutoff_eq_of_mem_closedBall (H : Fin (L + 1) → ℕ) (r nGauge : ℕ)
    (Ereg : ((Fin (deepestNReg H r) → ℝ) × (Fin nGauge → ℝ)) → (Fin (deepestNReg H r) → ℝ))
    (χ : ContDiffBump (0 : (Fin (deepestNReg H r) → ℝ) × (Fin nGauge → ℝ)))
    (q : DeepestSplit H r nGauge)
    (hq : (q.1, q.2.2) ∈ Metric.closedBall
      (0 : (Fin (deepestNReg H r) → ℝ) × (Fin nGauge → ℝ)) χ.rIn) :
    regStraightenCutoff H r nGauge Ereg χ q = (Ereg (q.1, q.2.2), q.2) := by
  have hχq : χ (q.1, q.2.2) = 1 := χ.one_of_mem_closedBall hq
  refine Prod.ext ?_ rfl
  show χ (q.1, q.2.2) • Ereg (q.1, q.2.2) + (1 - χ (q.1, q.2.2)) • q.1 = Ereg (q.1, q.2.2)
  rw [hχq]; simp

end DLNFibre.DLN.RLCT
