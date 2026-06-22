import DLNFibre.DLN.RLCT.Validate.DeepestSplitReindex
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeChart

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

end DLNFibre.DLN.RLCT
