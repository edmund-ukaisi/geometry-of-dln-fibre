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

end DLNFibre.DLN.RLCT
