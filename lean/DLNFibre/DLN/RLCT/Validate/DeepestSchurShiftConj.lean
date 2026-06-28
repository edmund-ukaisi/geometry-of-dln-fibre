import DLNFibre.DLN.RLCT.Validate.DeepestSchurShift
import DLNFibre.DLN.RLCT.Validate.DeepestLDUReadback

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestSchurShiftConj` — the CONJUGATED cutoff Schur shift

The W-a **conjugated** core-shift (pivot the actual deepest layer block `M̄A_s + readX_s`, off-diagonals
`M̄Z_s + readZ_s` / `M̄Y_s + readY_s`), parallel to the bare `schurCutoffShift` in `DeepestSchurShift`.
The bare path stays untouched (it is consumed by `DeepestGermCharge` and the L≥3 legs); these `…Conj`
parallels are used ONLY in the L=2 wire's `hstep2` (the bare↔conjugated MP-shear RLCT bridge — the
conjugated absorb is a LOCAL RLCT intermediate, never a chart field, so its derivative never enters
PIN-1; NO atom needed). The conjugated correction `schurCorrectionConj` itself + the dict-match keystone
`absorbedCoreConj_eq_schurCore` live in `DeepestSchurShift` / `DeepestLDUReadback` (banked, clean-three).

**Continuity, NOT strict-derivative.** The MP-shear route needs only that `schurCutoffShiftConj` is
globally continuous and vanishes at the origin (so the conjugated `coreShearHomeo` is a basepoint-fixing
homeomorphism, hence MP via `measurePreserving_coreShear`). The strict-derivative-`0` fact (which is
FALSE — `D(schurCorrectionConj)(0) = −M̄Z_0·M̄A_0⁻¹·D(readY_0) ≠ 0`, the "atom") is NOT needed.

The conjugated pivot `M̄A_s + readX_s` is invertible near the origin iff `M̄A_s = deepBlkA_s` is a unit
(`readX → 0` at `0`). That unit-ness (`hDA`) is threaded as a hypothesis here — discharged at the wire
(layer-0 via `deepestPoint_leadingBlock_isUnit`/`htop`; layer-`(L−1)` via the column-WLOG dual).
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology Matrix
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The conjugated raw shift + its origin value -/

/-- **The conjugated raw Schur shift**: the per-layer conjugated corrections assembled and flat-encoded
into the core slot (parallel to `schurShiftRaw`, with `schurCorrectionConj` in place of
`schurCorrection`). -/
noncomputable def schurShiftRawConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) :
    Fin (flatDim (deepestM H r)) → ℝ :=
  paramsEquivFlat (deepestM H r) (schurCorrectionConj H r B hB hr hL p)

/-- At the origin the conjugated raw shift vanishes: at `p = 0` the reads are `0`, and at the two L=2
boundary layers one off-diagonal deepest block vanishes (`deepBlkY_0 = 0` / `deepBlkZ_(L−1) = 0`), so
each conjugated correction has a zero factor. (At a layer where both `M̄Y_s` and `M̄Z_s` could be
nonzero this would need more; the boundary structure is what makes the L=2 origin value `0`.) -/
theorem schurCorrectionConj_zero_boundary (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (hbdy : deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0) :
    schurCorrectionConj H r B hB hr hL 0 s = 0 := by
  unfold schurCorrectionConj
  simp only [readX_zero, readY_zero, readZ_zero, add_zero]
  rcases hbdy with hY | hZ
  · rw [hY, Matrix.mul_zero]
  · rw [hZ, neg_zero, Matrix.zero_mul, Matrix.zero_mul]

/-! ## Continuity of the conjugated correction (CONTINUITY only — NOT strict-derivative) -/

/-- `ContinuousAt` rectangular matrix multiplication (a public copy of the bare file's private helper). -/
private theorem continuousAt_matrix_mul' {X mm nn pp : Type*} [TopologicalSpace X] [Fintype nn]
    {A : X → Matrix mm nn ℝ} {C : X → Matrix nn pp ℝ} {x : X}
    (hA : ContinuousAt A x) (hC : ContinuousAt C x) :
    ContinuousAt (fun q => A q * C q) x := by
  refine continuousAt_pi.mpr (fun i => continuousAt_pi.mpr (fun j => ?_))
  simp only [Matrix.mul_apply]
  have hAelem : ∀ (i' : mm) (k : nn), Continuous (fun M : Matrix mm nn ℝ => M i' k) :=
    fun i' k => (continuous_apply k).comp (continuous_apply i')
  have hCelem : ∀ (k : nn) (j' : pp), Continuous (fun M : Matrix nn pp ℝ => M k j') :=
    fun k j' => (continuous_apply j').comp (continuous_apply k)
  have hsum : ∀ k : nn, ContinuousAt (fun q => A q i k * C q k j) x := fun k =>
    ((hAelem i k).continuousAt.comp hA).mul ((hCelem k j).continuousAt.comp hC)
  have := tendsto_finset_sum (Finset.univ : Finset nn)
    (fun k _ => (hsum k : Filter.Tendsto (fun q => A q i k * C q k j) (𝓝 x) _))
  simpa [ContinuousAt] using this

/-- The conjugated pivot inverse `(M̄A_s + readX p s)⁻¹` is `ContinuousAt p` where its det `≠ 0`
(`M̄A_s = deepBlkA_s` is constant; `readX` continuous). -/
theorem continuousAt_inv_deepBlkA_add_readX (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
    (hdet : (deepBlkA H r B hB hr hL s + readX H r hr hL p s).det ≠ 0) :
    ContinuousAt (fun q => (deepBlkA H r B hB hr hL s + readX H r hr hL q s)⁻¹) p := by
  have hadd : ContinuousAt
      (fun q => deepBlkA H r B hB hr hL s + readX H r hr hL q s) p :=
    (continuous_const.add (continuous_readX H r hr hL s)).continuousAt
  refine ContinuousAt.comp ?_ hadd
  apply continuousAt_matrix_inv
  obtain ⟨u, hu⟩ := Ne.isUnit hdet
  rw [← hu]
  exact NormedRing.inverse_continuousAt u

/-- The conjugated per-layer correction is `ContinuousAt p` where the conjugated pivot det `≠ 0`. -/
theorem continuousAt_schurCorrectionConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
    (hdet : (deepBlkA H r B hB hr hL s + readX H r hr hL p s).det ≠ 0) :
    ContinuousAt (fun q => schurCorrectionConj H r B hB hr hL q s) p := by
  unfold schurCorrectionConj
  refine continuousAt_matrix_mul' (continuousAt_matrix_mul' ?_
    (continuousAt_inv_deepBlkA_add_readX H r B hB hr hL s p hdet)) ?_
  · exact (continuous_const.add (continuous_readZ H r hr hL s)).continuousAt.neg
  · exact (continuous_const.add (continuous_readY H r hr hL s)).continuousAt
