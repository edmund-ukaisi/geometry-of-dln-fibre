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

/-! ## The conjugated unit-set + cutoff + global continuity of `schurCutoffShiftConj`

The conjugated correction is `ContinuousAt` only on the open **conjugated unit-set** `unitSetConj` where
every conjugated pivot `det(M̄A_s + readX_s) ≠ 0`. It contains the origin WHEN every `M̄A_s = deepBlkA_s`
is a unit (`hDA`, the foundation discharged at the wire). A `ContDiffBump` with support in `unitSetConj`
gives a globally continuous cutoff `schurCutoffShiftConj`, `= 1` near `0`, vanishing off the set. -/

/-- The conjugated unit-set: gauge coords where every conjugated pivot `M̄A_s + readX_s` is invertible. -/
def unitSetConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Set ((Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) :=
  {p | ∀ s : Fin L, (deepBlkA H r B hB hr hL s + readX H r hr hL p s).det ≠ 0}

theorem isOpen_unitSetConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    IsOpen (unitSetConj H r B hB hr hL) := by
  have hrw : unitSetConj H r B hB hr hL
      = ⋂ s : Fin L, {p | (deepBlkA H r B hB hr hL s + readX H r hr hL p s).det ≠ 0} := by
    ext p; simp [unitSetConj, Set.mem_iInter]
  rw [hrw]
  refine isOpen_iInter_of_finite (fun s => ?_)
  have hcont : Continuous (fun p => (deepBlkA H r B hB hr hL s + readX H r hr hL p s).det) :=
    (continuous_const.add (continuous_readX H r hr hL s)).matrix_det
  exact hcont.isOpen_preimage _ isOpen_ne

/-- The origin lies in the conjugated unit-set when every conjugated pivot base `M̄A_s` is a unit. -/
theorem mem_unitSetConj_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s)) :
    (0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) ∈ unitSetConj H r B hB hr hL := by
  intro s
  rw [readX_zero H r hr hL s, add_zero]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (hDA s)).ne_zero

/-- An open ball `ball 0 ε ⊆ unitSetConj` (the origin's conjugated-unit nbhd; needs `hDA`). -/
theorem exists_ball_subset_unitSetConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s)) :
    ∃ ε > 0, Metric.ball (0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) ε
      ⊆ unitSetConj H r B hB hr hL := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_unitSetConj H r B hB hr hL) 0
    (mem_unitSetConj_zero H r B hB hr hL hDA)
  exact ⟨ε, hε, hball⟩

/-- The chosen conjugated-unit-ball radius `ε > 0`. -/
noncomputable def unitRadiusConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s)) : ℝ :=
  (exists_ball_subset_unitSetConj H r B hB hr hL hDA).choose

theorem unitRadiusConj_pos (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s)) :
    0 < unitRadiusConj H r B hB hr hL hDA :=
  (exists_ball_subset_unitSetConj H r B hB hr hL hDA).choose_spec.1

theorem ball_unitRadiusConj_subset (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s)) :
    Metric.ball (0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
        (unitRadiusConj H r B hB hr hL hDA)
      ⊆ unitSetConj H r B hB hr hL :=
  (exists_ball_subset_unitSetConj H r B hB hr hL hDA).choose_spec.2

/-- The conjugated cutoff bump (outer radius `ε/2`, `= 1` on the inner ball `closedBall 0 (ε/4)`). -/
noncomputable def cutoffBumpConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s)) :
    ContDiffBump (0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) where
  rIn := unitRadiusConj H r B hB hr hL hDA / 4
  rOut := unitRadiusConj H r B hB hr hL hDA / 2
  rIn_pos := by have := unitRadiusConj_pos H r B hB hr hL hDA; linarith
  rIn_lt_rOut := by have := unitRadiusConj_pos H r B hB hr hL hDA; linarith

theorem tsupport_cutoffBumpConj_subset_unitSetConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s)) :
    tsupport (⇑(cutoffBumpConj H r B hB hr hL hDA)) ⊆ unitSetConj H r B hB hr hL := by
  rw [(cutoffBumpConj H r B hB hr hL hDA).tsupport_eq]
  refine subset_trans ?_ (ball_unitRadiusConj_subset H r B hB hr hL hDA)
  intro x hx
  rw [Metric.mem_closedBall] at hx
  rw [Metric.mem_ball]
  have hpos := unitRadiusConj_pos H r B hB hr hL hDA
  show dist x 0 < unitRadiusConj H r B hB hr hL hDA
  have : (cutoffBumpConj H r B hB hr hL hDA).rOut = unitRadiusConj H r B hB hr hL hDA / 2 := rfl
  rw [this] at hx
  linarith

/-- The conjugated raw shift is `ContinuousAt p` on `unitSetConj`. -/
theorem continuousAt_schurShiftRawConj_of_mem_unitSetConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
    (hp : p ∈ unitSetConj H r B hB hr hL) :
    ContinuousAt (schurShiftRawConj H r B hB hr hL) p := by
  unfold schurShiftRawConj
  refine (continuous_paramsEquivFlat (deepestM H r)).continuousAt.comp ?_
  exact continuousAt_pi.mpr (fun s => continuousAt_schurCorrectionConj H r B hB hr hL s p (hp s))

/-- **The conjugated cutoff Schur shift** `χ_conj • schurShiftRawConj` — globally continuous,
vanishing at the origin, `= raw` on the inner ball. -/
noncomputable def schurCutoffShiftConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) :
    Fin (flatDim (deepestM H r)) → ℝ :=
  (cutoffBumpConj H r B hB hr hL hDA p) • schurShiftRawConj H r B hB hr hL p

/-- The conjugated cutoff is globally `Continuous` (via `continuous_of_tsupport`: on `tsupport χ_conj
⊆ unitSetConj` the raw shift is `ContinuousAt`; off it the bump vanishes). -/
theorem continuous_schurCutoffShiftConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s)) :
    Continuous (schurCutoffShiftConj H r B hB hr hL hDA) := by
  refine continuous_of_tsupport (fun x hx => ?_)
  have hxsupp : x ∈ tsupport (⇑(cutoffBumpConj H r B hB hr hL hDA)) := by
    refine (tsupport_smul_subset_left (⇑(cutoffBumpConj H r B hB hr hL hDA))
      (schurShiftRawConj H r B hB hr hL)) ?_
    exact hx
  have hxU : x ∈ unitSetConj H r B hB hr hL :=
    tsupport_cutoffBumpConj_subset_unitSetConj H r B hB hr hL hDA hxsupp
  have hχ : ContinuousAt (⇑(cutoffBumpConj H r B hB hr hL hDA)) x :=
    (cutoffBumpConj H r B hB hr hL hDA).continuous.continuousAt
  have hraw : ContinuousAt (schurShiftRawConj H r B hB hr hL) x :=
    continuousAt_schurShiftRawConj_of_mem_unitSetConj H r B hB hr hL x hxU
  exact hχ.smul hraw

/-- The conjugated cutoff vanishes at the origin (boundary `schurShiftRawConj 0 = 0`). -/
theorem schurCutoffShiftConj_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (hbdy : ∀ s : Fin L, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0) :
    schurCutoffShiftConj H r B hB hr hL hDA 0 = 0 := by
  have hraw0 : schurShiftRawConj H r B hB hr hL 0 = 0 := by
    unfold schurShiftRawConj
    rw [show schurCorrectionConj H r B hB hr hL 0 = (fun _ => 0 : Params (deepestM H r)) from by
      funext s; exact schurCorrectionConj_zero_boundary H r B hB hr hL s (hbdy s)]
    funext i; rfl
  simp only [schurCutoffShiftConj, hraw0, smul_zero]
