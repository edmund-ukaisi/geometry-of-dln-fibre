import DLNFibre.DLN.RLCT.Validate.DeepestHsub3regGen
import DLNFibre.DLN.RLCT.Validate.DeepestHmoveGen
import DLNFibre.DLN.RLCT.Validate.DeepestSchurSmooth
import DLNFibre.DLN.RLCT.Validate.DeepestPsiSplitGenLeftCol

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestChainUnitGerm` — the base-chain eventual-unit germs (#120 `hstep2`, item 2)

The `∀ᶠ`-unit infrastructure the concrete `hsub3reg` germ needs. `deepestEFull_sq_sum_eq_of_chain_movedC`
(`DeepestHsub3regGen`) consumes, for the base chain `C = deepestChain (framedParamsPivot … q₂)`, the three
`∀ k`-unit hypotheses `hP` (`(partProd C k).toBlocks₁₁`), `hA` (`(C k).toBlocks₁₁`), `hN` (`nMix C k`). At
the deepest point (`q₂ = split wstar`) every base-chain layer IS the block-normal corner `diag(I_r, 0)`
(`framedParamsPivot_eq_frame_of_front` + the corner normal form `hNF`/`hcorner`), so there all three are the
identity — a unit. Continuity of the chain entries in `q` (`contDiff_framedParamsPivot_entry` through the
fixed reindex) plus determinant continuity + `ContinuousAt.eventually_ne` then propagate the units to a
neighborhood. This module builds those eventual-unit germs and assembles them (with the banked move identity
`psiSplitRawGen_deepestChain_hmove`) into the concrete general-`L` reg-preservation germ `hsub3reg`.

The `∀ k` reduces to a finite range: off the used prefix (`k ≥ L`) the chain layer IS the fixed corner
default — `(C k).toBlocks₁₁ = 1` (`deepestChain_tail_toBlocks₁₁`), `(C k).toBlocks₂₁ = 0`
(`deepestChain_tail_toBlocks₂₁`), so `nMix C k = 1` and `(partProd C k).toBlocks₁₁` stabilises — all
UNCONDITIONAL units. Only `k < L` (`k ≤ L` for `partProd`) needs the eventual argument.
-/

open Matrix MeasureTheory Topology
open scoped ENNReal

namespace DLNFibre.DLN.RLCT

set_option linter.unusedSectionVars false

variable {L : ℕ}

/-! ## Generic eventual-`IsUnit` via determinant continuity -/

/-- **Eventual `IsUnit` from determinant continuity + a nonzero value.** If `x ↦ det (M x)` is continuous
at `x₀` and `det (M x₀) ≠ 0`, then `M x` is a unit for `x` near `x₀`. (`ContinuousAt.eventually_ne` +
`Matrix.isUnit_iff_isUnit_det`.) -/
theorem eventually_isUnit_of_continuousAt_det {X : Type*} [TopologicalSpace X]
    {n : Type*} [Fintype n] [DecidableEq n] (M : X → Matrix n n ℝ) (x₀ : X)
    (hcont : ContinuousAt (fun x => (M x).det) x₀) (hne : (M x₀).det ≠ 0) :
    ∀ᶠ x in nhds x₀, IsUnit (M x) := by
  filter_upwards [hcont.eventually_ne hne] with x hx
  exact (Matrix.isUnit_iff_isUnit_det (M x)).mpr (isUnit_iff_ne_zero.mpr hx)

/-! ## Continuity of the base-chain entries in the split parameter -/

/-- Each entry of the base chain `deepestChain (framedParamsPivot … q) k` is `ContDiff ⊤` in `q`. For
`k < L` the layer is a fixed double reindex of the `framedParamsPivot` layer `⟨k, _⟩`
(`contDiff_framedParamsPivot_entry`); for `k ≥ L` it is the constant corner default. -/
theorem contDiff_deepestChain_framedParamsPivot_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (i : Fin r ⊕ Fin (deepestChainWidth H k - r))
    (j : Fin r ⊕ Fin (deepestChainWidth H (k + 1) - r)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : DeepestSplit H r (deepestNGauge H r) =>
      deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k i j) := by
  by_cases hk : k < L
  · -- k < L: reindex of the framedParamsPivot layer ⟨k, hk⟩.
    have heq : (fun q : DeepestSplit H r (deepestNGauge H r) =>
        deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k i j)
        = fun q => framedParamsPivot H r hr hL J Pf Qf q ⟨k, hk⟩
            ((finCongr (deepestChainWidth_castSucc H k hk)).symm
              ((deepestChainSplit H r hr k).symm i))
            ((finCongr (deepestChainWidth_succ H k hk)).symm
              ((deepestChainSplit H r hr (k + 1)).symm j)) := by
      funext q
      rw [deepestChain, Matrix.reindex_apply, Matrix.submatrix_apply, deepestChainLayer, dif_pos hk,
        Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [heq]
    exact contDiff_framedParamsPivot_entry H r hr hL J Pf Qf ⟨k, hk⟩ _ _
  · -- k ≥ L: the layer is the constant corner default (independent of the parameter `q`).
    have hmat : ∀ q : DeepestSplit H r (deepestNGauge H r),
        deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k
          = deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0) k := by
      intro q
      rw [deepestChain, deepestChain, deepestChainLayer, deepestChainLayer]
      simp only [dif_neg hk]
    have heq : (fun q : DeepestSplit H r (deepestNGauge H r) =>
        deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k i j)
        = fun _ => deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0) k i j := by
      funext q; rw [hmat q]
    rw [heq]
    exact contDiff_const

/-- Continuity (in the flat parameter `x`, through the homeomorphism `split`) of the base-chain
`toBlocks₁₁` determinant. -/
theorem continuous_deepestChain_toBlocks₁₁_det (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r)) (k : ℕ) :
    Continuous (fun x => (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf (split x)) k).toBlocks₁₁.det) := by
  apply Continuous.matrix_det
  refine continuous_matrix (fun i j => ?_)
  have hcd := contDiff_deepestChain_framedParamsPivot_entry H r hr hL J Pf Qf k (Sum.inl i) (Sum.inl j)
  exact (hcd.continuous.comp split.continuous)

/-! ## The value of the base-chain `toBlocks₁₁` at the basepoint (`= I`, hence a unit) -/

/-- The reindexed corner-normal-form `toBlocks₁₁` is the identity. For any matrix that reindexes (through a
`finCongr` width bridge) to the split-coordinate corner shape `if i = j ∧ i < r then 1 else 0`, its
`deepestChain`-split `(1,1)` block reads the first-`r` corner entries, which are the identity. -/
theorem deepestChainLayer_corner_toBlocks₁₁ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (A : Params H) (k : ℕ) (hk : k < L)
    (hcor : A ⟨k, hk⟩ = Matrix.of (fun (i : Fin (H (⟨k, hk⟩ : Fin L).castSucc))
        (j : Fin (H (⟨k, hk⟩ : Fin L).succ)) => if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0)) :
    (deepestChain H r hr A k).toBlocks₁₁ = (1 : Matrix (Fin r) (Fin r) ℝ) := by
  funext i j
  rw [Matrix.toBlocks₁₁, Matrix.of_apply, deepestChain, Matrix.reindex_apply, Matrix.submatrix_apply,
    deepestChainSplit, deepestChainSplit, rThresholdSplit_symm_inl, rThresholdSplit_symm_inl,
    deepestChainLayer, dif_pos hk, Matrix.reindex_apply, Matrix.submatrix_apply, hcor, Matrix.of_apply,
    finCongr_symm, finCongr_symm, finCongr_apply, finCongr_apply, Matrix.one_apply]
  simp only [Fin.coe_cast, Fin.coe_castLE]
  by_cases h : i = j
  · subst h; simp [i.isLt]
  · rw [if_neg h, if_neg (fun hc => h (Fin.ext hc.1))]

/-- The split-coordinate `fromBlocks 1 0 0 0` reindexed back to ambient coordinates is the corner shape
`if i = j ∧ i < r then 1 else 0`. (Local copy of the `DeepestGaugeConstruction` private helper.) -/
theorem reindex_symm_fromBlocks_one_eq_corner (r a b : ℕ) (ha : r ≤ a) (hb : r ≤ b) :
    Matrix.reindex (rThresholdSplit r a ha).symm (rThresholdSplit r b hb).symm
        (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
      = Matrix.of (fun (i : Fin a) (j : Fin b) =>
          if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.symm_symm]
  rcases hi : (rThresholdSplit r a ha) i with p | p <;>
    rcases hj : (rThresholdSplit r b hb) j with q | q
  · rw [Matrix.fromBlocks_apply₁₁]
    have hip : i = p.castLE ha := by
      rw [← rThresholdSplit_symm_inl r a ha p, ← hi, Equiv.symm_apply_apply]
    have hjq : j = q.castLE hb := by
      rw [← rThresholdSplit_symm_inl r b hb q, ← hj, Equiv.symm_apply_apply]
    simp only [Matrix.one_apply, Matrix.of_apply, hip, hjq, Fin.coe_castLE]
    by_cases hpq : p = q
    · subst hpq; simp [p.isLt]
    · rw [if_neg hpq, if_neg]; rintro ⟨hval, _⟩; exact hpq (Fin.ext hval)
  · rw [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    have hjq : j = ⟨r + q, by omega⟩ := by
      rw [← rThresholdSplit_symm_inr r b hb q, ← hj, Equiv.symm_apply_apply]
    have hip : i = p.castLE ha := by
      rw [← rThresholdSplit_symm_inl r a ha p, ← hi, Equiv.symm_apply_apply]
    simp only [Matrix.of_apply, hip, hjq, Fin.coe_castLE]
    rw [if_neg]; rintro ⟨hval, hlt⟩; omega
  · rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    have hip : i = ⟨r + p, by omega⟩ := by
      rw [← rThresholdSplit_symm_inr r a ha p, ← hi, Equiv.symm_apply_apply]
    simp only [Matrix.of_apply, hip]
    rw [if_neg]; rintro ⟨hval, hlt⟩; omega
  · rw [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
    have hip : i = ⟨r + p, by omega⟩ := by
      rw [← rThresholdSplit_symm_inr r a ha p, ← hi, Equiv.symm_apply_apply]
    simp only [Matrix.of_apply, hip]
    rw [if_neg]; rintro ⟨hval, hlt⟩; omega

/-- The base-chain `toBlocks₁₁` at the deepest basepoint is the identity, at every layer `k < L`. The
framed layer there is `Pf · deepest · Qf` (`framedParamsPivot_eq_frame_of_front`); for a non-last layer the
corner normal form `hNF` makes it the split corner (`deepestChainLayer_corner_toBlocks₁₁`), for the last
layer the pivot corner `hcorner` gives the reindexed `fromBlocks 1 0 0 0` directly. -/
theorem deepestChain_wstar_toBlocks₁₁_eq_one (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront' : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hNF : ∀ s : Fin L, (s : ℕ) + 1 ≠ L →
      Pf s * (deepestPoint H r B hB hr hL s) * Qf s
        = Matrix.of (fun (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) =>
            if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0))
    (hPfL : Pf (lastLayer hL)
      = (1 : Matrix (Fin (H (lastLayer hL).castSucc)) (Fin (H (lastLayer hL).castSucc)) ℝ))
    (hcorner' : Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        ((deepestPoint H r B hB hr hL (lastLayer hL)) * Qf (lastLayer hL))
        = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (k : ℕ) (hk : k < L) :
    (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf
        (split ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)))) k).toBlocks₁₁
      = (1 : Matrix (Fin r) (Fin r) ℝ) := by
  set wstar := (paramsEquivFlat H) (deepestPoint H r B hB hr hL) with hwstar
  -- The framed layer at the basepoint is `Pf · deepest · Qf`.
  have hframe : framedParamsPivot H r hr hL J Pf Qf (split wstar) ⟨k, hk⟩
      = Pf ⟨k, hk⟩ * deepestPoint H r B hB hr hL ⟨k, hk⟩ * Qf ⟨k, hk⟩ := by
    rw [hsplit wstar,
      framedParamsPivot_eq_frame_of_front H r B hB hr hL J hJfront' Pf Qf hNF hPfL hcorner' wstar ⟨k, hk⟩,
      show (paramsEquivFlat H).symm wstar = deepestPoint H r B hB hr hL from
        (paramsEquivFlat H).symm_apply_apply _]
  -- Reduce to: the framed layer at `⟨k, hk⟩` is the split corner shape, then `deepestChainLayer_corner`.
  apply deepestChainLayer_corner_toBlocks₁₁ H r hr _ k hk
  rw [hframe]
  by_cases hlast : (k : ℕ) + 1 = L
  · -- Last layer: `Pf (last) = 1`; `hcorner` says `deepest · Qf` reindexes to `fromBlocks 1 0 0 0`,
    -- i.e. it IS the corner shape (`reindex_symm_fromBlocks_one_eq_corner`).
    have hkl : (⟨k, hk⟩ : Fin L) = lastLayer hL := Fin.ext (by simp only [lastLayer]; omega)
    subst hJfront'
    rw [pivotThresholdSplit_pivotJSucc_frontEmbed H r hr hL] at hcorner'
    rw [hkl, hPfL, Matrix.one_mul]
    have hdQ : deepestPoint H r B hB hr hL (lastLayer hL) * Qf (lastLayer hL)
        = Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
            (rThresholdSplit r (H (lastLayer hL).succ) (hr _)).symm
            (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
      rw [← Matrix.reindex_symm, ← hcorner', Equiv.symm_apply_apply]
    rw [hdQ, reindex_symm_fromBlocks_one_eq_corner]
  · -- Non-last layer: `Pf · deepest · Qf` is the split corner (`hNF`).
    exact hNF ⟨k, hk⟩ hlast

/-- The base-chain layer `toBlocks₁₁` is a unit at every layer, near the deepest basepoint. -/
theorem eventually_isUnit_deepestChain_toBlocks₁₁ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront' : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hNF : ∀ s : Fin L, (s : ℕ) + 1 ≠ L →
      Pf s * (deepestPoint H r B hB hr hL s) * Qf s
        = Matrix.of (fun (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) =>
            if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0))
    (hPfL : Pf (lastLayer hL)
      = (1 : Matrix (Fin (H (lastLayer hL).castSucc)) (Fin (H (lastLayer hL).castSucc)) ℝ))
    (hcorner' : Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        ((deepestPoint H r B hB hr hL (lastLayer hL)) * Qf (lastLayer hL))
        = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w) (k : ℕ) :
    ∀ᶠ x in nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
      IsUnit ((deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf (split x)) k).toBlocks₁₁) := by
  by_cases hk : k < L
  · refine eventually_isUnit_of_continuousAt_det _ _
      (continuous_deepestChain_toBlocks₁₁_det H r hr hL J Pf Qf split k).continuousAt ?_
    rw [deepestChain_wstar_toBlocks₁₁_eq_one H r B hB hr hL J hJfront' Pf Qf hNF hPfL hcorner'
      split hsplit k hk, Matrix.det_one]
    exact one_ne_zero
  · filter_upwards with x
    rw [deepestChain_tail_toBlocks₁₁ H r hr _ k hk]
    exact isUnit_one

end DLNFibre.DLN.RLCT
