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

end DLNFibre.DLN.RLCT
