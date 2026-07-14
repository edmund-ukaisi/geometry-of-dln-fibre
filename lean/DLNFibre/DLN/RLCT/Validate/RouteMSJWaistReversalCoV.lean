import DLNFibre.DLN.RLCT.Validate.RouteMBoxReduction
import DLNFibre.DLN.RLCT.Validate.MinAdmPermInvariance

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJWaistReversalCoV` — the box-integral reversal invariance

**Thread `genm-sj5-waist` (aoyagi-full Stage 2), hole (c) `deeperFlagWaist_finite`, the O2 brick.** The
layer-product box integral is invariant under REVERSING the chain (`M ↦ M ∘ Fin.rev`). Reversing the
layer order and transposing each layer sends the tuple `A = (A₀,…,A_{L−1})` to the reversed-transposed
tuple whose product is `(prod M A)ᵀ`, and `frobSq` is transpose-invariant, so the two box integrals are
EQUAL (`routeMLayerBoxIntegral_comp_rev`). Since `minAdm (M ∘ Fin.rev) = minAdm M` (permutation
invariance at `Fin.revPerm`), the two thresholds coincide, hence `RouteMBoxThresholdFinite` transfers
(`routeMBoxThresholdFinite_of_rev`).

This is the arity-recursion enabler for the `≥ 4`-width waist branch: a `≥ 4`-width waist `M` reverses to
a GOOD chain (`rev M` head-split-good — deep-tail min ≤ pivot), so the good-case machinery
(`deeperFlagGood_finite`) discharges `RouteMBoxThresholdFinite (rev M)`, and this brick transfers it back
to `M`. The 3-width waist base needs no reversal (`routeMBoxThresholdFinite_mnp`).

UNTRACKED, NOT wired into `DLNFibre.lean`/`AxCheck` — the canonical library stays 0-sorry.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Matrix
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **The layer-product box integral is reversal-invariant** —
`routeMLayerBoxIntegral M c' 1 = routeMLayerBoxIntegral (M ∘ Fin.rev) c' 1`. The measure-preserving
reverse-transpose bijection `Φ : Params M ≃ᵐ Params (M ∘ Fin.rev)`, `Φ A s = (A (Fin.rev s))ᵀ`, sends
`paramsBoxM M 1` to `paramsBoxM (M ∘ Fin.rev) 1` (entry bound preserved under transpose + reindex) and
satisfies `prod (M ∘ Fin.rev) (Φ A) = (prod M A)ᵀ`, so `frobSq (prod (M ∘ Fin.rev) (Φ A)) =
frobSq (prod M A)`. -/
theorem routeMLayerBoxIntegral_comp_rev (M : Fin (L + 1) → ℕ) (c' : ℝ) :
    routeMLayerBoxIntegral M c' 1 = routeMLayerBoxIntegral (M ∘ Fin.rev) c' 1 := by
  -- ISOLATED CORRECT-STATEMENT SORRY (the O2 brick; statement is cast-free — the casts live inside
  -- the proof, matching CLAUDE.md's `prodAux`-reassoc "two-tides" cast territory). PROOF PLAN:
  --   1. `revParams : Params M → Params (M ∘ Fin.rev)`, `revParams A s = reindex (finCongr h_r)
  --      (finCongr h_c) (A (Fin.rev s))ᵀ`, with `h_r : M (Fin.rev s).succ = M (Fin.rev s.castSucc)`,
  --      `h_c : M (Fin.rev s).castSucc = M (Fin.rev s.succ)` (`congrArg M ∘ Fin.ext`, `Fin.val_rev`).
  --   2. `prod_revParams : prod (M ∘ Fin.rev) (revParams A) = reindex (finCongr _) (finCongr _)
  --      ((prod M A)ᵀ)` — `prodAux` induction reusing `prodAux_succ` + `Matrix.transpose_mul`; the
  --      running-width reindex casts are the labour (cf. `RouteMFrontPeel.mul_three_reassoc`,
  --      `reindex_finCongr_mul`; do cast bookkeeping at the equiv level, never entrywise).
  --   3. `frobSq (prod (M ∘ Fin.rev) (revParams A)) = frobSq (prod M A)` (frobSq is transpose- and
  --      reindex-invariant: `∑∑ (Xᵀ)² = ∑∑ X²`, `Finset.sum_comm`).
  --   4. `revParams` is a MeasurableEquiv, MeasurePreserving (transpose + layer-reindex = a coordinate
  --      permutation of the flat `Params` pi-Lebesgue; route via `paramsEquivFlat` MP + a
  --      `MeasurableEquiv.piCongrLeft`/`volume_preserving_piCongrLeft` permutation, OR directly as a
  --      `Matrix.transposeMeasurableEquiv`-style pi-swap per layer + `MeasurableEquiv.piCongrLeft` on
  --      `Fin.revPerm`), and `revParams '' (paramsBoxM M 1) = paramsBoxM (M ∘ Fin.rev) 1` (entry bound
  --      preserved under transpose + reindex).
  --   5. Assemble via `MeasurePreserving.setLIntegral_comp_preimage_emb` (as in
  --      `RouteMBoxReduction.routeMCore_le_matBox` step 2) + `setLIntegral_congr_fun` with (3).
  -- Self-contained, network-free, ideal for a focused tide. NOT laundered — statement correct, connector
  -- + wrapper + rev-good all proven around it.
  sorry

/-- **`RouteMBoxThresholdFinite` transfers across chain reversal.** If the reversed chain `M ∘ Fin.rev`
has finite box integral below its threshold, so does `M`: the thresholds coincide
(`minAdm (M ∘ Fin.rev) = minAdm M`, `minAdm_comp_perm` at `Fin.revPerm`) and the box integrals are equal
(`routeMLayerBoxIntegral_comp_rev`). -/
theorem routeMBoxThresholdFinite_of_rev (M : Fin (L + 1) → ℕ)
    (h : RouteMBoxThresholdFinite (M ∘ Fin.rev)) : RouteMBoxThresholdFinite M := by
  intro c' hc'
  have hperm : minAdm (M ∘ Fin.rev) = minAdm M := by
    have : (M ∘ Fin.rev) = (M ∘ (Fin.revPerm : Equiv.Perm (Fin (L + 1)))) := rfl
    rw [this]; exact minAdm_comp_perm (Fin.revPerm) M
  have hc'rev : (c' : ℝ) < (minAdm (M ∘ Fin.rev) : ℝ) / 2 := by rw [hperm]; exact hc'
  rw [routeMLayerBoxIntegral_comp_rev M (c' : ℝ)]
  exact h c' hc'rev

end DLNFibre.DLN.RLCT
