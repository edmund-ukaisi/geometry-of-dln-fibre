import DLNFibre.DLN.RLCT.Validate.DeepestGaugeConstruction

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestEFullCoreConstant` — the "value-fold atom" ∂E/∂core(0)=0

The L2 diffeo-bridge's `hTilde` (PIN-1, `deepest_regAbsorb_exists`) needs, for the CONJUGATED core
absorb, that `D(deepestEFull)(0)` annihilates the core direction (so `eTilde`'s reg-reg block stays the
PIN-1 invertible frame `F` despite the conjugated `coreAbsorb.symm`'s reg→core shear). The clean,
formalizable form is the **value-constant atom**: at the regular-and-spectator-zero slice, `deepestEFull`
is INDEPENDENT of the core slot —

    deepestEFull (0, c, 0) = deepestEFull (0, 0, 0)   (∀ c)

which gives `D(fun c => deepestEFull (0,c,0))(0) = 0` (a constant has zero derivative) ⟹
`D(deepestEFull)(0).comp coreInCLM = 0` ⟹ `D_E ∘ (core-shear) = 0`.

**Why it holds (the frame-identity read, no Taylor).** `deepestEFull q` reads the reg-residual `{11,12,21}`
blocks of `P = reindex(prod(framedParamsPivot q))`. At reg=spec=0 every gauge read `X/Y/Z = 0`, so the
core slot `c` enters ONLY each framed layer's `(2,2)`-block. At `L = 2` the two layers are both boundary:
the boundary-inner frame identities `Qf (firstLayer) = 1` and `Pf (lastLayer) = 1` (hQf0/hPfL) — together
with the endpoint triangularity (hPtri layer-0 block-lower, hQtri layer-1 block-upper) — send the core's
contribution entirely into the product's `(2,2)` block, leaving `{11,12,21}` core-FREE. So the reg-residual
is constant in `c`. (Verified sympy against the real boundary frames: `{11,12,21}` is literally `(1,0,0)`
independent of `c`.)
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology Matrix

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **`deepestEFull` reads off the framed-product reg-blocks** (per-coordinate, the un-squared
`deepestEFull_sq_sum_eq_blocks`): two points whose framed reindexed products agree on the `{11,12,21}`
blocks have equal `deepestEFull`. (Each coordinate IS a block entry by the `deepestEFull` def, via
`regResidualPack`.) -/
theorem deepestEFull_eq_of_framedProd_regBlocks_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q₁ q₂ : DeepestSplit H r (deepestNGauge H r))
    (h11 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (prod H (framedParamsPivot H r hr hL J Pf Qf q₁))).toBlocks₁₁
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (prod H (framedParamsPivot H r hr hL J Pf Qf q₂))).toBlocks₁₁)
    (h12 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (prod H (framedParamsPivot H r hr hL J Pf Qf q₁))).toBlocks₁₂
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (prod H (framedParamsPivot H r hr hL J Pf Qf q₂))).toBlocks₁₂)
    (h21 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (prod H (framedParamsPivot H r hr hL J Pf Qf q₁))).toBlocks₂₁
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (prod H (framedParamsPivot H r hr hL J Pf Qf q₂))).toBlocks₂₁) :
    deepestEFull H r hr hL J Pf Qf q₁ = deepestEFull H r hr hL J Pf Qf q₂ := by
  funext i
  rcases hpack : regResidualPack H r hr i with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
    simp only [deepestEFull, hpack]
  · rw [h11]
  · rw [h12]
  · rw [h21]

end DLNFibre.DLN.RLCT
