import DLNFibre.Core.Aoyagi.BlockDivision

/-!
# `Core.Aoyagi.BlockShearDivision` — the structural `u_pivot` division under `blow-up ∘ shear` (FIX-A)

seat-w0l3, L3 δ=1 (post FIX-A order flip: `stepMap = blockBlowupMap S p ∘ (pivot-keeping shear)`,
blow-up OUTERMOST). With the blow-up outermost and a shear that KEEPS the pivot coordinate
(`hpiv : ∀ v, sh v pivot = v pivot`), every CENTER coordinate pulls back with an EXACT `v_pivot`
factor:

  `(blockBlowupMap S p (sh v)) j = v_pivot · blockBlowupCoordQuot p j (sh v)`  (`j ∈ S`),

no vanishing-to-division lemma, no analyticity of the shear — the factor is closed-form (the shear sits
INSIDE the blow-up's argument, so `blockBlowupMap_center_eq` fires directly and `hpiv` rewrites the
pivot value). This is the δ=1 exact division at the residual level: a center-supported combination (the
`SupportedOn` ideal-membership form) pulls back to `v_pivot · (∑ (c∘σ)·quot∘sh)` — the strict-transform
residual, with the child witness law `q' = q∘σ` (division-free, FIX-RESID). Shape-independent (does not
touch `foldResid`'s terminal guard); consumed by the δ=1 leaf against the flipped `stepMap`.
-/

open MeasureTheory Set Filter Topology RLCT

namespace DLNFibre.Core.Aoyagi

variable {D : ℕ}

/-- **The structural pivot division (center coordinate, `blow-up ∘ pivot-keeping shear`).** For `j ∈ S`
and a shear `sh` keeping the pivot (`sh v pivot = v pivot`), the pulled-back center coordinate factors
as `v_pivot · blockBlowupCoordQuot p j (sh v)`, EXACTLY (closed-form quotient, no localization). -/
theorem blockBlowupMap_comp_shear_center_eq (S : Finset (Fin D)) (p : Fin D) {j : Fin D} (hj : j ∈ S)
    (sh : (Fin D → ℝ) → (Fin D → ℝ)) (hpiv : ∀ v, sh v p = v p) (v : Fin D → ℝ) :
    blockBlowupMap S p (sh v) j = v p * blockBlowupCoordQuot p j (sh v) := by
  rw [blockBlowupMap_center_eq S p hj (sh v), hpiv]

/-- **The strict-transform residual division (center-supported combination, `blow-up ∘ shear`).** A
residual entry that is a combination `∑ a, cₐ · (center coord kₐ)` of center coordinates pulls back,
after `σ = blockBlowupMap S p ∘ sh` with `sh` pivot-keeping, to `v_pivot · (∑ a, (cₐ∘σ)·(quot(kₐ)∘sh))`
— the EXACT `/v_pivot` of the δ=1 witness law, division-free (the `v_pivot` sits in the child dominant
`b'`, the quotient is the strict-transform residual). -/
theorem blockBlowup_comp_shear_center_comb_eq {n : ℕ} (S : Finset (Fin D)) (p : Fin D)
    (c : Fin n → (Fin D → ℝ) → ℝ) (k : Fin n → Fin D) (hk : ∀ a, k a ∈ S)
    (sh : (Fin D → ℝ) → (Fin D → ℝ)) (hpiv : ∀ v, sh v p = v p) (v : Fin D → ℝ) :
    (∑ a, c a (blockBlowupMap S p (sh v)) * (blockBlowupMap S p (sh v)) (k a))
      = v p * ∑ a, c a (blockBlowupMap S p (sh v)) * blockBlowupCoordQuot p (k a) (sh v) := by
  rw [blockBlowup_center_comb_eq S p c k hk (sh v), hpiv]

/-- **Continuity of the strict-transform quotient** (`blow-up ∘ shear`): the δ=1 child witness quotient
`fun v ↦ ∑ a, (cₐ∘σ)·(quot(kₐ)∘sh)` is `ContinuousOn W` when the coefficients `cₐ` are `ContinuousOn V`,
`sh` is continuous, and `σ = blockBlowupMap S p ∘ sh` maps `W` into `V`. Regularity enters HERE only
(the equality above is regularity-free); with the flipped order, `sh` continuous suffices — no
vanishing-to-division. -/
theorem continuousOn_blockBlowup_comp_shear_quot {n : ℕ} (S : Finset (Fin D)) (p : Fin D)
    (c : Fin n → (Fin D → ℝ) → ℝ) (k : Fin n → Fin D) {V W : Set (Fin D → ℝ)}
    (sh : (Fin D → ℝ) → (Fin D → ℝ)) (hsh : Continuous sh)
    (hc : ∀ a, ContinuousOn (c a) V)
    (hmaps : Set.MapsTo (fun v ↦ blockBlowupMap S p (sh v)) W V) :
    ContinuousOn
      (fun v ↦ ∑ a, c a (blockBlowupMap S p (sh v)) * blockBlowupCoordQuot p (k a) (sh v)) W := by
  refine continuousOn_finset_sum _ (fun a _ ↦ ?_)
  have hσcont : Continuous (fun v ↦ blockBlowupMap S p (sh v)) :=
    (continuous_blockBlowupMap S p).comp hsh
  exact ((hc a).comp hσcont.continuousOn hmaps).mul
    (((continuous_blockBlowupCoordQuot p (k a)).comp hsh).continuousOn)

end DLNFibre.Core.Aoyagi
