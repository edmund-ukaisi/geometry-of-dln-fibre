import DLNFibre.DLN.RLCT.Validate.RouteMSchurDirectMorseP
import DLNFibre.DLN.RLCT.Validate.RouteMSchurCapAP

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurCapACarveP` — the `Fin p` cap-A carve chain

The output-width-`p` generalisation of `RouteMSchurFiring`'s cap-A ratio-residual carve
(`schurRatioResidGen_mid` + its deps), closing the interior-stratum / corank-leaf branch
`schurCoreP_capA` of `schurRecStep_p` (task #146).

The cap-A carve is the recursion-driven branch: for `c' < schurLambdaP p r` with the binding stratum
interior (`schurLambdaP p r > p/2`), the angular ratio-residual is peeled by the N2b `j = 1` minor-pivot
Schur split — the top `Fin p` Morse block (threshold `p/2`) is dominated, leaving the SHIFTED corank-`(r−1)`
core at exponent `c'' = c' − p/2 ∈ (0, schurLambdaP p (r−1))`, closed by the abstract lower IH.

## What is `4 → p` here vs. what is reused verbatim

The `S`-column-width `Fin 4 → Fin p` swap touches only the integrand width:
* `frobSqGP_ne_zero_ae` / `frobSqShiftGP_ne_zero_ae` — the a.e.-positivity of the free / shifted core at
  output width `p` (the `Fin 4`-hardcoded `coreEntryPolyG`/`coreJoinG`/`frobSqG_ne_zero_ae` analogs).
* `resolvedShiftRGP_le` — the JOINT brick: the a.e. `Fin p` Morse peel (`core_T_peel_le_aeG` at `m+1=p`,
  threshold `p/2`) + the DONE `schurResidGP_translate_le`.
* `innerSGenP_eq_norm` / `innerSGenCarveP_le` — the pivot-normalised form + the N2b carve heart
  (`schur_minorPivot_split (p := p)`, `frobSqTopRowP_eq_shearP`, `stepShearP_r` — all DONE in DirectMorseP).
* `schurRatioResidGenP_mid` / `schurRatioResidGenP` — the carve assembly + subcritical fold.
* `schur_matBoxGenP_chart_capA_lt_top` / `schurCoreP_capA_interior` — the cap-A per-chart + the `r²`-chart
  cover (mirror of DirectMorseP's `schur_matBoxGenP_chart_lt_top` / `schurCoreP_directMorse`, swapping the
  cap-B angular residual for the carve).

REUSED VERBATIM from `RouteMSchurFiring` (the `r²−1` ratio reshape, `S`-width-FREE): `RmatGnorm`,
`RmatGnorm_pivot`, `RmatGnorm_offpivot_le`, `RmatGnorm_eq_slot`, `slotMatG`, `cellR`, `zσG`, `zEG`,
`zEG_symm_apply`, `zσG_slot`, `RmatGnorm_carve_*`, `ScCarve_eq`, `bgShiftG`, `bgShiftG_entry_le`,
`piRatioG_symm_offpivot_le`, `ofReal_rpow_le_const_mul`, `ofReal_rpow_neg_le_one_addG`, `zEG_fst_apply`,
`zEG_snd_apply`. The `Fin p`-general bricks REUSED from DirectMorseP / CapAP: `frobSqTopRowP_eq_shearP`,
`frobSq_rmatMul_permGP`, `stepShearP_r`, `innerSGenP`, `measurable_innerSGenP`, `innerSGenP_offpivot`,
`coreSchurGenValP`, `coreSchurGenValP_lt_top`, `schurResidGP_translate_le`.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-! ## The `Fin p` a.e.-positivity of the free / shifted core (4 → p of `frobSqG_ne_zero_ae`) -/

/-- The joint coords `(Fin m → Fin m → ℝ) × (Fin m → Fin p → ℝ) ≃ᵐ ((Fin m × Fin m) ⊕ (Fin m × Fin p) → ℝ)`
(`Fin p` analog of `coreJoinG`; `matToProdG` is already `(a,b)`-general). -/
noncomputable def coreJoinGP (m p : ℕ) :
    ((Fin m → Fin m → ℝ) × (Fin m → Fin p → ℝ))
      ≃ᵐ (((Fin m × Fin m) ⊕ (Fin m × Fin p)) → ℝ) :=
  ((matToProdG m m).prodCongr (matToProdG m p)).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin m × Fin m) ⊕ (Fin m × Fin p) => ℝ)).symm

theorem coreJoinGP_inl (m p : ℕ) (q : (Fin m → Fin m → ℝ) × (Fin m → Fin p → ℝ)) (i j : Fin m) :
    coreJoinGP m p q (Sum.inl (i, j)) = q.1 i j := by
  show (MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin m × Fin m) ⊕ (Fin m × Fin p) => ℝ)).symm
      (matToProdG m m q.1, matToProdG m p q.2) (Sum.inl (i, j)) = q.1 i j
  rw [MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  show matToProdG m m q.1 (i, j) = q.1 i j
  rw [matToProdG_apply]

theorem coreJoinGP_inr (m p : ℕ) (q : (Fin m → Fin m → ℝ) × (Fin m → Fin p → ℝ)) (k : Fin m) (j : Fin p) :
    coreJoinGP m p q (Sum.inr (k, j)) = q.2 k j := by
  show (MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin m × Fin m) ⊕ (Fin m × Fin p) => ℝ)).symm
      (matToProdG m m q.1, matToProdG m p q.2) (Sum.inr (k, j)) = q.2 k j
  rw [MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  show matToProdG m p q.2 (k, j) = q.2 k j
  rw [matToProdG_apply]

theorem measurePreserving_coreJoinGP (m p : ℕ) :
    MeasurePreserving (coreJoinGP m p)
      (volume : Measure ((Fin m → Fin m → ℝ) × (Fin m → Fin p → ℝ)))
      (volume : Measure (((Fin m × Fin m) ⊕ (Fin m × Fin p)) → ℝ)) := by
  unfold coreJoinGP
  refine MeasurePreserving.trans ?_
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : (Fin m × Fin m) ⊕ (Fin m × Fin p) => ℝ))
  rw [show (volume : Measure ((Fin m → Fin m → ℝ) × (Fin m → Fin p → ℝ))) = volume.prod volume
    from rfl,
    show (volume : Measure (((Fin m × Fin m) → ℝ) × ((Fin m × Fin p) → ℝ))) = volume.prod volume
    from rfl]
  exact (measurePreserving_matToProdG m m).prod (measurePreserving_matToProdG m p)

open MvPolynomial in
/-- The `(0,0)`-entry polynomial of `Δ·S` over the joint index `(Fin m × Fin m) ⊕ (Fin m × Fin p)`
(`Fin p` analog of `coreEntryPolyG`; needs `0 < p` for the `⟨0⟩ : Fin p` column). -/
noncomputable def coreEntryPolyGP (m p : ℕ) (hm : 0 < m) (hp : 0 < p) :
    MvPolynomial ((Fin m × Fin m) ⊕ (Fin m × Fin p)) ℝ :=
  ∑ k : Fin m,
    X (Sum.inl (⟨0, hm⟩, k)) * X (Sum.inr (k, ⟨0, hp⟩))

open MvPolynomial in
theorem eval_coreEntryPolyGP (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (q : (Fin m → Fin m → ℝ) × (Fin m → Fin p → ℝ)) :
    MvPolynomial.eval (coreJoinGP m p q) (coreEntryPolyGP m p hm hp)
      = ∑ k : Fin m, q.1 ⟨0, hm⟩ k * q.2 k ⟨0, hp⟩ := by
  rw [coreEntryPolyGP, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X, coreJoinGP_inl, coreJoinGP_inr]

open MvPolynomial in
theorem coreEntryPolyGP_ne_zero (m p : ℕ) (hm : 0 < m) (hp : 0 < p) :
    coreEntryPolyGP m p hm hp ≠ 0 := by
  intro h0
  set Δ0 : Fin m → Fin m → ℝ := fun i k => if i = ⟨0, hm⟩ ∧ k = ⟨0, hm⟩ then 1 else 0 with hΔ0
  set S0 : Fin m → Fin p → ℝ := fun k j => if k = ⟨0, hm⟩ ∧ j = ⟨0, hp⟩ then 1 else 0 with hS0
  have hval : MvPolynomial.eval (coreJoinGP m p (Δ0, S0)) (coreEntryPolyGP m p hm hp) = 1 := by
    rw [eval_coreEntryPolyGP]
    rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
    · rw [hΔ0, hS0]; simp
    · intro k _ hk; rw [hΔ0]; simp [hk]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h0] at hval; simp at hval

/-- **The free core is positive a.e. at output width `p`** (`Fin p` analog of `frobSqG_ne_zero_ae`). -/
theorem frobSqGP_ne_zero_ae (m p : ℕ) (hm : 0 < m) (hp : 0 < p) :
    ∀ᵐ q : (Fin m → Fin m → ℝ) × (Fin m → Fin p → ℝ) ∂(volume),
      0 < frobSq (rmatMul q.1 q.2) := by
  have hae : ∀ᵐ x : ((Fin m × Fin m) ⊕ (Fin m × Fin p)) → ℝ,
      MvPolynomial.eval x (coreEntryPolyGP m p hm hp) ≠ 0 :=
    ae_eval_ne_zero_fintype (coreEntryPolyGP m p hm hp) (coreEntryPolyGP_ne_zero m p hm hp)
  have hms : MeasurableSet
      {x : ((Fin m × Fin m) ⊕ (Fin m × Fin p)) → ℝ |
        MvPolynomial.eval x (coreEntryPolyGP m p hm hp) ≠ 0} := by
    have : MeasurableSet {x : ((Fin m × Fin m) ⊕ (Fin m × Fin p)) → ℝ |
        MvPolynomial.eval x (coreEntryPolyGP m p hm hp) = 0} :=
      (MvPolynomial.continuous_eval (coreEntryPolyGP m p hm hp)).measurable (measurableSet_singleton 0)
    exact this.compl.congr (by ext x; simp)
  have hpull : ∀ᵐ q : (Fin m → Fin m → ℝ) × (Fin m → Fin p → ℝ) ∂(volume),
      MvPolynomial.eval (coreJoinGP m p q) (coreEntryPolyGP m p hm hp) ≠ 0 := by
    rw [← (measurePreserving_coreJoinGP m p).map_eq] at hae
    exact (ae_map_iff (measurePreserving_coreJoinGP m p).measurable.aemeasurable hms).1 hae
  refine hpull.mono (fun q hq => ?_)
  rw [eval_coreEntryPolyGP] at hq
  have hentry : (rmatMul q.1 q.2) ⟨0, hm⟩ ⟨0, hp⟩ = ∑ k, q.1 ⟨0, hm⟩ k * q.2 k ⟨0, hp⟩ := rfl
  have hne : (rmatMul q.1 q.2) ⟨0, hm⟩ ⟨0, hp⟩ ≠ 0 := by rw [hentry]; exact hq
  have hpos : 0 < ((rmatMul q.1 q.2) ⟨0, hm⟩ ⟨0, hp⟩) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
  refine lt_of_lt_of_le hpos ?_
  unfold frobSq
  calc ((rmatMul q.1 q.2) ⟨0, hm⟩ ⟨0, hp⟩) ^ 2
      = ∑ j ∈ {(⟨0, hp⟩ : Fin p)}, ((rmatMul q.1 q.2) ⟨0, hm⟩ j) ^ 2 := by simp
    _ ≤ ∑ j, ((rmatMul q.1 q.2) ⟨0, hm⟩ j) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    _ ≤ ∑ i, ∑ j, ((rmatMul q.1 q.2) i j) ^ 2 :=
        Finset.single_le_sum (f := fun i => ∑ j, ((rmatMul q.1 q.2) i j) ^ 2)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ _)

/-- **The shifted free core is positive a.e. at output width `p`** (`Fin p` analog of
`frobSqShiftG_ne_zero_ae`). -/
theorem frobSqShiftGP_ne_zero_ae (m p : ℕ) (hm : 0 < m) (hp : 0 < p) (Sh : Fin m → Fin m → ℝ) :
    ∀ᵐ q : (Fin m → Fin m → ℝ) × (Fin m → Fin p → ℝ) ∂(volume),
      0 < frobSq (rmatMul (fun i j => q.1 i j - Sh i j) q.2) := by
  set τ : (Fin m → Fin m → ℝ) × (Fin m → Fin p → ℝ) → (Fin m → Fin m → ℝ) × (Fin m → Fin p → ℝ) :=
    fun q => (q.1 + (fun i j => -Sh i j), q.2) with hτ
  have hmpΔ : MeasurePreserving (fun Δ : Fin m → Fin m → ℝ => Δ + (fun i j => -Sh i j))
      volume volume :=
    measurePreserving_add_right volume (fun i j => -Sh i j)
  have hmp : MeasurePreserving τ volume volume := by
    rw [show (volume : Measure ((Fin m → Fin m → ℝ) × (Fin m → Fin p → ℝ))) = volume.prod volume
      from rfl]
    exact hmpΔ.prod (MeasurePreserving.id volume)
  have hmsSet : MeasurableSet {q : (Fin m → Fin m → ℝ) × (Fin m → Fin p → ℝ) |
      0 < frobSq (rmatMul q.1 q.2)} :=
    measurableSet_lt measurable_const (by unfold frobSq rmatMul; fun_prop)
  have hae : ∀ᵐ x ∂(volume.map τ), 0 < frobSq (rmatMul x.1 x.2) := by
    rw [hmp.map_eq]; exact frobSqGP_ne_zero_ae m p hm hp
  have hpull : ∀ᵐ q ∂(volume : Measure ((Fin m → Fin m → ℝ) × (Fin m → Fin p → ℝ))),
      0 < frobSq (rmatMul (τ q).1 (τ q).2) :=
    (ae_map_iff hmp.measurable.aemeasurable hmsSet).1 hae
  refine hpull.mono (fun q hq => ?_)
  have hΔeq : (τ q).1 = (fun i j => q.1 i j - Sh i j) := by
    funext i j; show (q.1 + (fun i j => -Sh i j)) i j = q.1 i j - Sh i j
    simp [Pi.add_apply, sub_eq_add_neg]
  have hSeq : (τ q).2 = q.2 := rfl
  rw [hΔeq, hSeq] at hq
  exact hq

end DLNFibre.DLN.RLCT
