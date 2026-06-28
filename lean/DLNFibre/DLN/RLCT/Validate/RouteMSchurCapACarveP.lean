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

/-! ## The SHIFTED resolved-form UNIFORM `_le` bound (the JOINT brick, `Fin p` spectator) -/

/-- **The SHIFTED resolved-form UNIFORM `_le` bound at output width `p`** (`Fin p` analog of
`resolvedShiftRG_le`). For a fixed shift `Sh : Fin (r−1) → Fin (r−1) → ℝ` with `|Sh i j| ≤ B`,
`p/2 < c'`, every `K > 0`,
`∫_{Δ}∫_{S}∫_{T∈morseBox p K} (∑_{i:Fin p} T_i² + frobSq((Δ−Sh)·S))^{−c'}` is bounded by
`ofReal(Cresid p c') · coreSchurGenValP (r−1) p (c'−p/2) (K+B)` — INDEPENDENT of `Sh`. The `Fin p` Morse
`T`-peel (`core_T_peel_le_aeG`, `m+1 = p`, threshold `p/2`) on the shifted core (`> 0` a.e. by
`frobSqShiftGP_ne_zero_ae`) leaves the residual at `c'−p/2`, closed by the DONE `schurResidGP_translate_le`. -/
theorem resolvedShiftRGP_le (r p : ℕ) (hr : 3 ≤ r) (hp : 0 < p)
    (Sh : Fin (r - 1) → Fin (r - 1) → ℝ) (B : ℝ) (hB : ∀ i j, |Sh i j| ≤ B)
    (K : ℝ) (hK : 0 < K) (c' : ℝ) (hcp : (p : ℝ) / 2 < c') :
    (∫⁻ Δ in matBox (r - 1) (r - 1) K, ∫⁻ S in matBox (r - 1) p K, ∫⁻ T in morseBox p K,
        ENNReal.ofReal ((∑ i, (T i) ^ 2
          + frobSq (rmatMul (fun a b => Δ a b - Sh a b) S)) ^ (-c')))
      ≤ ENNReal.ofReal (Cresid p c') * coreSchurGenValP (r - 1) p (c' - (p : ℝ) / 2) (K + B) := by
  have hm : 0 < r - 1 := by omega
  -- write `p = pm + 1` so the peel's `morseBox (pm+1)` / `(pm+1)/2` match `morseBox p` / `p/2` literally
  obtain ⟨pm, rfl⟩ : ∃ pm, p = pm + 1 := ⟨p - 1, by omega⟩
  set w : (Fin (r - 1) → Fin (r - 1) → ℝ) × (Fin (r - 1) → Fin (pm + 1) → ℝ) → ℝ :=
    fun q => frobSq (rmatMul (fun a b => q.1 a b - Sh a b) q.2) with hwdef
  have hmeasT : Measurable (fun q : ((Fin (r - 1) → Fin (r - 1) → ℝ) × (Fin (r - 1) → Fin (pm + 1) → ℝ))
      × (Fin (pm + 1) → ℝ) => ENNReal.ofReal ((∑ i, (q.2 i) ^ 2 + w q.1) ^ (-c'))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    show Measurable (fun q : ((Fin (r - 1) → Fin (r - 1) → ℝ) × (Fin (r - 1) → Fin (pm + 1) → ℝ))
        × (Fin (pm + 1) → ℝ) =>
        (∑ i, (q.2 i) ^ 2 + frobSq (rmatMul (fun a b => q.1.1 a b - Sh a b) q.1.2)))
    unfold frobSq rmatMul; fun_prop
  -- Step 1: Tonelli ∫_Δ∫_S∫_T = ∫_{(Δ,S)}∫_T over the product box
  have hstep1 : ∫⁻ Δ in matBox (r - 1) (r - 1) K, ∫⁻ S in matBox (r - 1) (pm + 1) K,
        ∫⁻ T in morseBox (pm + 1) K,
        ENNReal.ofReal ((∑ i, (T i) ^ 2 + frobSq (rmatMul (fun a b => Δ a b - Sh a b) S)) ^ (-c'))
      = ∫⁻ q in (matBox (r - 1) (r - 1) K ×ˢ matBox (r - 1) (pm + 1) K),
          (∫⁻ T in morseBox (pm + 1) K,
          ENNReal.ofReal ((∑ i, (T i) ^ 2 + w q) ^ (-c'))) ∂volume := by
    rw [Measure.volume_eq_prod (Fin (r - 1) → Fin (r - 1) → ℝ) (Fin (r - 1) → Fin (pm + 1) → ℝ),
      setLIntegral_prod _ (Measurable.lintegral_prod_right hmeasT).aemeasurable]
  rw [hstep1]
  -- Step 2: the a.e. T-peel (m = pm): bound by Cresid · ∫_{(Δ,S)} w^{−(c'−(pm+1)/2)}
  have hwpos : ∀ᵐ z ∂(volume.restrict
        (matBox (r - 1) (r - 1) K ×ˢ matBox (r - 1) (pm + 1) K)), 0 < w z :=
    ae_restrict_of_ae (frobSqShiftGP_ne_zero_ae (r - 1) (pm + 1) hm hp Sh)
  have hpeel := core_T_peel_le_aeG (m := pm) (volume) c' (by exact_mod_cast hcp) K hK w
    (matBox (r - 1) (r - 1) K ×ˢ matBox (r - 1) (pm + 1) K) hwpos
  refine le_trans hpeel ?_
  -- Step 3: the residual ∫_{(Δ,S)} w^{−(c'−(pm+1)/2)} = ∫_Δ∫_S frobSq((Δ−Sh)·S)^{−(c'−(pm+1)/2)}
  refine mul_le_mul_left' ?_ _
  have hmeasResid : Measurable
      (fun q : (Fin (r - 1) → Fin (r - 1) → ℝ) × (Fin (r - 1) → Fin (pm + 1) → ℝ) =>
        ENNReal.ofReal ((w q) ^ (-(c' - (pm + 1 : ℝ) / 2)))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-(c' - (pm + 1 : ℝ) / 2))) (by fun_prop)
    show Measurable (fun q : (Fin (r - 1) → Fin (r - 1) → ℝ) × (Fin (r - 1) → Fin (pm + 1) → ℝ) =>
        frobSq (rmatMul (fun a b => q.1 a b - Sh a b) q.2))
    unfold frobSq rmatMul; fun_prop
  have hresid : (∫⁻ q in (matBox (r - 1) (r - 1) K ×ˢ matBox (r - 1) (pm + 1) K),
        ENNReal.ofReal ((w q) ^ (-(c' - (pm + 1 : ℝ) / 2))))
      = ∫⁻ Δ in matBox (r - 1) (r - 1) K, ∫⁻ S in matBox (r - 1) (pm + 1) K,
          ENNReal.ofReal ((frobSq (rmatMul (fun a b => Δ a b - Sh a b) S))
            ^ (-(c' - ((pm : ℝ) + 1) / 2))) := by
    rw [Measure.volume_eq_prod (Fin (r - 1) → Fin (r - 1) → ℝ) (Fin (r - 1) → Fin (pm + 1) → ℝ),
      setLIntegral_prod _ hmeasResid.aemeasurable]
  rw [hresid]
  -- the residual exponent `c' − (pm+1)/2 = c' − p/2`; close by schurResidGP_translate_le
  have hcast : (c' - ((pm : ℝ) + 1) / 2) = (c' - ((pm + 1 : ℕ) : ℝ) / 2) := by push_cast; ring
  rw [hcast]
  exact schurResidGP_translate_le r (pm + 1) hr Sh B hB (c' - ((pm + 1 : ℕ) : ℝ) / 2) K

/-! ## The pivot-normalised form of `innerSGenP` (4 → p of `innerSGen_eq_norm`) -/

/-- **The `S` row-permutation CoV on `matBox r p T`** (`Fin p` analog of `matBox_rowperm_lintegralG`):
permuting the `Fin r` row-index of `S` by `σc` is measure-preserving (`piCongrLeft`) and the box is
`σc`-invariant. -/
theorem matBox_rowperm_lintegralGP {r p : ℕ} (T : ℝ) (σc : Fin r ≃ Fin r)
    (f : (Fin r → Fin p → ℝ) → ℝ≥0∞) :
    (∫⁻ S in matBox r p T, f S) = ∫⁻ S in matBox r p T, f (fun k j => S (σc k) j) := by
  set E := MeasurableEquiv.piCongrLeft (fun _ : Fin r => Fin p → ℝ) σc with hE
  have hmp : MeasurePreserving E.symm volume volume :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin r => Fin p → ℝ) σc).symm E
  have hpre : matBox r p T = E.symm ⁻¹' (matBox r p T) := by
    ext S
    simp only [Set.mem_preimage, matBox, Set.mem_setOf_eq]
    constructor
    · intro h i k; exact h (σc i) k
    · intro h i k
      have := h (σc.symm i) k
      rw [show E.symm S (σc.symm i) k = S i k from by
        show S (σc (σc.symm i)) k = S i k; rw [Equiv.apply_symm_apply]] at this
      exact this
  have key := hmp.setLIntegral_comp_preimage_emb E.symm.measurableEmbedding f (matBox r p T)
  have hrhs : (∫⁻ S in matBox r p T, f (fun k j => S (σc k) j))
      = ∫⁻ S in matBox r p T, f (E.symm S) := rfl
  rw [hrhs]
  rw [← hpre] at key
  exact key.symm

/-- **`innerSGenP` in the pivot-normalised form** (`Fin p` analog of `innerSGen_eq_norm`).
`innerSGenP r p c' T pivot ((piRatioG …).symm (0,z)) = ∫_{S∈matBox r p T} frobSq(RmatGnorm·S)^{−c'}`:
row/col-permute `RmatG` by `σr,σc` (`frobSq_rmatMul_permGP`) under the `S`-row-permute CoV
(`matBox_rowperm_lintegralGP`). -/
theorem innerSGenP_eq_norm (r N p : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r) (c' : ℝ) (T : ℝ)
    (pivot : Fin (r * r)) (z : Fin N → ℝ) :
    innerSGenP r p c' T pivot ((piRatioG r N hN pivot).symm (0, z))
      = ∫⁻ S in matBox r p T,
          ENNReal.ofReal ((frobSq (rmatMul (RmatGnorm r N hN hr pivot z) S)) ^ (-c')) := by
  set y := (piRatioG r N hN pivot).symm (0, z) with hy
  set σr := Equiv.swap ((eG r).symm pivot).1 (⟨0, by omega⟩ : Fin r) with hσr
  set σc := Equiv.swap ((eG r).symm pivot).2 (⟨0, by omega⟩ : Fin r) with hσc
  rw [innerSGenP]
  rw [matBox_rowperm_lintegralGP T σc
    (fun S => ENNReal.ofReal ((frobSq (rmatMul (RmatGnorm r N hN hr pivot z) S)) ^ (-c')))]
  refine lintegral_congr (fun S => ?_)
  congr 2
  exact frobSq_rmatMul_permGP (RmatG r pivot y) S σr σc

/-! ## The per-`(M,v)` carve bound (the heart, `Fin p`; 4 → p of `innerSGenCarve_le`) -/

/-- **The per-`(M,v)` carve bound at output width `p` (the firing heart, `M` FREE).** For the carved
angular matrix `R = RmatGnorm (zEG.symm (M,v))` (pivot `1`, `|entries| ≤ 1` when `M,v ∈ [−1,1]`),
`p/2 < c'`, the inner-`S` integral over `matBox r p T` is bounded by `ofReal(c₀^{−c'})` times the per-`M`
resolved slice (radius `K = max 1 (r·T)`, shift `Sh = bgShiftG v`): N2b (`j = 1`) lower-bounds
`frobSq(R·S)` by `c₀·(frobSq row0 + frobSq(Sc·S_bot))` (`ofReal_rpow_le_const_mul`); the top-row bridge
(`frobSqTopRowP_eq_shearP`) + `stepShearP_r` peel the `Fin p` Morse spectator (box enlarged to `K`); the
carve-`Sc` readback (`ScCarve_eq`) turns `Sc` into `(fun a b => M(a,b) − bgShiftG v a b)`. `M` stays free
so the outer `∫_M` fires in the assembling theorem. The constant `c₀` is the `(p := p)` N2b `.choose`. -/
theorem innerSGenCarveP_le (r N p : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r) (hp : 0 < p) (c' : ℝ)
    (hcp : (p : ℝ) / 2 < c')
    (pivot : Fin (r * r)) (T : ℝ) (hT : 0 < T)
    (M : (Fin (r - 1) × Fin (r - 1)) → ℝ) (v : (Fin (r - 1) ⊕ Fin (r - 1)) → ℝ)
    (hM : M ∈ Set.univ.pi (fun _ : (Fin (r - 1) × Fin (r - 1)) => Set.Icc (-1 : ℝ) 1))
    (hv : v ∈ Set.univ.pi (fun _ : (Fin (r - 1) ⊕ Fin (r - 1)) => Set.Icc (-1 : ℝ) 1)) :
    (∫⁻ S in matBox r p T,
        ENNReal.ofReal ((frobSq (rmatMul (RmatGnorm r N hN hr pivot ((zEG r N hN hr pivot).symm (M, v))) S))
          ^ (-c')))
      ≤ ENNReal.ofReal
          (((schur_minorPivot_split (r := r) (p := p) 1 (by omega)).choose) ^ (-c'))
        * (∫⁻ S_bot in matBox (r - 1) p (max 1 ((r : ℝ) * T)),
            ∫⁻ T' in morseBox p (max 1 ((r : ℝ) * T)),
              ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                + frobSq (rmatMul (fun a b => M (a, b) - bgShiftG (r - 1) v a b) S_bot)) ^ (-c'))) := by
  classical
  have hc0 : 0 < c' := lt_trans (by positivity) hcp
  set z := (zEG r N hN hr pivot).symm (M, v) with hzdef
  set R : Matrix (Fin r) (Fin r) ℝ := Matrix.of (RmatGnorm r N hN hr pivot z) with hRdef
  have hrm1 : (1 : ℕ) ≤ r := by omega
  have hzbox : z ∈ Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1) := by
    intro k _
    rw [hzdef, zEG_symm_apply]
    rcases (zσG r N hN hr pivot k) with s | s
    · exact hM s (Set.mem_univ s)
    · exact hv s (Set.mem_univ s)
  have hpiv : R ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := RmatGnorm_pivot r N hN hr pivot z
  have hbd : ∀ a b, |R a b| ≤ 1 := by
    intro a b
    by_cases hab : a = ⟨0, by omega⟩ ∧ b = ⟨0, by omega⟩
    · rw [hab.1, hab.2, hpiv]; norm_num
    · exact RmatGnorm_offpivot_le r N hN hr pivot z hzbox a b hab
  set c₀ := (schur_minorPivot_split (r := r) (p := p) 1 (by omega)).choose with hc₀def
  obtain ⟨c₁, hc₀, hc₁, hN2b⟩ := (schur_minorPivot_split (r := r) (p := p) 1 hrm1).choose_spec
  set M11 : Matrix (Fin 1) (Fin 1) ℝ :=
    Matrix.of (fun a b : Fin 1 => R ⟨a, lt_of_lt_of_le a.2 hrm1⟩ ⟨b, lt_of_lt_of_le b.2 hrm1⟩) with hM11
  have hM11_one : M11 = 1 := by
    ext a b; fin_cases a; fin_cases b
    simp only [hM11, Matrix.of_apply, Matrix.one_apply_eq]
    exact hpiv
  have hpivdet : M11.det = 1 := by rw [hM11_one]; simp
  have hpivot : ∀ I J : Fin 1 → Fin r, |(R.submatrix I J).det| ≤ |M11.det| := by
    intro I J
    rw [Matrix.det_fin_one, hpivdet, abs_one, Matrix.submatrix_apply]
    exact hbd (I 0) (J 0)
  have hne : M11.det ≠ 0 := by rw [hpivdet]; norm_num
  obtain ⟨Sc, hSceq, _hdet, _, _⟩ := hN2b R (fun _ _ => 0) hbd hpivot hne
  set X : (Fin r → Fin p → ℝ) → ℝ := fun S =>
    frobSq (fun a : Fin 1 => rmatMul (fun x y => R x y) S ⟨a, lt_of_lt_of_le a.2 hrm1⟩)
      + frobSq (rmatMul (fun a b => Sc a b) (fun a : Fin (r - 1) => S ⟨1 + a, by omega⟩)) with hXdef
  have hlow : ∀ S, c₀ * X S ≤ frobSq (rmatMul (fun a b => R a b) S) := by
    intro S
    obtain ⟨Sc', hSceq', _, hlo, _⟩ := hN2b R S hbd hpivot hne
    have hSceq2 : Sc' = Sc := by rw [hSceq', ← hSceq]
    subst hSceq2
    simpa only [hXdef] using hlo
  have hupp : ∀ S, frobSq (rmatMul (fun a b => R a b) S) ≤ c₁ * X S := by
    intro S
    obtain ⟨Sc', hSceq', _, _, hup⟩ := hN2b R S hbd hpivot hne
    have hSceq2 : Sc' = Sc := by rw [hSceq', ← hSceq]
    subst hSceq2
    simpa only [hXdef] using hup
  have hXnn : ∀ S, 0 ≤ X S := fun S => by
    rw [hXdef]; exact add_nonneg (frobSq_nonneg _) (frobSq_nonneg _)
  have hpt : ∀ S, ENNReal.ofReal ((frobSq (rmatMul (fun a b => R a b) S)) ^ (-c'))
      ≤ ENNReal.ofReal (c₀ ^ (-c')) * ENNReal.ofReal ((X S) ^ (-c')) := by
    intro S
    refine ofReal_rpow_le_const_mul (X S) (frobSq (rmatMul (fun a b => R a b) S)) c₀ c'
      hc0 hc₀ (hXnn S) (frobSq_nonneg _) (hlow S) ?_
    intro hX0
    have := hupp S
    rw [hX0, mul_zero] at this
    exact le_antisymm this (frobSq_nonneg _)
  have hM11_one' : (Matrix.of (fun a b : Fin 1 =>
      R ⟨a, lt_of_lt_of_le a.2 hrm1⟩ ⟨b, lt_of_lt_of_le b.2 hrm1⟩)) = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext a b; fin_cases a; fin_cases b
    simp only [Matrix.of_apply, Matrix.one_apply_eq]; exact hpiv
  have hM11inv : ∀ s t : Fin 1,
      (Matrix.of (fun a b : Fin 1 => R ⟨a, lt_of_lt_of_le a.2 hrm1⟩ ⟨b, lt_of_lt_of_le b.2 hrm1⟩))⁻¹ s t
        = if s = t then 1 else 0 := by
    intro s t; rw [hM11_one']; simp [Matrix.one_apply]
  have hSc_carve : (fun a b => Sc a b) = fun a b : Fin (r - 1) => M (a, b) - bgShiftG (r - 1) v a b := by
    funext a b
    rw [hSceq]
    simp only [Matrix.sub_apply, Matrix.of_apply, Matrix.mul_apply, hM11inv]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, if_true,
      mul_one, mul_ite, mul_zero]
    simp only [hRdef, Matrix.of_apply]
    have hcarve := ScCarve_eq r N hN hr pivot M v a b
    have h0idx : (⟨(0 : Fin 1), lt_of_lt_of_le (0 : Fin 1).2 hrm1⟩ : Fin r) = ⟨0, by omega⟩ := rfl
    rw [h0idx] at *
    convert hcarve using 2
  set K := max 1 ((r : ℝ) * T) with hKdef
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  set bcoup : Fin (r - 1) → ℝ := fun a => R ⟨0, by omega⟩ ⟨1 + (a : ℕ), by omega⟩ with hbcoup
  have hbcoup_le : ∀ a, |bcoup a| ≤ 1 := fun a => hbd _ _
  calc (∫⁻ S in matBox r p T,
          ENNReal.ofReal ((frobSq (rmatMul (fun a b => R a b) S)) ^ (-c')))
      ≤ ∫⁻ S in matBox r p T, ENNReal.ofReal (c₀ ^ (-c')) * ENNReal.ofReal ((X S) ^ (-c')) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (c₀ ^ (-c'))
          * ∫⁻ S in matBox r p T, ENNReal.ofReal ((X S) ^ (-c')) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (c₀ ^ (-c'))
          * (∫⁻ S_bot in matBox (r - 1) p K, ∫⁻ T' in morseBox p K,
              ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                + frobSq (rmatMul (fun a b => M (a, b) - bgShiftG (r - 1) v a b) S_bot)) ^ (-c'))) := by
        refine mul_le_mul_left' ?_ _
        have hpiv' : (fun x y => R x y) ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := hpiv
        have hXrw : ∀ S, X S
            = (∑ q, (S ⟨0, by omega⟩ q
                + ∑ a, bcoup a * S ⟨1 + (a : ℕ), by omega⟩ q) ^ 2)
              + frobSq (rmatMul (fun a b => Sc a b) (fun a q => S ⟨1 + (a : ℕ), by omega⟩ q)) := by
          intro S
          simp only [hXdef]
          rw [frobSqTopRowP_eq_shearP r p hr (fun x y => R x y) hpiv' S]
        calc (∫⁻ S in matBox r p T, ENNReal.ofReal ((X S) ^ (-c')))
            = ∫⁻ S in matBox r p T,
                ENNReal.ofReal (((∑ q, (S ⟨0, by omega⟩ q
                    + ∑ a, bcoup a * S ⟨1 + (a : ℕ), by omega⟩ q) ^ 2)
                  + frobSq (rmatMul (fun a b => Sc a b)
                      (fun a q => S ⟨1 + (a : ℕ), by omega⟩ q))) ^ (-c')) := by
              refine lintegral_congr (fun S => ?_); rw [hXrw S]
          _ ≤ ∫⁻ S_bot in matBox (r - 1) p T, ∫⁻ T' in morseBox p ((r : ℕ) * T),
                ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                  + frobSq (rmatMul (fun a b => Sc a b) S_bot)) ^ (-c')) :=
              stepShearP_r r p hr bcoup hbcoup_le (Matrix.of (fun a b => Sc a b)) T hT c'
          _ ≤ ∫⁻ S_bot in matBox (r - 1) p K, ∫⁻ T' in morseBox p K,
                ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                  + frobSq (rmatMul (fun a b => M (a, b) - bgShiftG (r - 1) v a b) S_bot)) ^ (-c')) := by
              have hSsub : matBox (r - 1) p T ⊆ matBox (r - 1) p K := by
                intro Y hY i k; have := Set.mem_Icc.1 (hY i k); rw [Set.mem_Icc]
                have hTK : T ≤ K := le_trans (le_mul_of_one_le_left hT.le
                  (by exact_mod_cast (show (1:ℕ) ≤ r by omega))) (le_max_right _ _)
                constructor <;> [linarith [this.1]; linarith [this.2]]
              have hTsub : morseBox p ((r : ℕ) * T) ⊆ morseBox p K := by
                intro Y hY
                simp only [morseBox, Set.mem_pi, Set.mem_univ, true_implies] at hY ⊢
                intro i
                have hrTK : ((r : ℕ) : ℝ) * T ≤ K := le_max_right _ _
                have := Set.mem_Icc.1 (hY i); rw [Set.mem_Icc]
                constructor <;> [linarith [this.1]; linarith [this.2]]
              refine le_trans (lintegral_mono_set hSsub) ?_
              refine lintegral_mono (fun S_bot => ?_)
              refine le_trans (lintegral_mono_set hTsub) ?_
              refine lintegral_mono (fun T' => ?_)
              rw [show (fun a b => Sc a b) = (fun a b : Fin (r - 1) => M (a, b) - bgShiftG (r - 1) v a b)
                from hSc_carve]

/-! ## The generic ratio-residual (the carve assembly; 4 → p of `schurRatioResidGen_mid`) -/

/-- **The generic ratio-residual at output width `p` (the carve heart, mid case `p/2 < c' < λ_{p,r}`).**
The JOINT integral over the `r²−1` angular ratios `z` (pivot axis set to `0` via `piRatioG`) and `S` is
finite for `p/2 < c' < schurLambdaP p r`, `r ≥ 3`: per `z` the angular `RmatG` has pivot `1`,
`|entries| ≤ 1`; N2b (`j = 1`) peels the top `Fin p` Morse block (threshold `p/2`), leaving the residual
at `c'' = c' − p/2 ∈ (0, schurLambdaP p (r−1))`; the `M22 ↦ Sc` carving + the lower IH `hIH` close it. -/
theorem schurRatioResidGenP_mid (r N p : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r) (hp : 0 < p)
    (hIH : SchurLowerIH p (schurLambdaP p) r) (c' : ℝ) (hcp : (p : ℝ) / 2 < c')
    (hc' : c' < schurLambdaP p r) (pivot : Fin (r * r)) (T : ℝ) (hT : 0 < T) :
    (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
        innerSGenP r p c' T pivot ((piRatioG r N hN pivot).symm (0, z)))
      < ⊤ := by
  classical
  have hc0 : 0 < c' := lt_trans (by positivity) hcp
  set Mbox := Set.univ.pi (fun _ : (Fin (r - 1) × Fin (r - 1)) => Set.Icc (-1 : ℝ) 1) with hMbox
  set vbox := Set.univ.pi (fun _ : (Fin (r - 1) ⊕ Fin (r - 1)) => Set.Icc (-1 : ℝ) 1) with hvbox
  set K := max 1 ((r : ℝ) * T) with hKdef
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  set c₀ := (schur_minorPivot_split (r := r) (p := p) 1 (by omega)).choose with hc₀def
  -- (1) rewrite the integrand to the pivot-normalised form (innerSGenP_eq_norm)
  rw [setLIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
    (fun z _ => innerSGenP_eq_norm r N p hN hr c' T pivot z)]
  -- (2) CoV via zEG : z ↦ (M,v); box preimage [-1,1]^N = zEG ⁻¹' (Mbox ×ˢ vbox)
  set H : ((Fin (r - 1) × Fin (r - 1) → ℝ) × ((Fin (r - 1) ⊕ Fin (r - 1)) → ℝ)) → ℝ≥0∞ := fun q =>
    ∫⁻ S in matBox r p T,
      ENNReal.ofReal ((frobSq (rmatMul (RmatGnorm r N hN hr pivot ((zEG r N hN hr pivot).symm q)) S))
        ^ (-c'))
    with hHdef
  have hHmeas : Measurable H := by
    rw [hHdef]
    apply Measurable.lintegral_prod_right (f := fun q S =>
      ENNReal.ofReal ((frobSq (rmatMul (RmatGnorm r N hN hr pivot ((zEG r N hN hr pivot).symm q)) S))
        ^ (-c')))
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    unfold frobSq rmatMul
    refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
    refine Measurable.pow_const (Finset.measurable_sum _ (fun k _ => ?_)) 2
    refine Measurable.mul ?_ ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp measurable_snd))
    have : Measurable (fun q : (Fin (r - 1) × Fin (r - 1) → ℝ) × ((Fin (r - 1) ⊕ Fin (r - 1)) → ℝ) =>
        RmatGnorm r N hN hr pivot ((zEG r N hN hr pivot).symm q) i k) := by
      unfold RmatGnorm
      have hz : Measurable (fun q : (Fin (r - 1) × Fin (r - 1) → ℝ) × ((Fin (r - 1) ⊕ Fin (r - 1)) → ℝ) =>
          (zEG r N hN hr pivot).symm q) := (zEG r N hN hr pivot).symm.measurable
      have hsel : Measurable (fun y : Fin N → ℝ => RmatG r pivot ((piRatioG r N hN pivot).symm (0, y))
          ((Equiv.swap ((eG r).symm pivot).1 ⟨0, by omega⟩) i)
          ((Equiv.swap ((eG r).symm pivot).2 ⟨0, by omega⟩) k)) := by
        simp only [RmatG_entry]
        by_cases h : eG r ((Equiv.swap ((eG r).symm pivot).1 ⟨0, by omega⟩) i,
            (Equiv.swap ((eG r).symm pivot).2 ⟨0, by omega⟩) k) = pivot
        · simp only [if_pos h]; exact measurable_const
        · simp only [if_neg h]
          exact (measurable_pi_apply _).comp
            (by fun_prop : Measurable (fun y : Fin N → ℝ => (piRatioG r N hN pivot).symm (0, y)))
      exact hsel.comp hz
    exact this.comp measurable_fst
  have hpre : (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))
      = (zEG r N hN hr pivot) ⁻¹' (Mbox ×ˢ vbox) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, hMbox, hvbox, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h
      refine ⟨fun ik => ?_, fun s => ?_⟩
      · rw [zEG_fst_apply]; exact h _
      · rw [zEG_snd_apply]; exact h _
    · rintro ⟨h1, h2⟩ i
      obtain ⟨s, hs⟩ := (zσG r N hN hr pivot).symm.surjective i
      rcases s with ik | s
      · have := h1 ik; rw [zEG_fst_apply, hs] at this; exact this
      · have := h2 s; rw [zEG_snd_apply, hs] at this; exact this
  rw [hpre]
  have hintegrand : (∫⁻ x in (zEG r N hN hr pivot) ⁻¹' (Mbox ×ˢ vbox),
      ∫⁻ S in matBox r p T,
        ENNReal.ofReal ((frobSq (rmatMul (RmatGnorm r N hN hr pivot x) S)) ^ (-c')))
      = ∫⁻ x in (zEG r N hN hr pivot) ⁻¹' (Mbox ×ˢ vbox), H (zEG r N hN hr pivot x) := by
    refine lintegral_congr (fun x => ?_)
    rw [hHdef]; simp only [MeasurableEquiv.symm_apply_apply]
  rw [hintegrand]
  -- (3) CoV via zEG (MP), Tonelli to v outer
  rw [(measurePreserving_zEG r N hN hr pivot).setLIntegral_comp_preimage_emb
    (zEG r N hN hr pivot).measurableEmbedding H (Mbox ×ˢ vbox)]
  have hMboxms : MeasurableSet Mbox := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hvboxms : MeasurableSet vbox := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  rw [Measure.volume_eq_prod, setLIntegral_prod _ hHmeas.aemeasurable,
    lintegral_lintegral_swap hHmeas.aemeasurable]
  set curryME : (Fin (r - 1) → Fin (r - 1) → ℝ) ≃ᵐ (Fin (r - 1) × Fin (r - 1) → ℝ) :=
    (MeasurableEquiv.piCurry (fun (_ : Fin (r - 1)) (_ : Fin (r - 1)) => ℝ)).symm.trans
      (MeasurableEquiv.arrowCongr' (Equiv.sigmaEquivProd (Fin (r - 1)) (Fin (r - 1)))
        (MeasurableEquiv.refl ℝ)) with hcurryME
  have hcurryMP : MeasurePreserving curryME (volume : Measure (Fin (r - 1) → Fin (r - 1) → ℝ))
      (volume : Measure (Fin (r - 1) × Fin (r - 1) → ℝ)) := by
    rw [hcurryME]
    refine MeasurePreserving.trans ?_ (volume_preserving_arrowCongr'
      (Equiv.sigmaEquivProd (Fin (r - 1)) (Fin (r - 1))) (MeasurableEquiv.refl ℝ)
      (MeasurePreserving.id _))
    exact (measurePreserving_piCurry (fun (_ : Fin (r - 1)) (_ : Fin (r - 1)) => ℝ)
      (fun _ _ => (volume : Measure ℝ))).symm
      (MeasurableEquiv.piCurry (fun (_ : Fin (r - 1)) (_ : Fin (r - 1)) => ℝ))
  have hperv : ∀ v ∈ vbox, (∫⁻ M in Mbox, H (M, v))
      ≤ ENNReal.ofReal (c₀ ^ (-c'))
        * (ENNReal.ofReal (Cresid p c') * coreSchurGenValP (r - 1) p (c' - (p : ℝ) / 2) (K + 1)) := by
    intro v hv
    have hMcarve : ∀ M ∈ Mbox, H (M, v)
        ≤ ENNReal.ofReal (c₀ ^ (-c'))
          * (∫⁻ S_bot in matBox (r - 1) p K, ∫⁻ T' in morseBox p K,
              ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                + frobSq (rmatMul (fun a b => M (a, b) - bgShiftG (r - 1) v a b) S_bot)) ^ (-c'))) := by
      intro M hM
      rw [hHdef]
      exact innerSGenCarveP_le r N p hN hr hp c' hcp pivot T hT M v hM hv
    calc (∫⁻ M in Mbox, H (M, v))
        ≤ ∫⁻ M in Mbox, ENNReal.ofReal (c₀ ^ (-c'))
            * (∫⁻ S_bot in matBox (r - 1) p K, ∫⁻ T' in morseBox p K,
                ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                  + frobSq (rmatMul (fun a b => M (a, b) - bgShiftG (r - 1) v a b) S_bot)) ^ (-c'))) :=
          setLIntegral_mono_ae' hMboxms (ae_of_all _ (fun M hM => hMcarve M hM))
      _ = ENNReal.ofReal (c₀ ^ (-c'))
            * ∫⁻ M in Mbox, (∫⁻ S_bot in matBox (r - 1) p K, ∫⁻ T' in morseBox p K,
                ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                  + frobSq (rmatMul (fun a b => M (a, b) - bgShiftG (r - 1) v a b) S_bot)) ^ (-c'))) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (c₀ ^ (-c'))
            * (ENNReal.ofReal (Cresid p c') * coreSchurGenValP (r - 1) p (c' - (p : ℝ) / 2) (K + 1)) := by
          refine mul_le_mul_left' ?_ _
          have hvabs : ∀ s, |v s| ≤ 1 := by
            intro s; have := Set.mem_Icc.1 (hv s (Set.mem_univ s)); rw [abs_le]; exact this
          have hSh : ∀ i j, |bgShiftG (r - 1) v i j| ≤ (1 : ℝ) := fun i j =>
            bgShiftG_entry_le (r - 1) v hvabs i j
          set G : (Fin (r - 1) × Fin (r - 1) → ℝ) → ℝ≥0∞ := fun M =>
            ∫⁻ S_bot in matBox (r - 1) p K, ∫⁻ T' in morseBox p K,
              ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                + frobSq (rmatMul (fun a b => M (a, b) - bgShiftG (r - 1) v a b) S_bot)) ^ (-c'))
            with hGdef
          have hcov := hcurryMP.setLIntegral_comp_preimage_emb curryME.measurableEmbedding G Mbox
          have hpresub : curryME ⁻¹' Mbox ⊆ matBox (r - 1) (r - 1) K := by
            intro Δ hΔ i k
            have h1K : (1 : ℝ) ≤ K := le_max_left _ _
            have hmem : curryME Δ ∈ Mbox := hΔ
            have : curryME Δ (i, k) ∈ Set.Icc (-1 : ℝ) 1 := hmem (i, k) (Set.mem_univ _)
            have hΔik : Δ i k ∈ Set.Icc (-1 : ℝ) 1 := by
              rw [hcurryME] at this; exact this
            have := Set.mem_Icc.1 hΔik
            rw [Set.mem_Icc]; constructor <;> [linarith [this.1]; linarith [this.2]]
          have hcurryapp : ∀ (Δ : Fin (r - 1) → Fin (r - 1) → ℝ) (a b : Fin (r - 1)),
              curryME Δ (a, b) = Δ a b := fun Δ a b => rfl
          have hGcurry : ∀ Δ : Fin (r - 1) → Fin (r - 1) → ℝ, G (curryME Δ)
              = ∫⁻ S_bot in matBox (r - 1) p K, ∫⁻ T' in morseBox p K,
                  ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                    + frobSq (rmatMul (fun a b => Δ a b - bgShiftG (r - 1) v a b) S_bot)) ^ (-c')) := by
            intro Δ; rw [hGdef]; simp only [hcurryapp]
          calc (∫⁻ M in Mbox, G M)
              = ∫⁻ Δ in curryME ⁻¹' Mbox, G (curryME Δ) := hcov.symm
            _ = ∫⁻ Δ in curryME ⁻¹' Mbox, ∫⁻ S_bot in matBox (r - 1) p K, ∫⁻ T' in morseBox p K,
                  ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                    + frobSq (rmatMul (fun a b => Δ a b - bgShiftG (r - 1) v a b) S_bot)) ^ (-c')) :=
                lintegral_congr (fun Δ => hGcurry Δ)
            _ ≤ ∫⁻ Δ in matBox (r - 1) (r - 1) K, ∫⁻ S_bot in matBox (r - 1) p K, ∫⁻ T' in morseBox p K,
                  ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                    + frobSq (rmatMul (fun a b => Δ a b - bgShiftG (r - 1) v a b) S_bot)) ^ (-c')) :=
                lintegral_mono_set hpresub
            _ ≤ ENNReal.ofReal (Cresid p c') * coreSchurGenValP (r - 1) p (c' - (p : ℝ) / 2) (K + 1) :=
                resolvedShiftRGP_le r p hr hp (bgShiftG (r - 1) v) 1 hSh K hKpos c' hcp
  calc (∫⁻ v in vbox, ∫⁻ M in Mbox, H (M, v))
      ≤ ∫⁻ _v in vbox, ENNReal.ofReal (c₀ ^ (-c'))
          * (ENNReal.ofReal (Cresid p c') * coreSchurGenValP (r - 1) p (c' - (p : ℝ) / 2) (K + 1)) :=
        setLIntegral_mono_ae' hvboxms (ae_of_all _ (fun v hv => hperv v hv))
    _ = (ENNReal.ofReal (c₀ ^ (-c'))
          * (ENNReal.ofReal (Cresid p c')
            * coreSchurGenValP (r - 1) p (c' - (p : ℝ) / 2) (K + 1))) * volume vbox := by
        rw [setLIntegral_const]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)) ?_
        · -- coreSchurGenValP < ⊤ via the abstract IH (c' − p/2 < schurLambdaP p (r−1))
          refine coreSchurGenValP_lt_top r p hr hIH (c' - (p : ℝ) / 2) (by linarith) ?_ (K + 1)
            (by linarith)
          -- c' − p/2 < schurLambdaP p (r−1) via the peel j = 1
          have hpeel := schurLambdaP_peel_le p (r := r) (j := 1) (le_refl 1) (by omega)
          simp only [Nat.cast_one, one_mul] at hpeel
          linarith
        · rw [hvbox]
          exact (isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top

/-- **The generic ratio-residual, all `0 < c' < λ_{p,r}` (subcritical fold).** Mid case `p/2 < c'` is
`schurRatioResidGenP_mid`; subcritical `c' ≤ p/2` dominates `F^{−c'} ≤ 1 + F^{−c''}` and reduces to the
`c'' = ½(p/2 + λ_{p,r})` mid case (`c'' ∈ (p/2, λ_{p,r})` since the interior stratum has `λ_{p,r} > p/2`). -/
theorem schurRatioResidGenP (r N p : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r) (hp : 0 < p)
    (hIH : SchurLowerIH p (schurLambdaP p) r) (c' : ℝ) (hc0 : 0 < c') (hc' : c' < schurLambdaP p r)
    (hmid : (p : ℝ) / 2 < schurLambdaP p r) (pivot : Fin (r * r)) (T : ℝ) (hT : 0 < T) :
    (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
        innerSGenP r p c' T pivot ((piRatioG r N hN pivot).symm (0, z)))
      < ⊤ := by
  -- the midpoint `c'' = ½(p/2 + λ_{p,r}) ∈ (p/2, λ_{p,r})`
  set c'' : ℝ := ((p : ℝ) / 2 + schurLambdaP p r) / 2 with hc''def
  have hc''lo : (p : ℝ) / 2 < c'' := by rw [hc''def]; linarith
  have hc''hi : c'' < schurLambdaP p r := by rw [hc''def]; linarith
  rcases lt_or_ge ((p : ℝ) / 2) c' with hc2 | hc2
  · exact schurRatioResidGenP_mid r N p hN hr hp hIH c' hc2 hc' pivot T hT
  · -- c' ≤ p/2: dominate the inner integrand by `1 + (·)^{−c''}`, reduce to the c'' mid case
    set q : (Fin N → ℝ) → (Fin (r * r) → ℝ) := fun z => (piRatioG r N hN pivot).symm (0, z) with hq
    have hdom : ∀ z : Fin N → ℝ,
        innerSGenP r p c' T pivot (q z)
          ≤ volume (matBox r p T) + innerSGenP r p c'' T pivot (q z) := by
      intro z
      rw [innerSGenP, innerSGenP]
      calc (∫⁻ S in matBox r p T,
              ENNReal.ofReal ((frobSq (rmatMul (RmatG r pivot (q z)) S)) ^ (-c')))
          ≤ ∫⁻ S in matBox r p T,
              (1 + ENNReal.ofReal ((frobSq (rmatMul (RmatG r pivot (q z)) S)) ^ (-c''))) :=
            lintegral_mono (fun S =>
              ofReal_rpow_neg_le_one_addG _ (frobSq_nonneg _) c' c'' hc0 (by linarith))
        _ = volume (matBox r p T) + ∫⁻ S in matBox r p T,
              ENNReal.ofReal ((frobSq (rmatMul (RmatG r pivot (q z)) S)) ^ (-c'')) := by
            rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul]
    refine lt_of_le_of_lt (lintegral_mono hdom) ?_
    rw [lintegral_add_left measurable_const, setLIntegral_const]
    refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
    · exact ENNReal.mul_lt_top (matBox_volume_lt_top r p T)
        (by rw [show (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)) = morseBox N 1 from by
          rw [morseBox]]; exact morseBox_volume_lt_top N 1)
    · exact schurRatioResidGenP_mid r N p hN hr hp hIH c'' hc''lo hc''hi pivot T hT

/-! ## The cap-A per-chart finiteness (mirror of DirectMorseP's `schur_matBoxGenP_chart_lt_top`) -/

/-- **The cap-A per-chart finiteness.** The output-width-`p` per-chart integral is finite for
`0 < c' < schurLambdaP p r` (`r ≥ 3`, interior stratum `schurLambdaP p r > p/2`): same radial-axis ×
angular-residual factorisation as DirectMorseP's `schur_matBoxGenP_chart_lt_top`, with the angular
residual supplied by the cap-A carve `schurRatioResidGenP` (vs. cap-B `schurRatioResidP_capB_lt_top`). The
radial cap `c' < r²/2` holds via `schurLambdaP_le_sq`. -/
theorem schur_matBoxGenP_chart_capA_lt_top (r p : ℕ) (hr : 3 ≤ r) (hp : 0 < p)
    (hIH : SchurLowerIH p (schurLambdaP p) r) (c' : ℝ) (hc0 : 0 < c') (hc' : c' < schurLambdaP p r)
    (hmid : (p : ℝ) / 2 < schurLambdaP p r) (pivot : Fin (r * r)) (T : ℝ) (hT : 0 < T) :
    ∫⁻ y in chartDomOn (Finset.univ : Finset (Fin (r * r))) pivot \ pivotZeroOn pivot,
        ENNReal.ofReal |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin (r * r))) pivot y).det|
          * (flatBoxGen r T).indicator (gFlatGen r p c' T) (pivotBlowupOn
              (Finset.univ : Finset (Fin (r * r))) pivot y)
      < ⊤ := by
  have hrr : 0 < r * r := by positivity
  obtain ⟨N, hN⟩ : ∃ N, r * r = N + 1 := ⟨r * r - 1, by omega⟩
  have hcr : c' < (r ^ 2 : ℝ) / 2 := lt_of_lt_of_le hc' (schurLambdaP_le_sq p r)
  have hdet : ∀ y : Fin (r * r) → ℝ,
      |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin (r * r))) pivot y).det|
        = |y pivot| ^ (r * r - 1) := by
    intro y
    rw [pivotBlowupOnDeriv_det (Finset.univ : Finset (Fin (r * r))) pivot (Finset.mem_univ pivot) y,
      Finset.card_univ, Fintype.card_fin]
    simp [abs_pow]
  simp only [hdet]
  have hmsD : MeasurableSet
      (chartDomOn (Finset.univ : Finset (Fin (r * r))) pivot \ pivotZeroOn pivot) := by
    refine MeasurableSet.diff ?_ ?_
    · have heq : chartDomOn (Finset.univ : Finset (Fin (r * r))) pivot
          = ⋂ k ∈ (Finset.univ.erase pivot), {y : Fin (r * r) → ℝ | |y k| ≤ 1} := by
        ext y
        simp only [chartDomOn, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_erase,
          Finset.mem_univ, and_true, true_implies]
      rw [heq]
      refine Finset.measurableSet_biInter (Finset.univ.erase pivot) (fun k _ => ?_)
      exact measurableSet_le ((measurable_pi_apply k).abs) measurable_const
    · exact (measurable_pi_apply pivot (measurableSet_singleton 0))
  rw [setLIntegral_congr_fun hmsD
    (fun y hy => chart_integrand_factorGen r p c' hc0 T hT pivot y hy.2 hy.1)]
  set e := piRatioG r N hN pivot with he
  have hmp : MeasurePreserving e (volume) (volume) := measurePreserving_piRatioG r N hN pivot
  have hpre : (chartDomOn (Finset.univ : Finset (Fin (r * r))) pivot \ pivotZeroOn pivot)
      = e ⁻¹' (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))) := by
    ext y
    simp only [chartDomOn, pivotZeroOn, Set.mem_diff, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, he]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [piRatioG_apply_fst]; exact h2, fun j => ?_⟩
      rw [Set.mem_Icc, ← abs_le, piRatioG_apply_snd]
      exact h1 _ (Finset.mem_univ _) (piRatioG_ratioIdx_ne r N hN pivot j)
    · rintro ⟨h1, h2⟩
      rw [piRatioG_apply_fst] at h1
      refine ⟨fun k _ hk => ?_, h1⟩
      have hne : finCongr hN k ≠ finCongr hN pivot := fun h => hk ((finCongr hN).injective h)
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
      have hk_eq : k = (finCongr hN).symm ((finCongr hN pivot).succAbove j) := by
        rw [hj]; exact ((finCongr hN).symm_apply_apply k).symm
      have hj2 := h2 j
      rw [Set.mem_Icc, ← abs_le, piRatioG_apply_snd r N hN pivot y j] at hj2
      rw [hk_eq]; exact hj2
  set g : (Fin (r * r) → ℝ) → ℝ≥0∞ := fun y =>
    (Set.Icc (-T) T).indicator
        (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) (y pivot)
      * innerSGenP r p c' T pivot y with hgdef
  have hgmeas : Measurable g := by
    rw [hgdef]
    refine Measurable.mul ?_ (measurable_innerSGenP r p c' T pivot)
    have hind : Measurable (fun a : ℝ =>
        (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a) := by
      refine Measurable.indicator ?_ measurableSet_Icc
      exact ENNReal.measurable_ofReal.comp ((measurable_id.abs).pow_const _)
    exact hind.comp (measurable_pi_apply pivot)
  rw [hpre]
  have hSms : MeasurableSet
      (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))) :=
    MeasurableSet.prod (by measurability) (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
  have key := hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding (fun q => g (e.symm q))
    (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)))
  have htrans : (∫⁻ y in e ⁻¹' (({a : ℝ | a ≠ 0}) ×ˢ
        (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))), g y)
      = ∫⁻ q in (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))),
          g (e.symm q) := by
    rw [← key]
    refine setLIntegral_congr_fun (e.measurable hSms) (fun y _ => ?_)
    rw [MeasurableEquiv.symm_apply_apply]
  rw [htrans]
  have hgsymm_meas : Measurable (fun q : ℝ × (Fin N → ℝ) => g (e.symm q)) :=
    hgmeas.comp e.symm.measurable
  rw [Measure.volume_eq_prod ℝ (Fin N → ℝ), setLIntegral_prod _ hgsymm_meas.aemeasurable]
  have hfactor : ∀ a : ℝ, ∀ z : Fin N → ℝ,
      g (e.symm (a, z))
        = (Set.Icc (-T) T).indicator
            (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a
          * innerSGenP r p c' T pivot (e.symm (0, z)) := by
    intro a z
    have hp_eq : (e.symm (a, z)) pivot = a := by rw [he]; exact piRatioG_symm_pivot r N hN pivot a z
    have hoff : innerSGenP r p c' T pivot (e.symm (a, z))
        = innerSGenP r p c' T pivot (e.symm (0, z)) := by
      refine innerSGenP_offpivot r p c' T pivot _ _ (fun i hi => ?_)
      rw [he]; exact piRatioG_symm_offpivot r N hN pivot a 0 z i hi
    show (Set.Icc (-T) T).indicator
        (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) ((e.symm (a, z)) pivot)
        * innerSGenP r p c' T pivot (e.symm (a, z)) = _
    rw [hp_eq, hoff]
  have hN3a : (∫⁻ a in Set.Icc (-T) T,
      ENNReal.ofReal (|a| ^ ((r ^ 2 : ℝ) - 1 - 2 * c'))) < ⊤ :=
    radial_aAxis_divisor_lt_top r (by omega) T hT c' hcr
  have hexp : ((r ^ 2 : ℝ) - 1 - 2 * c') = (((r * r - 1 : ℕ) : ℝ) - 2 * c') := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]; push_cast [pow_two]; ring
  rw [hexp] at hN3a
  have hradfin : (∫⁻ a in {a : ℝ | a ≠ 0},
        (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a) < ⊤ := by
    have hle1 : (∫⁻ a in {a : ℝ | a ≠ 0},
          (Set.Icc (-T) T).indicator
            (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a)
        ≤ ∫⁻ a, (Set.Icc (-T) T).indicator
            (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a := by
      have := lintegral_mono_set (μ := volume) (s := {a : ℝ | a ≠ 0}) (t := Set.univ)
        (Set.subset_univ _)
        (f := (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))))
      rwa [setLIntegral_univ] at this
    have heq2 : (∫⁻ a, (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a)
        = ∫⁻ a in Set.Icc (-T) T, ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c')) :=
      lintegral_indicator measurableSet_Icc _
    rw [heq2] at hle1
    exact lt_of_le_of_lt hle1 hN3a
  have hratiofin : (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
        innerSGenP r p c' T pivot (e.symm (0, z))) < ⊤ :=
    schurRatioResidGenP r N p hN hr hp hIH c' hc0 hc' hmid pivot T hT
  have hinner : ∀ a : ℝ,
      (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)), g (e.symm (a, z)))
        = (Set.Icc (-T) T).indicator
            (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a
          * ∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
              innerSGenP r p c' T pivot (e.symm (0, z)) := by
    intro a
    have hradne : (Set.Icc (-T) T).indicator
        (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a ≠ ⊤ := by
      rw [Set.indicator_apply]; split <;> simp [ENNReal.ofReal_ne_top]
    rw [lintegral_congr (fun z => hfactor a z), lintegral_const_mul' _ _ hradne]
  rw [lintegral_congr hinner, lintegral_mul_const' _ _ hratiofin.ne]
  exact ENNReal.mul_lt_top hradfin hratiofin

end DLNFibre.DLN.RLCT
