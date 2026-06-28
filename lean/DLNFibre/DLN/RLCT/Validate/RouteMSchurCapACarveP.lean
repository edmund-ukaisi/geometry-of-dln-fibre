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

end DLNFibre.DLN.RLCT
