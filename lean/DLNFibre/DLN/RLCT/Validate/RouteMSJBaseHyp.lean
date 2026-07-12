import DLNFibre.DLN.RLCT.Validate.RouteMSJAdm
import DLNFibre.DLN.RLCT.Validate.RouteMSJBaseFinite
import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedRec
import DLNFibre.DLN.RLCT.Validate.RouteMSJLeafFinite
import DLNFibre.DLN.RLCT.Validate.RouteMSJMonomialLower
import DLNFibre.DLN.RLCT.Validate.MonomialThresholdIdentity

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJBaseHyp` — the `DecoratedBaseHyp` base cases (#4)

**Thread `genm-sj5-desc4`, `DecoratedBaseHyp` (#4) — COMPLETE.** `decoratedBaseHyp_faithful`
proves `DecoratedBaseHyp adm` (sorry-free, axiom-clean), against the strengthened
`RouteMSJAdm.FaithfulSJAt` (S2-settled, `faithfulsj-design §★★★`). At a width-2 chain the `adm`
disjunction `admCorankA M = 0 ∨ admCorankB M = 0 ∨ FaithfulSJAt D` dispatches to three closers:

* **(i) `decoratedBase_corankZero`** — the degenerate binding cut. At width 2 `bindingCut M = 0`
  (`bindingCut_two`), so `admCorankA M = M 0`, `admCorankB M = M 1`; either being `0` forces
  `minAdm M = M 0 · M 1 = 0` (`minAdm_two_eq`), hence `carrierThreshold M = 0` — no exponent
  `c' ≥ 0` lies strictly below it, so finiteness holds VACUOUSLY.

* **(ii) `decoratedBase_d0_of_lossEq`** — the `d = 0` free-block leaf. `FaithfulSJAt`'s `d = 0`
  disjunct is the HEq-free OBSERVABLE form (`carrier.loss = ∑_v (x v)²`); with `genuineCarrier`'s
  `ctx = prod` clause the assembly derives `decLoss = frobSq (prod M (e z))` (the `hν`-transport
  cancelled by `eqRec_fun_apply_eqRec`), the `d = 0` integral collapses (empty exceptional monomial,
  unit box measure `1`), and the banked width-2 CoV `baseBoxCoV_lt_top` closes it.

* **(iii) `decoratedBase_routeA_of_leafForm`** — the `d ≥ 1` resolved corner. `FaithfulSJAt`'s clean
  route-A leaf-form bundle (`decLoss = commonDivisor(u)² · frobSq (Γ·Z)`, `Z·Zᵀ ≽ c·1`,
  `minAdm M ≤ a·n`) Tonelli-separates into a `u`-monomial box integral times a `Γ`-block integral,
  the first finite below `monomialThreshold` (β), the second the banked `corankLeaf_rpow_lt_top`;
  MIN-of-two-full-budgets, both `≥ ½·minAdm M`. Supporting bricks: `decLoss_commonDivisor_factor`
  (the DERIVED weighted-`δ` u-part), `decLoss_clean_of_uniformResidualSupport` (S2=yes collapse),
  `WeightedLeafForm` (the alternative weighted-provenance clause, staged).

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators Matrix

/-! ## Width-2 arithmetic (case (i) support) -/

/-- **The binding cut of a width-2 chain is `0`** — a two-node chain carries no corank peel
(`bindingCut`'s `n = 1` arm). -/
theorem bindingCut_two (M : Fin (1 + 1) → ℕ) : bindingCut M = 0 := rfl

/-- **A degenerate binding-cut corank forces `minAdm M = 0`.** At width 2 `admCorankA M = M 0` and
`admCorankB M = M 1` (since `bindingCut M = 0`), so either being `0` sends `minAdm M = M 0 · M 1`
(`minAdm_two_eq`) to `0`. -/
theorem minAdm_eq_zero_of_corankZero (M : Fin (1 + 1) → ℕ)
    (h : admCorankA M = 0 ∨ admCorankB M = 0) : minAdm M = 0 := by
  rw [minAdm_two_eq]
  rcases h with h | h
  · have hM0 : M 0 = 0 := by
      have := h; unfold admCorankA at this; rw [bindingCut_two] at this; simpa using this
    simp [hM0]
  · have hM1 : M 1 = 0 := by
      have := h; unfold admCorankB at this; rw [bindingCut_two] at this; simpa using this
    simp [hM1]

/-! ## Case (i) — the vacuous degenerate-corank base -/

/-- **`DecoratedBaseHyp` case (i): the degenerate binding cut.** If either binding-cut corank is `0`
then `carrierThreshold M = ½·minAdm M = 0`, so no exponent `c' : NNReal` lies strictly below it and
finiteness holds vacuously. Design-independent (no `FaithfulSJAt` shape). -/
theorem decoratedBase_corankZero {M : Fin (1 + 1) → ℕ} (D : SJDecoration M)
    (h : admCorankA M = 0 ∨ admCorankB M = 0) : DecoratedBoxThresholdFinite D := by
  intro c' hc'
  exfalso
  rw [carrierThreshold, minAdm_eq_zero_of_corankZero M h] at hc'
  simp only [Nat.cast_zero, zero_div] at hc'
  exact absurd hc' (not_lt.mpr c'.coe_nonneg)

/-! ## Case (ii) — the `d = 0` free-block leaf, modulo the loss identity -/

/-- **`DecoratedBaseHyp` case (ii): the `d = 0` free-block leaf (analytic core).** Given a
measure-preserving deeper parametrization `e : D.Z ≃ᵐ Params M` with `dom = e ⁻¹' (paramsBoxM M 1)`
and the loss identity `decLoss u z = frobSq (prod M (e z))` (the `d = 0` carrier IS the product
loss), the decorated integral collapses to the banked width-2 free-matrix change of variables
`baseBoxCoV_lt_top`: with `D.d = 0` the exceptional monomial `∏_ℓ |u_ℓ|^{jac_ℓ}` is the empty
product `1` and the unit box has full measure `1`, so
`D.integral c' = ∫_{e⁻¹ box} frobSq (prod M (e z))^{−c'}`, finite below `carrierThreshold M`. The
`hloss` hypothesis is what a (re-stated, extractable) `FaithfulSJAt` `d = 0` disjunct supplies. -/
theorem decoratedBase_d0_of_lossEq {M : Fin (1 + 1) → ℕ} (D : SJDecoration M)
    (e : letI := D.mZ; D.Z ≃ᵐ Params M) (hmp : letI := D.mZ; MeasurePreserving e)
    (hdom : letI := D.mZ; D.dom = e ⁻¹' paramsBoxM M 1) (hd0 : D.d = 0)
    (hloss : letI := D.mZ; ∀ (u : Fin D.d → ℝ) (z : D.Z),
      D.decLoss u z = frobSq (prod M (e z))) :
    DecoratedBoxThresholdFinite D := by
  letI := D.mZ
  intro c' hc'
  haveI hEmpty : IsEmpty (Fin D.d) := by rw [hd0]; infer_instance
  have hprod : ∀ u : Fin D.d → ℝ, (∏ ℓ, |u ℓ| ^ (D.jac ℓ)) = 1 := by
    intro u; rw [Finset.univ_eq_empty, Finset.prod_empty]
  have hvol : (volume : Measure (Fin D.d → ℝ)) (unitBox D.d) = 1 := by
    rw [unitBox, volume_pi_pi]; simp
  have hdommeas : MeasurableSet D.dom := by
    rw [hdom]; exact (measurableSet_paramsBoxM M 1).preimage e.measurable
  have hkey : D.integral (c' : ℝ)
      = ∫⁻ z in D.dom, ENNReal.ofReal ((frobSq (prod M (e z))) ^ (-(c' : ℝ))) := by
    unfold SJDecoration.integral
    refine setLIntegral_congr_fun hdommeas (fun z _ => ?_)
    have hpt : ∀ u : Fin D.d → ℝ,
        ENNReal.ofReal ((∏ ℓ, |u ℓ| ^ D.jac ℓ) * D.decLoss u z ^ (-(c' : ℝ)))
          = ENNReal.ofReal ((frobSq (prod M (e z))) ^ (-(c' : ℝ))) :=
      fun u => by rw [hprod u, one_mul, hloss u z]
    rw [lintegral_congr hpt, setLIntegral_const, hvol, mul_one]
  rw [hkey, hdom]
  exact baseBoxCoV_lt_top e hmp c' hc'

/-! ## Case (iii) — the `d ≥ 1` resolved corner, route-A analytic core (modulo the leaf form) -/

/-- **`DecoratedBaseHyp` case (iii): the `d ≥ 1` resolved corner (route-A analytic core).** Given
the route-A LEAF FORM as explicit structural hypotheses — a free-block measure iso
`eΓ : D.Z ≃ᵐ (Fin a → Fin n → ℝ)` with `dom = eΓ ⁻¹' matBox a n 1`, a fixed deeper tail
`Z : Matrix (Fin n) (Fin Dt) ℝ` with the units bound `Z·Zᵀ ≽ cpos·1` (`cpos > 0`), the free-block
dimension bound `minAdm M ≤ a · n` (dim Γ dominates `minAdm`; equality at the width-2 leaf, but only
`≤` is needed — and only `≤` is width-general), the threshold clause β
`½·minAdm M ≤ monomialThreshold D.d (sharedDivisorExp supp) jac`, and the block loss decomposition
`decLoss u z = commonDivisor(u)² · frobSq (Γ(z) · Z)` — the decorated integral separates (Tonelli)
into `(∫_unitBox monomialIntegrand) · (∫_matBox frobSq (Γ·Z)^{−c'})`. The first factor is finite
below `monomialThreshold` (β, via the banked monomial-box brick); the second is the banked route-A
leaf `corankLeaf_rpow_lt_top` after the measure-preserving change of variables, finite below
`(a·n)/2 ≥ ½·minAdm M`. Threshold is `min` of the two budgets, both `≥ ½·minAdm M` — NOT a sum.
The five hypotheses are exactly the route-A leaf form a `FaithfulSJAt` `d ≥ 1` branch must carry
(handoff item 2); the analytic composition is proved here, sorry-free. -/
theorem decoratedBase_routeA_of_leafForm {M : Fin (1 + 1) → ℕ} (D : SJDecoration M) (i₀ : D.ι)
    (a n Dt : ℕ) (Z : Matrix (Fin n) (Fin Dt) ℝ) (cpos : ℝ) (hcpos : 0 < cpos)
    (hZ : (Z * Zᵀ - cpos • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (eΓ : letI := D.mZ; D.Z ≃ᵐ (Fin a → Fin n → ℝ))
    (hmp : letI := D.mZ; MeasurePreserving eΓ)
    (hdom : letI := D.mZ; D.dom = eΓ ⁻¹' matBox a n 1) (hdim : minAdm M ≤ a * n)
    (hbeta : letI := D.fι; letI : Nonempty D.ι := ⟨i₀⟩;
      (minAdm M : ℝ≥0∞) / 2 ≤ monomialThreshold D.d (sharedDivisorExp D.carrier.supp) D.jac)
    (hdec : letI := D.mZ; letI := D.fι; letI : Nonempty D.ι := ⟨i₀⟩;
      ∀ (u : Fin D.d → ℝ) (z : D.Z),
        D.decLoss u z = commonDivisor D.carrier.supp u ^ 2 * frobSq (rmatMul (eΓ z) Z)) :
    DecoratedBoxThresholdFinite D := by
  letI := D.mZ; letI := D.fι; haveI : Nonempty D.ι := ⟨i₀⟩
  intro c' hc'
  set k := sharedDivisorExp D.carrier.supp with hk
  rw [carrierThreshold] at hc'
  -- split off the degenerate `minAdm M = 0` (threshold `0`, so `c' < 0` is vacuous).
  rcases Nat.eq_zero_or_pos (minAdm M) with hm0 | hmpos_nat
  · exfalso
    rw [hm0] at hc'; simp only [Nat.cast_zero, zero_div] at hc'
    exact absurd hc' (not_lt.mpr c'.coe_nonneg)
  -- `minAdm M > 0`; the leaf identity gives `a·n ≥ minAdm M > 0` and the `Γ`-budget `≥ ½·minAdm`.
  have han : 0 < a * n := lt_of_lt_of_le hmpos_nat hdim
  have hmpos : (0 : ℝ) < (minAdm M : ℝ) := by exact_mod_cast hmpos_nat
  have hmle : (minAdm M : ℝ) ≤ (a : ℝ) * (n : ℝ) := by exact_mod_cast hdim
  have hcltan : (c' : ℝ) < (a * n : ℝ) / 2 := by
    have : (c' : ℝ) < (minAdm M : ℝ) / 2 := hc'
    linarith
  have hden : ENNReal.ofReal ((minAdm M : ℝ) / 2) = (minAdm M : ℝ≥0∞) / 2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_natCast,
      ENNReal.ofReal_ofNat]
  have hc'enn : (c' : ℝ≥0∞) < (minAdm M : ℝ≥0∞) / 2 := by
    rw [← hden, ← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff (div_pos hmpos (by norm_num))).mpr hc'
  have hax : ∀ j, (c' : ℝ≥0∞) < axisRatio (D.jac j) (k j) := by
    intro j
    have hle : monomialThreshold D.d k D.jac ≤ axisRatio (D.jac j) (k j) := by
      rw [monomialThreshold_eq_iInf_axisRatio]; exact iInf_le _ j
    exact lt_of_lt_of_le (lt_of_lt_of_le hc'enn hbeta) hle
  have hIu : (∫⁻ u in unitBox D.d,
      ENNReal.ofReal (monomialIntegrand D.d k D.jac (c' : ℝ) u)) < ⊤ :=
    monomialIntegrand_lintegral_unitBox_lt_top D.d k D.jac (c' : ℝ)
      (fun j => axisRatio_lt_exp (hax j))
  have hIΓ : (∫⁻ z in D.dom,
      ENNReal.ofReal ((frobSq (rmatMul (eΓ z) Z)) ^ (-(c' : ℝ)))) < ⊤ := by
    rw [hdom, hmp.setLIntegral_comp_preimage_emb eΓ.measurableEmbedding
      (fun Γ => ENNReal.ofReal ((frobSq (rmatMul Γ Z)) ^ (-(c' : ℝ)))) (matBox a n 1)]
    exact corankLeaf_rpow_lt_top han Z cpos hcpos hZ (c' : ℝ) c'.coe_nonneg hcltan 1 one_pos
  have hpt : ∀ (u : Fin D.d → ℝ) (z : D.Z),
      (∏ ℓ, |u ℓ| ^ D.jac ℓ) * D.decLoss u z ^ (-(c' : ℝ))
        = monomialIntegrand D.d k D.jac (c' : ℝ) u
          * (frobSq (rmatMul (eΓ z) Z)) ^ (-(c' : ℝ)) := by
    intro u z
    rw [hdec u z, Real.mul_rpow (by positivity) (frobSq_nonneg _), ← mul_assoc]
    congr 1
    rw [monomialIntegrand, commonDivisor_sq]
  have hkey : D.integral (c' : ℝ)
      = (∫⁻ u in unitBox D.d, ENNReal.ofReal (monomialIntegrand D.d k D.jac (c' : ℝ) u))
        * (∫⁻ z in D.dom, ENNReal.ofReal ((frobSq (rmatMul (eΓ z) Z)) ^ (-(c' : ℝ)))) := by
    unfold SJDecoration.integral
    rw [← lintegral_const_mul' _ _ hIu.ne]
    refine setLIntegral_congr_fun ?_ (fun z _ => ?_)
    · rw [hdom]; exact (matBox_measurableSet a n 1).preimage eΓ.measurable
    · rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr (fun u => ?_)
      rw [hpt u z, ENNReal.ofReal_mul (monomialIntegrand_nonneg' D.d k D.jac (c' : ℝ) u)]
  rw [hkey]
  exact ENNReal.mul_lt_top hIu hIΓ

/-- **`rmatMul X 1 = X`** — right-multiplication by the identity is the identity (entrywise). The
width-2 tail collapse `Z_tail = prod (dropHead M) ≡ 1` (`tailProd_width2`) turns each residual
`rmatMul (eΓ z).1 (Z_tail r)` into the plain front-block entry `(eΓ z).1`. -/
theorem rmatMul_one {p n : ℕ} (X : Fin p → Fin n → ℝ) :
    rmatMul X (1 : Matrix (Fin n) (Fin n) ℝ) = X := by
  funext i j
  simp only [rmatMul, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-! ## Case (iii), product-domain variant — the units-FREE Γ×tail split -/

/-- **`DecoratedBaseHyp` case (iii), PRODUCT-domain variant (units-free Γ×tail split).** Same route-A
analytic core as `decoratedBase_routeA_of_leafForm`, but the deeper measure iso now SPLITS
`eΓ : D.Z ≃ᵐ (Fin a → Fin n → ℝ) × R` (front free block × tail coordinate `R`, a finite-measure box
`Rbox`), and the loss reads off the front block against a FIXED tail `Z` — `decLoss u z =
commonDivisor(u)² · frobSq (Γ(z) · Z)` with `Γ(z) = (eΓ z).1`. This is the shape the units-FREE
`gammaPrimeClause` produces at the width-2 base after the tail collapses (`prod (dropHead M) ≡ 1`, so
`Z = 1`, `cpos = 1`, `hZ = (0).PosSemidef`). The tail coordinate contributes only a FINITE volume factor
`volume Rbox < ⊤` (the integrand is constant in `r`, bounded by the measurability-free Tonelli
`lintegral_prod_le`); the front-block integral is the banked `corankLeaf_rpow_lt_top`. No units bound is
CARRIED — it is DERIVED at the base via `Z = 1`. -/
theorem decoratedBase_routeA_of_leafForm_prod {M : Fin (1 + 1) → ℕ} (D : SJDecoration M) (i₀ : D.ι)
    (a n Dt : ℕ) (R : Type) [mR : MeasureSpace R] [SFinite (volume : Measure R)] (Rbox : Set R)
    (hRmeas : MeasurableSet Rbox) (hRfin : (volume : Measure R) Rbox < ⊤)
    (Z : Matrix (Fin n) (Fin Dt) ℝ) (cpos : ℝ) (hcpos : 0 < cpos)
    (hZ : (Z * Zᵀ - cpos • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (eΓ : letI := D.mZ; D.Z ≃ᵐ (Fin a → Fin n → ℝ) × R)
    (hmp : letI := D.mZ; MeasurePreserving eΓ)
    (hdom : letI := D.mZ; D.dom = eΓ ⁻¹' (matBox a n 1 ×ˢ Rbox)) (hdim : minAdm M ≤ a * n)
    (hbeta : letI := D.fι; letI : Nonempty D.ι := ⟨i₀⟩;
      (minAdm M : ℝ≥0∞) / 2 ≤ monomialThreshold D.d (sharedDivisorExp D.carrier.supp) D.jac)
    (hdec : letI := D.mZ; letI := D.fι; letI : Nonempty D.ι := ⟨i₀⟩;
      ∀ (u : Fin D.d → ℝ) (z : D.Z),
        D.decLoss u z = commonDivisor D.carrier.supp u ^ 2 * frobSq (rmatMul (eΓ z).1 Z)) :
    DecoratedBoxThresholdFinite D := by
  letI := D.mZ; letI := D.fι; haveI : Nonempty D.ι := ⟨i₀⟩
  intro c' hc'
  set k := sharedDivisorExp D.carrier.supp with hk
  rw [carrierThreshold] at hc'
  rcases Nat.eq_zero_or_pos (minAdm M) with hm0 | hmpos_nat
  · exfalso
    rw [hm0] at hc'; simp only [Nat.cast_zero, zero_div] at hc'
    exact absurd hc' (not_lt.mpr c'.coe_nonneg)
  have han : 0 < a * n := lt_of_lt_of_le hmpos_nat hdim
  have hmpos : (0 : ℝ) < (minAdm M : ℝ) := by exact_mod_cast hmpos_nat
  have hmle : (minAdm M : ℝ) ≤ (a : ℝ) * (n : ℝ) := by exact_mod_cast hdim
  have hcltan : (c' : ℝ) < (a * n : ℝ) / 2 := by
    have : (c' : ℝ) < (minAdm M : ℝ) / 2 := hc'
    linarith
  have hden : ENNReal.ofReal ((minAdm M : ℝ) / 2) = (minAdm M : ℝ≥0∞) / 2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_natCast,
      ENNReal.ofReal_ofNat]
  have hc'enn : (c' : ℝ≥0∞) < (minAdm M : ℝ≥0∞) / 2 := by
    rw [← hden, ← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff (div_pos hmpos (by norm_num))).mpr hc'
  have hax : ∀ j, (c' : ℝ≥0∞) < axisRatio (D.jac j) (k j) := by
    intro j
    have hle : monomialThreshold D.d k D.jac ≤ axisRatio (D.jac j) (k j) := by
      rw [monomialThreshold_eq_iInf_axisRatio]; exact iInf_le _ j
    exact lt_of_lt_of_le (lt_of_lt_of_le hc'enn hbeta) hle
  have hIu : (∫⁻ u in unitBox D.d,
      ENNReal.ofReal (monomialIntegrand D.d k D.jac (c' : ℝ) u)) < ⊤ :=
    monomialIntegrand_lintegral_unitBox_lt_top D.d k D.jac (c' : ℝ)
      (fun j => axisRatio_lt_exp (hax j))
  -- the PRODUCT-domain Γ-integral finiteness: CoV to `matBox ×ˢ Rbox`, Tonelli-bound (integrand constant
  -- in the tail `r`), giving `volume Rbox · corankLeaf < ⊤`.
  have hIΓ : (∫⁻ z in D.dom,
      ENNReal.ofReal ((frobSq (rmatMul (eΓ z).1 Z)) ^ (-(c' : ℝ)))) < ⊤ := by
    rw [hdom, hmp.setLIntegral_comp_preimage_emb eΓ.measurableEmbedding
      (fun p => ENNReal.ofReal ((frobSq (rmatMul p.1 Z)) ^ (-(c' : ℝ)))) (matBox a n 1 ×ˢ Rbox)]
    have hle : (∫⁻ p in (matBox a n 1 ×ˢ Rbox),
          ENNReal.ofReal ((frobSq (rmatMul p.1 Z)) ^ (-(c' : ℝ))))
        ≤ (volume : Measure R) Rbox
            * ∫⁻ Γ in matBox a n 1, ENNReal.ofReal ((frobSq (rmatMul Γ Z)) ^ (-(c' : ℝ))) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      refine le_trans (lintegral_prod_le _) ?_
      have hcong : (∫⁻ Γ, ∫⁻ _r,
            ENNReal.ofReal ((frobSq (rmatMul Γ Z)) ^ (-(c' : ℝ)))
              ∂(volume : Measure R).restrict Rbox
            ∂(volume : Measure (Fin a → Fin n → ℝ)).restrict (matBox a n 1))
          = ∫⁻ Γ in matBox a n 1,
              ENNReal.ofReal ((frobSq (rmatMul Γ Z)) ^ (-(c' : ℝ))) * (volume : Measure R) Rbox := by
        refine lintegral_congr (fun Γ => ?_)
        rw [setLIntegral_const]
      rw [hcong, lintegral_mul_const' _ _ hRfin.ne, mul_comm]
    refine lt_of_le_of_lt hle (ENNReal.mul_lt_top hRfin ?_)
    exact corankLeaf_rpow_lt_top han Z cpos hcpos hZ (c' : ℝ) c'.coe_nonneg hcltan 1 one_pos
  have hpt : ∀ (u : Fin D.d → ℝ) (z : D.Z),
      (∏ ℓ, |u ℓ| ^ D.jac ℓ) * D.decLoss u z ^ (-(c' : ℝ))
        = monomialIntegrand D.d k D.jac (c' : ℝ) u
          * (frobSq (rmatMul (eΓ z).1 Z)) ^ (-(c' : ℝ)) := by
    intro u z
    rw [hdec u z, Real.mul_rpow (by positivity) (frobSq_nonneg _), ← mul_assoc]
    congr 1
    rw [monomialIntegrand, commonDivisor_sq]
  have hkey : D.integral (c' : ℝ)
      = (∫⁻ u in unitBox D.d, ENNReal.ofReal (monomialIntegrand D.d k D.jac (c' : ℝ) u))
        * (∫⁻ z in D.dom, ENNReal.ofReal ((frobSq (rmatMul (eΓ z).1 Z)) ^ (-(c' : ℝ)))) := by
    unfold SJDecoration.integral
    rw [← lintegral_const_mul' _ _ hIu.ne]
    refine setLIntegral_congr_fun ?_ (fun z _ => ?_)
    · rw [hdom]
      exact ((matBox_measurableSet a n 1).prod hRmeas).preimage eΓ.measurable
    · rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr (fun u => ?_)
      rw [hpt u z, ENNReal.ofReal_mul (monomialIntegrand_nonneg' D.d k D.jac (c' : ℝ) u)]
  rw [hkey]
  exact ENNReal.mul_lt_top hIu hIΓ

/-! ## The weighted loss factoring (the `commonDivisor²` split — the u-structure is DERIVED) -/

/-- **The decorated loss factors through the common divisor (the WEIGHTED form).**
Splitting each generator monomial through the common divisor (`genMonomial_factor`, banked), the
decorated loss is `commonDivisor(u)²` times the residual sum weighted by the LEFTOVER monomials
`u^{δ_i} = genMonomial (residualSupport supp) i u` (`δ_iℓ = supp i ℓ − k_ℓ`). This is the u-part of
the co-design's WEIGHTED identity — DERIVED from the carrier algebra, not carried: only the
generator↔product-entry provenance `res_i = [Γ·Z_tail]_{ρ(i)}` need be a `FaithfulSJAt` clause. When
the leftover support vanishes on a SPANNING set of generators (the S2 spanning-zero-leftover case)
this lower-bounds `decLoss` by `commonDivisor(u)² · frobSq (Γ·Z_tail)`, feeding the route-A leaf. -/
theorem decLoss_commonDivisor_factor {M : Fin (L + 1) → ℕ} (D : SJDecoration M) (i₀ : D.ι)
    (u : Fin D.d → ℝ) (z : D.Z) :
    letI := D.fν; letI := D.fι; letI : Nonempty D.ι := ⟨i₀⟩
    D.decLoss u z
      = commonDivisor D.carrier.supp u ^ 2
        * ∑ i, (genMonomial (residualSupport D.carrier.supp) i u
            * D.carrier.residual (D.ctx z).1 (D.ctx z).2 i) ^ 2 := by
  letI := D.fν; letI := D.fι; haveI : Nonempty D.ι := ⟨i₀⟩
  unfold SJDecoration.decLoss SJLinGenState.loss
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [SJLinGenState.gen_eq, genMonomial_factor]
  ring

/-- **Under UNIFORM residual support (`supp ≡ sharedDivisorExp`) the loss collapses to the CLEAN
form `commonDivisor² · Σ_i res_i²`.** This is the S2=yes (uniform, cover's rowMix
constant-support-faithful) bridge: every leftover monomial is `1`, so `decLoss_commonDivisor_factor`
drops to the unweighted residual sum — an EQUALITY, holding at all arities, no spanning argument.
Composed with the residual-provenance `res_i = (Γ·Z_tail)_{ρ i}` (`ρ` a bijection) this is
`commonDivisor² · frobSq (Γ·Z_tail)`, feeding `decoratedBase_routeA_of_leafForm`. -/
theorem decLoss_clean_of_uniformResidualSupport {M : Fin (L + 1) → ℕ} (D : SJDecoration M)
    (i₀ : D.ι)
    (huniform : letI := D.fι; letI : Nonempty D.ι := ⟨i₀⟩;
      ∀ (i : D.ι) (ℓ : Fin D.d), D.carrier.supp i ℓ = sharedDivisorExp D.carrier.supp ℓ)
    (u : Fin D.d → ℝ) (z : D.Z) :
    letI := D.fν; letI := D.fι; letI : Nonempty D.ι := ⟨i₀⟩
    D.decLoss u z
      = commonDivisor D.carrier.supp u ^ 2
        * ∑ i, (D.carrier.residual (D.ctx z).1 (D.ctx z).2 i) ^ 2 := by
  letI := D.fν; letI := D.fι; haveI : Nonempty D.ι := ⟨i₀⟩
  rw [decLoss_commonDivisor_factor D i₀ u z]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hg1 : genMonomial (residualSupport D.carrier.supp) i u = 1 := by
    unfold genMonomial residualSupport
    exact Finset.prod_eq_one (fun ℓ _ => by rw [huniform i ℓ, Nat.sub_self, pow_zero])
  rw [hg1, one_mul]

/-! ## PREP — the WEIGHTED leaf-form provenance clause (the carried gamma-prime)

The carried `d ≥ 1` clause of the strengthened `FaithfulSJAt` (`faithfulsj-design` cover co-design).
Type-checked and staged here; NOT yet committed into `RouteMSJAdm.FaithfulSJAt` — held for cover's
S2 rowMix verdict + fidelity audit (avoid a further flip on the fidelity-critical def). -/

/-- **The weighted leaf-form provenance (the carried d≥1 clause, faithful at all arities).** There
free active block `Gamma z`, a z-DEPENDENT deeper tail family `Ztail z` (identified via
`genuineCarrier`'s product, NOT a fixed matrix), a generator-to-entry map `rho`, and the free-block
dimension bound `minAdm M ≤ a * n`, with each residual the `rho i` entry of the product
`Gamma z * Ztail z`. With `decLoss_commonDivisor_factor` (the DERIVED u-part) this gives the
weighted loss identity, true at every arity (leftover monomials survive mid-recursion). The clean
`commonDivisor^2 * frobSq (Gamma * Ztail)` and `Ztail = 1` are DERIVED-AT-BASE only, under the S2
spanning-zero-leftover condition (leftover support `0` on a spanning generator set) — the unforced
obligation cover's rowMix trace settles: on S2 yes `decoratedBase_routeA_of_leafForm` closes #4,
the anisotropic leaf. The standalone units bound is DROPPED (vacuous; derived-at-base). -/
def WeightedLeafForm {M : Fin (L + 1) → ℕ} (D : SJDecoration M) (i₀ : D.ι) : Prop :=
  letI := D.mZ; letI := D.fν; letI := D.fι; letI : Nonempty D.ι := ⟨i₀⟩
  ∃ (a n Dt : ℕ) (Γ : D.Z → Matrix (Fin a) (Fin n) ℝ)
    (Ztail : D.Z → Matrix (Fin n) (Fin Dt) ℝ) (ρ : D.ι → Fin a × Fin Dt),
    minAdm M ≤ a * n ∧
    ∀ (z : D.Z) (i : D.ι),
      D.carrier.residual (D.ctx z).1 (D.ctx z).2 i = (Γ z * Ztail z) (ρ i).1 (ρ i).2

/-! ## #4 — the full `DecoratedBaseHyp adm` (the 3-way dispatch, S2-uniform base) -/

/-- **Transport cancellation `(h ▸ f) (h ▸ x) = f x`.** A function transported along a type eq,
applied at the transported argument, recovers the original value. Proved generally (`subst`) — the
handle for the `d = 0` observable→product-loss step, where `genuineCarrier`'s `ctx = prod` lives
under the `D.ν = Params-index` transport `hν ▸ (D.ctx z).2`. -/
theorem eqRec_fun_apply_eqRec {α β : Type} (h : α = β) (f : α → ℝ) (x : α) :
    (h ▸ f) (h ▸ x) = f x := by subst h; rfl

/-- **`DecoratedBaseHyp adm` — #4 COMPLETE (S2 settled uniform).** At a width-2 chain, the `adm`
disjunction dispatches: (i) a degenerate binding corank → `decoratedBase_corankZero` (vacuous);
(ii) the `d = 0` observable-loss leaf → `decoratedBase_d0_of_lossEq`, deriving
`decLoss = frobSq (prod M (e z))` from the observable form + `genuineCarrier`'s `ctx = prod` clause
(the `hν`-transport cancelled by `eqRec_fun_apply_eqRec`); (iii) the `d ≥ 1` resolved corner →
`decoratedBase_routeA_of_leafForm`, consuming `FaithfulSJAt`'s clean route-A leaf-form bundle
(`Z_tail = I`-at-base baked into the carried clean identity, S2 §★★★). -/
theorem decoratedBaseHyp_faithful : DecoratedBaseHyp adm := by
  intro M D hD
  obtain ⟨hgen, hdisj⟩ := hD
  rcases hdisj with hck | hck | hf
  · exact decoratedBase_corankZero D (Or.inl hck)
  · exact decoratedBase_corankZero D (Or.inr hck)
  · obtain ⟨hζ, hν, e, hmpe, hdome, hctx⟩ := hgen
    rcases hf with ⟨hd0, hobs⟩ | ⟨_hd1, i₀, _halpha, hbeta, hdelta0, hgamma⟩
    · -- (ii) `d = 0` observable-loss leaf.
      refine decoratedBase_d0_of_lossEq D e hmpe hdome hd0 (fun u z => ?_)
      letI := D.fν; letI := D.fι
      rw [SJDecoration.decLoss, hobs (D.ctx z).1 (D.ctx z).2 u]
      have hfrob : frobSq (prod M (e z))
          = ∑ ik : (Fin (M 0) × Fin (M (Fin.last 1))), (prod M (e z) ik.1 ik.2) ^ 2 := by
        rw [frobSq, Fintype.sum_prod_type]
      rw [hfrob]
      refine Fintype.sum_equiv (Equiv.cast hν) _ _ (fun v => ?_)
      have hEq : (D.ctx z).2 v = prod M (e z) (Equiv.cast hν v).1 (Equiv.cast hν v).2 := by
        rw [← eqRec_fun_apply_eqRec hν (D.ctx z).2 v]
        exact congrFun (hctx z) (Equiv.cast hν v)
      rw [hEq]
    · -- (iii) `d ≥ 1` resolved corner (units-FREE Γ×tail split). At the width-2 base the head-dropped
      -- tail collapses (`prod (dropHead M) ≡ 1`, `tailProd_width2`), so the fixed tail is `Z = 1` and
      -- the DROPPED units bound is DERIVED (`c = 1`, `(1·1ᵀ − 1•1) = 0` PosSemidef). DERIVE the clean
      -- loss from `δ≡0` (uniform support) + the provenance `res = (Γ·Z_tail)_{ρ}` (ρ a bijection),
      -- then close via the product-domain route-A wrapper (`corankLeaf` × finite tail-box volume).
      obtain ⟨a, eΓ, ρ, hmpΓ, hdomΓ, hdim, hprov⟩ := hgamma
      letI := D.fν; letI := D.fι; haveI : Nonempty D.ι := ⟨i₀⟩
      -- the fixed base tail is the identity ⟹ the units bound holds with `c = 1`.
      have hZ : ((1 : Matrix (Fin (M 1)) (Fin (M 1)) ℝ) * (1 : Matrix (Fin (M 1)) (Fin (M 1)) ℝ)ᵀ
          - (1 : ℝ) • (1 : Matrix (Fin (M 1)) (Fin (M 1)) ℝ)).PosSemidef := by
        rw [Matrix.transpose_one, Matrix.mul_one, one_smul, sub_self]
        exact Matrix.PosSemidef.zero
      -- the head-dropped tail box is a one-point (no-layer) space, so it has finite volume.
      have hRmeas : MeasurableSet (paramsBoxM (dropHead M) 1) :=
        measurableSet_paramsBoxM (dropHead M) 1
      haveI hfin : IsFiniteMeasure (volume : Measure (Params (dropHead M))) := by
        rw [show (volume : Measure (Params (dropHead M))) = Measure.dirac isEmptyElim from
            Measure.volume_pi_eq_dirac]
        infer_instance
      have hRfin : (volume : Measure (Params (dropHead M))) (paramsBoxM (dropHead M) 1) < ⊤ :=
        measure_lt_top _ _
      -- the clean loss (δ≡0 collapse + provenance + tail `≡ 1`, `rmatMul _ 1 = _`).
      have hprov1 : ∀ (z : D.Z) (i : D.ι),
          D.carrier.residual (D.ctx z).1 (D.ctx z).2 i = (eΓ z).1 (ρ i).1 (ρ i).2 := by
        intro z i
        rw [hprov z i, tailProd_width2 M (eΓ z).2]
        exact congrFun (congrFun (rmatMul_one (eΓ z).1) (ρ i).1) (ρ i).2
      have hdec : ∀ (u : Fin D.d → ℝ) (z : D.Z),
          D.decLoss u z = commonDivisor D.carrier.supp u ^ 2
            * frobSq (rmatMul (eΓ z).1 (1 : Matrix (Fin (M 1)) (Fin (M 1)) ℝ)) := by
        intro u z
        rw [decLoss_clean_of_uniformResidualSupport D i₀ hdelta0 u z, rmatMul_one]
        congr 1
        have hsc : ∀ i, (D.carrier.residual (D.ctx z).1 (D.ctx z).2 i) ^ 2
            = ((eΓ z).1 (ρ i).1 (ρ i).2) ^ 2 := fun i => by rw [hprov1 z i]
        rw [Finset.sum_congr rfl (fun i _ => hsc i),
          Equiv.sum_comp ρ (fun pq => ((eΓ z).1 pq.1 pq.2) ^ 2), frobSq]
        exact Fintype.sum_prod_type (fun pq => ((eΓ z).1 pq.1 pq.2) ^ 2)
      exact decoratedBase_routeA_of_leafForm_prod D i₀ a (M 1) (M 1) (Params (dropHead M))
        (paramsBoxM (dropHead M) 1) hRmeas hRfin (1 : Matrix (Fin (M 1)) (Fin (M 1)) ℝ) 1 one_pos hZ
        eΓ hmpΓ hdomΓ hdim hbeta hdec

/-! ## P4 — the width-3 non-vacuity witness (anti-vacuity guard, bedrock)

The units-free `gammaPrimeClause` is NON-VACUOUS at INTERMEDIATE arity — the exact place the fixed-Z γ'
was vacuous (a single fixed `Z` cannot equal the varying deeper product mid-recursion). Here `M = (2,2,2)`
(`L = 2`, `minAdm = 3`, both binding coranks `> 0` so the `d ≥ 1` disjunct is genuinely REQUIRED): a
concrete decoration on `Z = (front block) × Params (dropHead M)` with `eΓ = refl`, the genuine tail
product `Z_tail = prod (dropHead M)` (a NON-trivial single tail layer `A⁽²⁾` here, NOT the identity), and
`ρ = id` satisfies the resolved-corner branch of `FaithfulSJAt` (α `pSimultaneous`, β `½·minAdm ≤
monomialThreshold` = `axisRatio 3 1 = 2 ≥ 3/2`, δ≡0 uniform support, γ' provenance). This is the
`P0`-cert §2 witness transported to the sound Γ×tail encoding. (The `genuineCarrier` clause of `adm` is
NOT asserted here — it would require the front/tail measure-split of `Params M`, which is `#5`'s peelOp
obligation; the guard is for the `FaithfulSJAt` γ' clause specifically, the one that was vacuous.) -/

/-- The width-3 non-vacuity witness decoration on `M = (2,2,2)`: `d = 1`, uniform support `≡ 1`,
`jac = ![3]`, deeper space `(front block) × (tail params)`, residuals reading off the genuine layer
product `Γ · A⁽²⁾`. -/
noncomputable def witnessDecoration222 : SJDecoration (![2, 2, 2] : Fin 3 → ℕ) where
  d := 1
  ζ := Unit
  ν := Fin 2 × Fin 2
  ι := Fin 2 × Fin 2
  fν := inferInstance
  fι := inferInstance
  carrier :=
    ({ supp := fun _ _ => 1
       coeff := fun _ ik v => if v = ik then 1 else 0 } :
      SJLinGenState Unit (Fin 2 × Fin 2) (Fin 2 × Fin 2) 1)
  jac := ![3]
  Z := (Fin 2 → Fin 2 → ℝ) × Params (dropHead (![2, 2, 2] : Fin 3 → ℕ))
  mZ := inferInstance
  ctx := fun z =>
    ((), fun ik => rmatMul z.1 (prod (dropHead (![2, 2, 2] : Fin 3 → ℕ)) z.2) ik.1 ik.2)
  dom := matBox 2 2 1 ×ˢ paramsBoxM (dropHead (![2, 2, 2] : Fin 3 → ℕ)) 1
  residualMeas := by
    intro i
    have hz : Continuous fun z : (Fin 2 → Fin 2 → ℝ) ×
        Params (dropHead (![2, 2, 2] : Fin 3 → ℕ)) => z.1 := continuous_fst
    have hr : Continuous fun z : (Fin 2 → Fin 2 → ℝ) ×
        Params (dropHead (![2, 2, 2] : Fin 3 → ℕ)) => z.2 := continuous_snd
    have hcont : Continuous fun z : (Fin 2 → Fin 2 → ℝ) ×
        Params (dropHead (![2, 2, 2] : Fin 3 → ℕ)) =>
        rmatMul z.1 (prod (dropHead (![2, 2, 2] : Fin 3 → ℕ)) z.2) i.1 i.2 := by
      simp only [rmatMul]
      refine continuous_finset_sum _ (fun k _ => ?_)
      exact ((continuous_apply k).comp ((continuous_apply i.1).comp hz)).mul
        (((continuous_prod (dropHead (![2, 2, 2] : Fin 3 → ℕ))).matrix_elem k i.2).comp hr)
    simp only [SJLinGenState.residual, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact hcont.measurable

/-- **P4 — the units-free γ' is NON-VACUOUS at intermediate arity.** The resolved-corner (`d ≥ 1`) branch
of `FaithfulSJAt` is inhabited by `witnessDecoration222` on the width-3 chain `(2,2,2)` — where the
head-dropped tail is a genuine (non-identity) single layer, so the fixed-Z γ' was vacuous. Guards against
the silent-vacuity trap: the units-free Γ×tail `gammaPrimeClause` is genuinely satisfiable mid-recursion
(with `eΓ = refl`, `Z_tail = prod (dropHead M)`, `ρ = id`). -/
theorem witnessDecoration222_faithful : FaithfulSJAt witnessDecoration222 := by
  letI : Fintype witnessDecoration222.ι := witnessDecoration222.fι
  letI : Fintype witnessDecoration222.ν := witnessDecoration222.fν
  letI : Nonempty witnessDecoration222.ι := ⟨(0, 0)⟩
  letI : MeasureSpace witnessDecoration222.Z := witnessDecoration222.mZ
  refine Or.inr ⟨le_refl 1, (0, 0), ?_, ?_, ?_, ?_⟩
  · -- (α) pSimultaneous: uniform support `≡ 1`.
    intro j ℓ; exact le_refl 1
  · -- (β) threshold: `½·minAdm = 3/2 ≤ ⨅ axisRatio = axisRatio 3 1 = 2` (per direction, `le_iInf`).
    have hk : ∀ ℓ, sharedDivisorExp witnessDecoration222.carrier.supp ℓ = 1 := fun ℓ =>
      le_antisymm (sharedDivisorExp_le _ (0, 0) ℓ) (Finset.le_inf' _ _ (fun i _ => le_refl 1))
    rw [monomialThreshold_eq_iInf_axisRatio, show minAdm (![2, 2, 2] : Fin 3 → ℕ) = 3 from by decide]
    refine le_iInf (fun j => ?_)
    rw [hk j, show witnessDecoration222.jac j = 3 by fin_cases j; rfl,
      show (3 : ℕ) = 4 - 1 from rfl, axisRatio_regularSeq 4 (by norm_num)]
    gcongr <;> norm_num
  · -- (δ≡0) uniform support: `supp i ℓ = sharedDivisorExp supp ℓ = 1`.
    intro i ℓ
    exact (le_antisymm (sharedDivisorExp_le _ i ℓ) (Finset.le_inf' _ _ (fun j _ => le_refl 1))).symm
  · -- (γ') provenance: `eΓ = refl`, `Z_tail = prod (dropHead M)`, `ρ = id`.
    refine ⟨2, MeasurableEquiv.refl _, Equiv.refl _, MeasurePreserving.id _, by rfl, by decide, ?_⟩
    intro z i
    show witnessDecoration222.carrier.residual (witnessDecoration222.ctx z).1
        (witnessDecoration222.ctx z).2 i
        = rmatMul z.1 (prod (dropHead (![2, 2, 2] : Fin 3 → ℕ)) z.2) i.1 i.2
    simp only [SJLinGenState.residual, witnessDecoration222, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]

end DLNFibre.DLN.RLCT
