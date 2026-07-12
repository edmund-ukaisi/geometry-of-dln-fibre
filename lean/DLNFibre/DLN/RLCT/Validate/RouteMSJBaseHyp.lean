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
    · -- (iii) `d ≥ 1` resolved corner. DERIVE the clean loss from `δ≡0` (uniform support) + the
      -- provenance `res = (Γ·Z)_{ρ}` (ρ a bijection), then close via route-A `corankLeaf`.
      obtain ⟨a, n, Dt, Z, c, eΓ, ρ, hc, hZ, hmpΓ, hdomΓ, hdim, hprov⟩ := hgamma
      letI := D.fν; letI := D.fι; haveI : Nonempty D.ι := ⟨i₀⟩
      have hdec : ∀ (u : Fin D.d → ℝ) (z : D.Z),
          D.decLoss u z = commonDivisor D.carrier.supp u ^ 2 * frobSq (rmatMul (eΓ z) Z) := by
        intro u z
        rw [decLoss_clean_of_uniformResidualSupport D i₀ hdelta0 u z]
        congr 1
        have hsc : ∀ i, (D.carrier.residual (D.ctx z).1 (D.ctx z).2 i) ^ 2
            = (rmatMul (eΓ z) Z (ρ i).1 (ρ i).2) ^ 2 := fun i => by rw [hprov z i]
        rw [Finset.sum_congr rfl (fun i _ => hsc i),
          Equiv.sum_comp ρ (fun pq => (rmatMul (eΓ z) Z pq.1 pq.2) ^ 2),
          frobSq, Fintype.sum_prod_type]
      exact decoratedBase_routeA_of_leafForm D i₀ a n Dt Z c hc hZ eΓ hmpΓ hdomΓ hdim hbeta hdec

end DLNFibre.DLN.RLCT
