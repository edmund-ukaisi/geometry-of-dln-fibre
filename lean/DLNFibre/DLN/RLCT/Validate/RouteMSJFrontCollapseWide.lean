import DLNFibre.DLN.RLCT.Validate.RouteMSJFrontCoV
import DLNFibre.DLN.RLCT.Validate.RouteMSJCornerLoss
import DLNFibre.DLN.RLCT.Validate.RouteMFrontPeel

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJFrontCollapseWide` — the `a=0` WIDE BOUNDED arm

**Thread `a0wire` (Lane-1 front-collapse, brick iii).** Wires the `a=0` wide bounded base of the
front-collapse atom: for a wide front (`M₀ ≤ M₁`) in the bounded density regime
(`M₂ < M₁ − M₀ + 1`), the front-factor box integral over `wingFrontBox M × paramsBoxM(tailChain M)`
is finite, GIVEN the plain one-shorter IH `hIH`.

The route (d1design Lane-1 GS route, pointwise-in-`F`, NO Cauchy–Binet) consumes the banked
`fixedF_wide_cov_bound` (`RouteMSJFrontCoV`, the two-matrix absorption CoV producing the free-`F`
Gram Jacobian `det(F·Fᵀ)^{−M₂/2}` and a radius-`M₁` `W`-box), `front_gram_qbox_lt_top` (the
`F`-integral of that Jacobian, finite in the bounded regime), and `redChain_box_lt_top` (the
reduced-chain box the plain IH closes at the unshifted exponent, saturated charge zero).

Steps (per the tide spec):
1. `hdet` — `det(F·Fᵀ) ≠ 0` on `wingFrontBox M`.
2/3. `hsplit` — the fixed-`F` fibre split `∫_{A'} frobSq(F·prod A')^{−c'} = ∫_{A₁ box 1} g(F·A₁)`.
4. pointwise `fixedF_wide_cov_bound` + `lintegral_mono` over `F`.
5/6. `hKfin` — the radius-`M₁` `W`-box integral `∫_{W box M₁} g < ⊤` (redChain box + `W`-scaling).
7. the `F`-integral of the Gram Jacobian, finite by `front_gram_qbox_lt_top`.
8. assemble the product of finite factors.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal BigOperators Matrix

variable {L : ℕ}

/-! ## Generic front-factor split (arity ≥ 2, uniform in `L`)

The banked front-split machinery (`eFront`, `routeMLayerBoxIntegral_front_split`) is stated for the
arity-≥3 shape `Fin (L+1+1+1)`. Both `hsplit` (peel the front of `tailChain M`) and `hKfin`
(identify the radius-1 `W`-box with the reduced-chain box) peel the FRONT layer off an
arity-≥2 chain, uniformly in `L`. This block re-derives the three supporting facts generically. -/

/-- **`rmatMul` associativity** (the raw double-sum reassociation). -/
theorem rmatMul_mul_assoc {p n q r : ℕ} (F : Fin p → Fin n → ℝ) (X : Fin n → Fin q → ℝ)
    (Y : Fin q → Fin r → ℝ) :
    rmatMul F (rmatMul X Y) = rmatMul (rmatMul F X) Y := by
  funext i j
  simp only [rmatMul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => by ring))

/-- **`rmatMul` by the identity on the left is the identity.** -/
theorem rmatMul_one_left {p q : ℕ} (Y : Fin p → Fin q → ℝ) :
    rmatMul (1 : Matrix (Fin p) (Fin p) ℝ) Y = Y := by
  funext i j
  simp only [rmatMul, Matrix.one_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

/-- **The matrix box has finite volume** (a finite product of finite-length intervals). -/
theorem volume_matBox_lt_top (p q : ℕ) (T : ℝ) : volume (matBox p q T) < ⊤ := by
  have hset : matBox p q T
      = Set.univ.pi (fun _ : Fin p => Set.univ.pi (fun _ : Fin q => Set.Icc (-T) T)) := by
    ext X; simp only [matBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  rw [hset, volume_pi_pi]
  refine ENNReal.prod_lt_top (fun i _ => ?_)
  rw [volume_pi_pi]
  refine ENNReal.prod_lt_top (fun j _ => ?_)
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

/-- **The generic front-peel measurable equiv**, `Params N ≃ᵐ (N₀×N₁ matrix) × Params (Mtail N)`,
peeling layer `0`. Definitionally `piFinSuccAbove` at `0` (the arity-≥2 analog of `eFront`). -/
noncomputable def eFrontN {n : ℕ} (N : Fin (n + 1 + 1) → ℕ) :
    Params N ≃ᵐ (Fin (N 0) → Fin (N 1) → ℝ) × Params (Mtail N) :=
  MeasurableEquiv.piFinSuccAbove
    (fun s : Fin (n + 1) => Fin (N s.castSucc) → Fin (N s.succ) → ℝ) 0

/-- `eFrontN` is measure-preserving. -/
theorem measurePreserving_eFrontN {n : ℕ} (N : Fin (n + 1 + 1) → ℕ) :
    MeasurePreserving (eFrontN N) (volume : Measure (Params N)) volume :=
  volume_preserving_piFinSuccAbove
    (fun s : Fin (n + 1) => Fin (N s.castSucc) → Fin (N s.succ) → ℝ) 0

/-- The first component of `eFrontN N A` is the leading layer `A 0`. -/
theorem eFrontN_fst {n : ℕ} (N : Fin (n + 1 + 1) → ℕ) (A : Params N) :
    (eFrontN N A).1 = A 0 := rfl

/-- The `s`-th tail layer of `eFrontN N A` is `A s.succ`. -/
theorem eFrontN_snd_apply {n : ℕ} (N : Fin (n + 1 + 1) → ℕ) (A : Params N) (s : Fin n) :
    (eFrontN N A).2 s = A s.succ := rfl

/-- The tail component of `eFrontN N A` is `Atail N A`. -/
theorem eFrontN_snd_eq_Atail {n : ℕ} (N : Fin (n + 1 + 1) → ℕ) (A : Params N) :
    (eFrontN N A).2 = Atail N A := by
  funext s
  have eA : N ((s.succ : Fin (n + 1)).castSucc) = Mtail N (s.castSucc) := rfl
  have eB : N ((s.succ : Fin (n + 1)).succ) = Mtail N (s.succ) := rfl
  rw [eFrontN_snd_apply, Atail_apply N A s eA eB,
    show (finCongr eA) = Equiv.refl _ from finCongr_refl _,
    show (finCongr eB) = Equiv.refl _ from finCongr_refl _]
  erw [Matrix.reindex_refl_refl]

/-- **The box preimage** `eFrontN ⁻¹' (matBox N₀ N₁ 1 ×ˢ box(Mtail N)) = paramsBoxM N 1`. -/
theorem eFrontN_preimage_box {n : ℕ} (N : Fin (n + 1 + 1) → ℕ) :
    eFrontN N ⁻¹' (matBox (N 0) (N 1) 1 ×ˢ paramsBoxM (Mtail N) 1) = paramsBoxM N 1 := by
  ext A
  simp only [Set.mem_preimage, Set.mem_prod, matBox, paramsBoxM, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h0, htail⟩ s
    refine Fin.cases (fun i j => ?_) (fun s' i j => ?_) s
    · exact h0 i j
    · exact htail s' i j
  · intro h
    exact ⟨fun i j => h 0 i j, fun s' i j => h s'.succ i j⟩

/-- **The pre-factored front-peel integrand identity.** For a fixed pre-factor `F`, the front loss
`frobSq (F · prod N A)` peels the leading layer `A 0` and reassociates:
`= frobSq ((F · A₀) · prod (Mtail N) (tail A))`, in raw-product `rmatMul` form. -/
theorem frobSq_rmatMul_prod_front {n : ℕ} (N : Fin (n + 1 + 1) → ℕ) {p : ℕ}
    (F : Fin p → Fin (N 0) → ℝ) (A : Params N) :
    frobSq (rmatMul F (prod N A))
      = frobSq (rmatMul (rmatMul F ((eFrontN N A).1)) (prod (Mtail N) ((eFrontN N A).2))) := by
  have emid : Mtail N (0 : Fin (n + 1)) = N ((0 : Fin (n + 1)).succ) := rfl
  have ecol : Mtail N (Fin.last n) = N (Fin.last (n + 1)) := rfl
  rw [eFrontN_fst, eFrontN_snd_eq_Atail, prod_front_peel N A emid ecol,
    show (finCongr emid) = Equiv.refl _ from finCongr_refl _,
    show (finCongr ecol) = Equiv.refl _ from finCongr_refl _]
  erw [Matrix.reindex_refl_refl]
  congr 1
  exact rmatMul_mul_assoc F (A 0) (prod (Mtail N) (Atail N A))

/-- **Measurability of the pre-factored front-factor integrand.** -/
theorem measurable_frontFactorIntegrand {n : ℕ} (N : Fin (n + 1 + 1) → ℕ) {p : ℕ}
    (F : Fin p → Fin (N 0) → ℝ) (c' : ℝ) :
    Measurable (fun q : (Fin (N 0) → Fin (N 1) → ℝ) × Params (Mtail N) =>
      ENNReal.ofReal (frobSq (rmatMul (rmatMul F q.1) (prod (Mtail N) q.2)) ^ (-c'))) := by
  have hP : Continuous (fun q : (Fin (N 0) → Fin (N 1) → ℝ) × Params (Mtail N) =>
      prod (Mtail N) q.2) := (continuous_prod (Mtail N)).comp continuous_snd
  have hR : Continuous (fun q : (Fin (N 0) → Fin (N 1) → ℝ) × Params (Mtail N) =>
      rmatMul (rmatMul F q.1) (prod (Mtail N) q.2)) := by
    unfold rmatMul
    refine continuous_pi (fun i => continuous_pi (fun j => ?_))
    refine continuous_finset_sum _ (fun k _ => Continuous.mul ?_ (hP.matrix_elem k j))
    exact continuous_finset_sum _ (fun l _ =>
      (continuous_const).mul ((continuous_apply k).comp
        ((continuous_apply l).comp continuous_fst)))
  have hcont : Continuous (fun q : (Fin (N 0) → Fin (N 1) → ℝ) × Params (Mtail N) =>
      frobSq (rmatMul (rmatMul F q.1) (prod (Mtail N) q.2))) := by
    unfold frobSq
    exact continuous_finset_sum _ (fun i _ => continuous_finset_sum _
      (fun j _ => (hR.matrix_elem i j).pow 2))
  exact ENNReal.measurable_ofReal.comp
    (Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop) hcont.measurable)

/-- **The generic pre-factored front-factor split.** The `N`-box integral of `frobSq (F · prod N A)`
factors: the front layer `A₁` (radius-1 box, outer) recombines with `F` into `F · A₁`, the deep tail
`A''` (radius-1 box, inner). -/
theorem frontFactor_split {n : ℕ} (N : Fin (n + 1 + 1) → ℕ) {p : ℕ}
    (F : Fin p → Fin (N 0) → ℝ) (c' : ℝ) :
    (∫⁻ A in paramsBoxM N 1, ENNReal.ofReal (frobSq (rmatMul F (prod N A)) ^ (-c')))
      = ∫⁻ A₁ in matBox (N 0) (N 1) 1, ∫⁻ A'' in paramsBoxM (Mtail N) 1,
          ENNReal.ofReal (frobSq (rmatMul (rmatMul F A₁) (prod (Mtail N) A'')) ^ (-c')) := by
  have hmp := measurePreserving_eFrontN N
  have hpre := hmp.setLIntegral_comp_preimage_emb
    (MeasurableEquiv.measurableEmbedding (eFrontN N))
    (fun q : (Fin (N 0) → Fin (N 1) → ℝ) × Params (Mtail N) =>
      ENNReal.ofReal (frobSq (rmatMul (rmatMul F q.1) (prod (Mtail N) q.2)) ^ (-c')))
    (matBox (N 0) (N 1) 1 ×ˢ paramsBoxM (Mtail N) 1)
  calc (∫⁻ A in paramsBoxM N 1, ENNReal.ofReal (frobSq (rmatMul F (prod N A)) ^ (-c')))
      = ∫⁻ A in eFrontN N ⁻¹' (matBox (N 0) (N 1) 1 ×ˢ paramsBoxM (Mtail N) 1),
          ENNReal.ofReal (frobSq (rmatMul (rmatMul F ((eFrontN N A).1))
            (prod (Mtail N) ((eFrontN N A).2))) ^ (-c')) := by
        rw [eFrontN_preimage_box]
        refine setLIntegral_congr_fun (measurableSet_paramsBoxM N 1) (fun A _ => ?_)
        rw [frobSq_rmatMul_prod_front N F A]
    _ = ∫⁻ q in (matBox (N 0) (N 1) 1 ×ˢ paramsBoxM (Mtail N) 1),
          ENNReal.ofReal (frobSq (rmatMul (rmatMul F q.1) (prod (Mtail N) q.2)) ^ (-c')) := hpre
    _ = ∫⁻ A₁ in matBox (N 0) (N 1) 1, ∫⁻ A'' in paramsBoxM (Mtail N) 1,
          ENNReal.ofReal (frobSq (rmatMul (rmatMul F A₁) (prod (Mtail N) A'')) ^ (-c')) := by
        rw [Measure.volume_eq_prod]
        exact setLIntegral_prod _ (measurable_frontFactorIntegrand N F c').aemeasurable

/-- **The `a=0` WIDE BOUNDED arm of the front-collapse atom.** For a wide front (`M₀ ≤ M₁`) in the
bounded density regime (`M₂ < M₁ − M₀ + 1`), GIVEN the plain one-shorter strong IH `hIH`, below the
geometric threshold (`c' < ½·minAdm M`), the front-factor box integral over
`wingFrontBox M × paramsBoxM(tailChain M)` is finite. -/
theorem frontCollapse_wide_bounded_lt_top (M : Fin (L + 1 + 1 + 1) → ℕ)
    (hwide : M 0 ≤ M 1) (hbnd : (M 2 : ℝ) < (M 1 : ℝ) - M 0 + 1)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    (∫⁻ F in wingFrontBox M, ∫⁻ A' in paramsBoxM (tailChain M) 1,
        ENNReal.ofReal ((frobSq (rmatMul F (prod (tailChain M) A'))) ^ (-(c' : ℝ)))) < ⊤ := by
  classical
  -- the deep chain `D = (M₂, M₃, …, M_last)` and the deep-tail fibre integrand `g`.
  set D : Fin (L + 1) → ℕ := Mtail (tailChain M) with hDdef
  set g : (Fin (M 0) → Fin (M 2) → ℝ) → ℝ≥0∞ := fun W =>
      ∫⁻ A'' in paramsBoxM D 1,
        ENNReal.ofReal ((frobSq (rmatMul W (prod D A''))) ^ (-(c' : ℝ))) with hgdef
  -- the `F`-independent constant and the radius-`M₁` `W`-box integral.
  set C : ℝ≥0∞ := ENNReal.ofReal ((2 * (M 1 : ℝ)) ^ ((M 1 - M 0) * M 2)) with hCdef
  set K : ℝ≥0∞ := ∫⁻ W in matBox (M 0) (M 2) (M 1 : ℝ), g W with hKdef
  -- the `F`-dependent Gram-Jacobian integrand.
  have hdetcont : Continuous
      (fun F : Fin (M 0) → Fin (M 1) → ℝ => (Matrix.of F * (Matrix.of F)ᵀ).det) := by
    refine Continuous.matrix_det ?_
    exact continuous_matrix (fun i j => by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
      fun_prop)
  have hrpow : Measurable (fun t : ℝ => t ^ (-(M 2 : ℝ) / 2)) := by fun_prop
  have hDetMeas : Measurable
      (fun F : Fin (M 0) → Fin (M 1) → ℝ =>
        ENNReal.ofReal (((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-(M 2 : ℝ) / 2))) :=
    ENNReal.measurable_ofReal.comp (hrpow.comp hdetcont.measurable)
  -- (hg) measurability of the deep-tail fibre integrand (parametric lintegral, Tonelli).
  have hg : Measurable g := by
    have hcont : Continuous (fun p : (Fin (M 0) → Fin (M 2) → ℝ) × Params D =>
        frobSq (rmatMul p.1 (prod D p.2))) := by
      have hP : Continuous (fun p : (Fin (M 0) → Fin (M 2) → ℝ) × Params D => prod D p.2) :=
        (continuous_prod D).comp continuous_snd
      have hR : Continuous (fun p : (Fin (M 0) → Fin (M 2) → ℝ) × Params D =>
          rmatMul p.1 (prod D p.2)) := by
        unfold rmatMul
        refine continuous_pi (fun i => continuous_pi (fun j => ?_))
        refine continuous_finset_sum _ (fun k _ => Continuous.mul ?_ (hP.matrix_elem k j))
        exact (continuous_apply k).comp ((continuous_apply i).comp continuous_fst)
      unfold frobSq
      exact continuous_finset_sum _ (fun i _ => continuous_finset_sum _
        (fun j _ => (hR.matrix_elem i j).pow 2))
    have hf : Measurable (fun p : (Fin (M 0) → Fin (M 2) → ℝ) × Params D =>
        ENNReal.ofReal ((frobSq (rmatMul p.1 (prod D p.2))) ^ (-(c' : ℝ)))) :=
      ENNReal.measurable_ofReal.comp
        (Measurable.comp (g := fun t : ℝ => t ^ (-(c' : ℝ))) (by fun_prop) hcont.measurable)
    rw [hgdef]
    exact hf.lintegral_prod_right'
  -- (hsplit) the fixed-`F` fibre split (front-peel `A₁ = A' 0` + Tonelli).
  have hsplit : ∀ F : Fin (M 0) → Fin (M 1) → ℝ,
      (∫⁻ A' in paramsBoxM (tailChain M) 1,
        ENNReal.ofReal ((frobSq (rmatMul F (prod (tailChain M) A'))) ^ (-(c' : ℝ))))
      = ∫⁻ A₁ in matBox (M 1) (M 2) 1, g (rmatMul F A₁) := by
    intro F
    refine (frontFactor_split (tailChain M) F (c' : ℝ)).trans ?_
    rw [hgdef]
    rfl
  -- (hKfin) the radius-`M₁` reduced-chain box is finite.
  -- (a) the radius-1 `W`-box integral IS the reduced-chain box, finite via the plain IH.
  have hK1eq : (∫⁻ W in matBox (M 0) (M 2) 1, g W)
      = routeMLayerBoxIntegral (redChain (M 0) M) (c' : ℝ) 1 := by
    have key := frontFactor_split (redChain (M 0) M)
      (1 : Matrix (Fin (redChain (M 0) M 0)) (Fin (redChain (M 0) M 0)) ℝ) (c' : ℝ)
    simp only [rmatMul_one_left] at key
    rw [routeMLayerBoxIntegral, hgdef]
    exact key.symm
  have hK1 : (∫⁻ W in matBox (M 0) (M 2) 1, g W) < ⊤ := by
    rw [hK1eq]
    have hred := redChain_box_lt_top M hIH c' hc'
    rwa [min_eq_left hwide] at hred
  have hKfin : K < ⊤ := by
    rw [hKdef]
    rcases Nat.eq_zero_or_pos (M 1) with hM1 | hM1
    · -- M₁ = 0 ⟹ M₀ = 0 (wide): the front has no rows, `frobSq` is `0`, integrand constant.
      have hM00 : M 0 = 0 := Nat.le_zero.mp (hwide.trans_eq hM1)
      haveI : IsEmpty (Fin (M 0)) := by rw [hM00]; infer_instance
      have hzero : ∀ W : Fin (M 0) → Fin (M 2) → ℝ,
          g W = ENNReal.ofReal ((0 : ℝ) ^ (-(c' : ℝ))) * volume (paramsBoxM D 1) := by
        intro W
        rw [hgdef]
        have hfz : ∀ A'' : Params D, frobSq (rmatMul W (prod D A'')) = 0 := by
          intro A''; simp [frobSq, Finset.univ_eq_empty]
        simp only [hfz]
        rw [setLIntegral_const]
      simp only [hzero, setLIntegral_const]
      exact ENNReal.mul_lt_top
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (paramsBoxM_volume_lt_top D 1))
        (volume_matBox_lt_top _ _ _)
    · -- M₁ > 0: the reduced-chain box at radius `M₁` is a scaling of the radius-1 box.
      set r : ℝ := (M 1 : ℝ) with hrdef
      have hrpos : 0 < r := by rw [hrdef]; exact_mod_cast hM1
      set G : Matrix (Fin (M 0)) (Fin (M 0)) ℝ := r • 1 with hGdef
      have hGdet : G.det ≠ 0 := by
        rw [hGdef, Matrix.det_smul, Matrix.det_one, mul_one]
        exact pow_ne_zero _ (ne_of_gt hrpos)
      -- `G`-left-multiplication is scalar multiplication by `r`.
      have hGmul : ∀ A : Fin (M 0) → Fin (M 2) → ℝ,
          (fun i j => ∑ k, G i k * A k j) = r • A := by
        intro A; funext i j
        have h1 : ∑ k, (1 : Matrix (Fin (M 0)) (Fin (M 0)) ℝ) i k * A k j = A i j :=
          congrFun (congrFun (rmatMul_one_left A) i) j
        calc ∑ k, G i k * A k j
            = ∑ k, r * ((1 : Matrix (Fin (M 0)) (Fin (M 0)) ℝ) i k * A k j) := by
              refine Finset.sum_congr rfl (fun k _ => ?_)
              rw [hGdef]; simp only [Matrix.smul_apply, smul_eq_mul]; ring
          _ = r * ∑ k, (1 : Matrix (Fin (M 0)) (Fin (M 0)) ℝ) i k * A k j :=
              (Finset.mul_sum _ _ _).symm
          _ = r * A i j := by rw [h1]
          _ = (r • A) i j := by simp [Pi.smul_apply]
      -- `g` is degree-`(−2c')` homogeneous.
      have hhom : ∀ A : Fin (M 0) → Fin (M 2) → ℝ,
          g (r • A) = ENNReal.ofReal ((r ^ 2) ^ (-(c' : ℝ))) * g A := by
        intro A
        simp only [hgdef]
        rw [← lintegral_const_mul' (ENNReal.ofReal ((r ^ 2) ^ (-(c' : ℝ)))) _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun A'' => ?_
        rw [frobSq_rmatMul_smul r A (prod D A''), Real.mul_rpow (by positivity) (frobSq_nonneg _),
          ENNReal.ofReal_mul (by positivity)]
      -- the box-membership equivalence under scaling.
      have hmem : ∀ A : Fin (M 0) → Fin (M 2) → ℝ,
          ((r • A) ∈ matBox (M 0) (M 2) r) ↔ (A ∈ matBox (M 0) (M 2) 1) := by
        intro A
        simp only [matBox, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, Set.mem_Icc]
        constructor
        · intro h i k; obtain ⟨h1, h2⟩ := h i k; constructor <;> nlinarith [hrpos]
        · intro h i k; obtain ⟨h1, h2⟩ := h i k; constructor <;> nlinarith [hrpos]
      -- the change of variables `W = r • A`.
      have hcov := lintegral_comp_rmatMulLeft G hGdet ((matBox (M 0) (M 2) r).indicator g)
        (hg.indicator (matBox_measurableSet (M 0) (M 2) r))
      simp only [hGmul] at hcov
      have hR : (∫⁻ B, (matBox (M 0) (M 2) r).indicator g B)
          = ∫⁻ W in matBox (M 0) (M 2) r, g W :=
        lintegral_indicator (matBox_measurableSet (M 0) (M 2) r) g
      have hL : (∫⁻ A, (matBox (M 0) (M 2) r).indicator g (r • A))
          = ENNReal.ofReal ((r ^ 2) ^ (-(c' : ℝ))) * ∫⁻ W in matBox (M 0) (M 2) 1, g W := by
        have hpt : ∀ A : Fin (M 0) → Fin (M 2) → ℝ,
            (matBox (M 0) (M 2) r).indicator g (r • A)
              = (matBox (M 0) (M 2) 1).indicator
                  (fun A => ENNReal.ofReal ((r ^ 2) ^ (-(c' : ℝ))) * g A) A := by
          intro A
          by_cases hA : A ∈ matBox (M 0) (M 2) 1
          · rw [Set.indicator_of_mem ((hmem A).mpr hA), Set.indicator_of_mem hA, hhom A]
          · rw [Set.indicator_of_notMem (fun hc => hA ((hmem A).mp hc)),
              Set.indicator_of_notMem hA]
        simp only [hpt]
        rw [lintegral_indicator (matBox_measurableSet (M 0) (M 2) 1),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have hcancel : ENNReal.ofReal (|G.det| ^ (M 2))
          * ENNReal.ofReal ((|G.det| ^ (M 2))⁻¹) = 1 := by
        rw [← ENNReal.ofReal_mul (by positivity),
          mul_inv_cancel₀ (pow_ne_zero _ (abs_ne_zero.mpr hGdet)), ENNReal.ofReal_one]
      have hKval : (∫⁻ B, (matBox (M 0) (M 2) r).indicator g B)
          = ENNReal.ofReal (|G.det| ^ (M 2))
            * (∫⁻ A, (matBox (M 0) (M 2) r).indicator g (r • A)) := by
        rw [hcov, ← mul_assoc, hcancel, one_mul]
      rw [← hR, hKval, hL]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK1)
  -- (hdet) the front Gram is nonsingular on `wingFrontBox`.
  have hdet : ∀ F ∈ wingFrontBox M, (Matrix.of F * (Matrix.of F)ᵀ).det ≠ 0 := by
    intro F hF
    set rowF : Fin (M 0) → EuclideanSpace ℝ (Fin (M 1)) := fun i => WithLp.toLp 2 (F i) with hrowF
    have hgram : Matrix.gram ℝ rowF = Matrix.of F * (Matrix.of F)ᵀ := by
      ext i j
      simp only [hrowF, Matrix.gram_apply, PiLp.inner_apply, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.of_apply]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    -- the rows of `F` are linearly independent (first `M₀` coords = the unit leading block).
    have hli : LinearIndependent ℝ rowF := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hcoord : ∀ j : Fin (M 1), ∑ i, c i * F i j = 0 := by
        intro j
        have h0 : (∑ i, c i • rowF i) j = (0 : EuclideanSpace ℝ (Fin (M 1))) j := by rw [hc]
        simpa [hrowF, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h0
      set e : Fin (M 0) ≃ Fin (min (M 0) (M 1)) := (finCongr (min_eq_left hwide)).symm with he
      have hBunit : IsUnit ((leadingBlock M F).submatrix e e) :=
        (Matrix.isUnit_submatrix_equiv e e).mpr hF.2
      have hcb : c ᵥ* ((leadingBlock M F).submatrix e e) = 0 := by
        funext j
        have hj := hcoord (Fin.castLE (min_le_right (M 0) (M 1)) (e j))
        simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, leadingBlock, Matrix.of_apply,
          Pi.zero_apply]
        exact hj
      have hc0 : c = 0 :=
        (Matrix.vecMul_injective_iff_isUnit.mpr hBunit) (hcb.trans (Matrix.zero_vecMul _).symm)
      exact fun i => congrFun hc0 i
    have hpd : (Matrix.gram ℝ rowF).PosDef := Matrix.posDef_gram_iff_linearIndependent.mpr hli
    rw [← hgram]
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      ((Matrix.posSemidef_gram ℝ rowF).posDef_iff_isUnit.mp hpd))
  -- STEP 4 + 8: the pointwise `fixedF` bound, monotone over `F`, then pull the constant out.
  have hmono : (∫⁻ F in wingFrontBox M, ∫⁻ A' in paramsBoxM (tailChain M) 1,
        ENNReal.ofReal ((frobSq (rmatMul F (prod (tailChain M) A'))) ^ (-(c' : ℝ))))
      ≤ (C * K) * ∫⁻ F in matBox (M 0) (M 1) 1,
          ENNReal.ofReal (((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-(M 2 : ℝ) / 2)) := by
    calc (∫⁻ F in wingFrontBox M, ∫⁻ A' in paramsBoxM (tailChain M) 1,
            ENNReal.ofReal ((frobSq (rmatMul F (prod (tailChain M) A'))) ^ (-(c' : ℝ))))
        = ∫⁻ F in wingFrontBox M, ∫⁻ A₁ in matBox (M 1) (M 2) 1, g (rmatMul F A₁) := by
          refine setLIntegral_congr_fun (measurableSet_wingFrontBox M) (fun F _ => ?_)
          exact hsplit F
      _ ≤ ∫⁻ F in wingFrontBox M,
            ENNReal.ofReal (((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-(M 2 : ℝ) / 2)) * (C * K) := by
          refine setLIntegral_mono (hDetMeas.mul measurable_const) ?_
          · intro F hF
            have hb := fixedF_wide_cov_bound (m := M 0) (n := M 1) (p := M 2) hwide F hF.1
              (hdet F hF) g hg
            calc ∫⁻ A₁ in matBox (M 1) (M 2) 1, g (rmatMul F A₁)
                ≤ ENNReal.ofReal (((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-(M 2 : ℝ) / 2))
                    * (ENNReal.ofReal ((2 * (M 1 : ℝ)) ^ ((M 1 - M 0) * M 2))
                        * ∫⁻ W in matBox (M 0) (M 2) (M 1 : ℝ), g W) := hb
              _ = ENNReal.ofReal (((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-(M 2 : ℝ) / 2))
                    * (C * K) := by rw [hCdef, hKdef]
      _ = (C * K) * ∫⁻ F in wingFrontBox M,
            ENNReal.ofReal (((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-(M 2 : ℝ) / 2)) := by
          rw [← lintegral_const_mul' (C * K) _ (ENNReal.mul_ne_top
            (by rw [hCdef]; exact ENNReal.ofReal_ne_top) hKfin.ne)]
          refine lintegral_congr fun F => ?_
          rw [mul_comm]
      _ ≤ (C * K) * ∫⁻ F in matBox (M 0) (M 1) 1,
            ENNReal.ofReal (((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-(M 2 : ℝ) / 2)) := by
          exact mul_le_mul' (le_refl (C * K)) (lintegral_mono_set (fun F hF => hF.1))
  refine lt_of_le_of_lt hmono ?_
  refine ENNReal.mul_lt_top ?_ ?_
  · refine ENNReal.mul_lt_top ?_ hKfin
    rw [hCdef]; exact ENNReal.ofReal_lt_top
  · exact front_gram_qbox_lt_top (M 2) hwide hbnd

end DLNFibre.DLN.RLCT
