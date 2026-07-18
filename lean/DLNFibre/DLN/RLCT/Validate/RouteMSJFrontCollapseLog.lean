import DLNFibre.DLN.RLCT.Validate.RouteMSJFrontCollapseWide
import Mathlib.MeasureTheory.Integral.MeanInequalities

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJFrontCollapseLog` — the `a=0` WIDE LOG arm (critical density)

**Thread `genm-log` (Lane-1 front-collapse, the LOG cell of `frontCollapseRankSector`).** The
critical-density cell `M₂ = M₁ − M₀ + 1` of the wide wing (`M₀ ≤ M₁`, slack `s = M₁ − M₀`,
`M₂ = s + 1`): the front-factor box integral over `wingFrontBox M × paramsBoxM(tailChain M)` is finite
below the geometric threshold `c' < ½·minAdm M`.

At `M₂ = M₁ − M₀ + 1` the naive Gram-Schmidt density factor DIVERGES — the free-`F` front-Gram
`∫ det(F·Fᵀ)^{−M₂/2}` sits exactly at its convergence boundary (`M₂ = M₁ − M₀ + 1`, not `<`). The route
here is a **Hölder exponent-trade** (NOT a δ-fold, which also diverges): fix `F`, pick a Hölder exponent
`s > 1` with `s·c' < ½·minAdm(redChain M₀ M)` (room from `saturated_threshold`, since
`c' < ½·minAdm(redChain M₀ M)`), and

1. Hölder on the finite box `Ω = paramsBoxM(tailChain M) 1` with `g ≡ 1`:
   `J_{c'}(F) ≤ (J_{sc'}(F))^{1/s} · vol(Ω)^{1/s'}` (`ENNReal.lintegral_mul_le_Lp_mul_Lq`);
2. the exponent-agnostic absorption CoV at `sc'` (`fixedF_wide_cov_bound`, packaged as
   `wide_fixedF_absorb`): `J_{sc'}(F) ≤ det(F·Fᵀ)^{−M₂/2} · Ke`, `Ke < ⊤` by the IH at `sc'`;
3. take `(·)^{1/s}`: `J_{c'}(F) ≤ det(F·Fᵀ)^{−M₂/(2s)} · const`;
4. integrate over `F`: converges by the REAL-exponent qbox at `a = M₂/s = (s+1)/s < s+1 = M₁ − M₀ + 1`
   (strict since `s > 1`) — `front_gram_qbox_real_lt_top`.

This reaches the FULL threshold `c' < ½·minAdm M` at the LOG density.

**Scope: WIDE (`a=0`) wing only.** The TALL (`b=0`) LOG cell is the transpose mirror; it needs a tall
absorption CoV (`fixedF_tall_cov_bound`, the `P = C·√(FᵀF)` square-replacement route), which is NOT yet
banked — see the mirror note at the foot of this file. `front_gram_qbox_tall_lt_top` (the tall density
factor) IS banked, so the tall-LOG lands once the tall absorption is built.

S2-FREE: pure measure theory + the banked bricks. Intended axiom footprint
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal BigOperators Matrix

variable {L : ℕ}

/-! ## The real-exponent front-Gram qbox finiteness -/

/-- **The front-Gram qbox finiteness at a REAL exponent** (the `M₂ : ℕ` version
`front_gram_qbox_lt_top` restated with a real density `a`). The free-`F` front Gram integral
`∫_{F ∈ box} det(F·Fᵀ)^{−a/2}` is finite whenever `M₀ ≤ M₁` and `a < M₁ − M₀ + 1`. Trivial
restatement — the backing `CorankSlabD.bRowGram_colBall_lt_top` is already `{a : ℝ}`. -/
theorem front_gram_qbox_real_lt_top {M₀ M₁ : ℕ} (a : ℝ) (hle : M₀ ≤ M₁)
    (hbnd : a < (M₁ : ℝ) - M₀ + 1) :
    (∫⁻ F in matBox M₀ M₁ 1,
        ENNReal.ofReal ((Matrix.of F * (Matrix.of F)ᵀ).det ^ (-a / 2))) < ⊤ :=
  lt_of_le_of_lt (lintegral_mono_set CorankSlabD.box_subset_colBall)
    (CorankSlabD.bRowGram_colBall_lt_top (n := M₀) hle (a := a) hbnd)

/-! ## The fixed-`F` wide absorption at a general real exponent -/

/-- **The fixed-`F` wide absorption bound at a general real exponent `e`.** For a wide front
(`M₀ ≤ M₁`), GIVEN the plain one-shorter IH `hIH`, whenever `0 ≤ e < ½·minAdm(redChain M₀ M)`, there is
an `F`-independent finite constant `Ke` such that for every `F ∈ wingFrontBox M`, the fixed-`F` tail box
integral `J_e(F) = ∫_{A'} frobSq(F · prod(tailChain M) A')^{−e}` is bounded by the free-`F` Gram
Jacobian `det(F·Fᵀ)^{−M₂/2}` times `Ke`. The exponent-agnostic core the LOG cell trades on: the density
exponent `M₂/2` is purely geometric (independent of `e`); only `Ke` (the reduced-chain box, closed by
`hIH` at `e`) carries `e`. This is the fixed-`F` half of `frontCollapse_wide_bounded_lt_top`, lifted to a
general real exponent. -/
theorem wide_fixedF_absorb (M : Fin (L + 1 + 1 + 1) → ℕ) (hwide : M 0 ≤ M 1)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (e : ℝ) (he0 : 0 ≤ e)
    (hered : e < (minAdm (redChain (M 0) M) : ℝ) / 2) :
    ∃ Ke : ℝ≥0∞, Ke < ⊤ ∧ ∀ F ∈ wingFrontBox M,
      (∫⁻ A' in paramsBoxM (tailChain M) 1,
          ENNReal.ofReal ((frobSq (rmatMul F (prod (tailChain M) A'))) ^ (-e)))
        ≤ ENNReal.ofReal (((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-(M 2 : ℝ) / 2)) * Ke := by
  classical
  -- the deep chain `D = (M₂, M₃, …, M_last)` and the deep-tail fibre integrand `g` (exponent `e`).
  set D : Fin (L + 1) → ℕ := Mtail (tailChain M) with hDdef
  set g : (Fin (M 0) → Fin (M 2) → ℝ) → ℝ≥0∞ := fun W =>
      ∫⁻ A'' in paramsBoxM D 1,
        ENNReal.ofReal ((frobSq (rmatMul W (prod D A''))) ^ (-e)) with hgdef
  set C : ℝ≥0∞ := ENNReal.ofReal ((2 * (M 1 : ℝ)) ^ ((M 1 - M 0) * M 2)) with hCdef
  set K : ℝ≥0∞ := ∫⁻ W in matBox (M 0) (M 2) (M 1 : ℝ), g W with hKdef
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
        ENNReal.ofReal ((frobSq (rmatMul p.1 (prod D p.2))) ^ (-e))) :=
      ENNReal.measurable_ofReal.comp
        (Measurable.comp (g := fun t : ℝ => t ^ (-e)) (by fun_prop) hcont.measurable)
    rw [hgdef]
    exact hf.lintegral_prod_right'
  -- (hsplit) the fixed-`F` fibre split (front-peel `A₁ = A' 0` + Tonelli).
  have hsplit : ∀ F : Fin (M 0) → Fin (M 1) → ℝ,
      (∫⁻ A' in paramsBoxM (tailChain M) 1,
        ENNReal.ofReal ((frobSq (rmatMul F (prod (tailChain M) A'))) ^ (-e)))
      = ∫⁻ A₁ in matBox (M 1) (M 2) 1, g (rmatMul F A₁) := by
    intro F
    refine (frontFactor_split (tailChain M) F e).trans ?_
    rw [hgdef]
    rfl
  -- (hK1eq) the radius-1 `W`-box integral IS the reduced-chain box.
  have hK1eq : (∫⁻ W in matBox (M 0) (M 2) 1, g W)
      = routeMLayerBoxIntegral (redChain (M 0) M) e 1 := by
    have key := frontFactor_split (redChain (M 0) M)
      (1 : Matrix (Fin (redChain (M 0) M 0)) (Fin (redChain (M 0) M 0)) ℝ) e
    simp only [rmatMul_one_left] at key
    rw [routeMLayerBoxIntegral, hgdef]
    exact key.symm
  -- (hK1) finite via the plain IH at exponent `e`.
  have hK1 : (∫⁻ W in matBox (M 0) (M 2) 1, g W) < ⊤ := by
    rw [hK1eq]
    have hcond : ((e.toNNReal : ℝ)) < (minAdm (redChain (M 0) M) : ℝ) / 2 := by
      rw [Real.coe_toNNReal e he0]; exact hered
    have h := hIH (redChain (M 0) M) e.toNNReal hcond
    rwa [Real.coe_toNNReal e he0] at h
  -- (hKfin) the radius-`M₁` reduced-chain box is finite (scaling from radius 1).
  have hKfin : K < ⊤ := by
    rw [hKdef]
    rcases Nat.eq_zero_or_pos (M 1) with hM1 | hM1
    · -- M₁ = 0 ⟹ M₀ = 0 (wide): the front has no rows, `frobSq` is `0`, integrand constant.
      have hM00 : M 0 = 0 := Nat.le_zero.mp (hwide.trans_eq hM1)
      haveI : IsEmpty (Fin (M 0)) := by rw [hM00]; infer_instance
      have hzero : ∀ W : Fin (M 0) → Fin (M 2) → ℝ,
          g W = ENNReal.ofReal ((0 : ℝ) ^ (-e)) * volume (paramsBoxM D 1) := by
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
      have hhom : ∀ A : Fin (M 0) → Fin (M 2) → ℝ,
          g (r • A) = ENNReal.ofReal ((r ^ 2) ^ (-e)) * g A := by
        intro A
        simp only [hgdef]
        rw [← lintegral_const_mul' (ENNReal.ofReal ((r ^ 2) ^ (-e))) _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun A'' => ?_
        rw [frobSq_rmatMul_smul r A (prod D A''), Real.mul_rpow (by positivity) (frobSq_nonneg _),
          ENNReal.ofReal_mul (by positivity)]
      have hmem : ∀ A : Fin (M 0) → Fin (M 2) → ℝ,
          ((r • A) ∈ matBox (M 0) (M 2) r) ↔ (A ∈ matBox (M 0) (M 2) 1) := by
        intro A
        simp only [matBox, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, Set.mem_Icc]
        constructor
        · intro h i k; obtain ⟨h1, h2⟩ := h i k; constructor <;> nlinarith [hrpos]
        · intro h i k; obtain ⟨h1, h2⟩ := h i k; constructor <;> nlinarith [hrpos]
      have hcov := lintegral_comp_rmatMulLeft G hGdet ((matBox (M 0) (M 2) r).indicator g)
        (hg.indicator (matBox_measurableSet (M 0) (M 2) r))
      simp only [hGmul] at hcov
      have hR : (∫⁻ B, (matBox (M 0) (M 2) r).indicator g B)
          = ∫⁻ W in matBox (M 0) (M 2) r, g W :=
        lintegral_indicator (matBox_measurableSet (M 0) (M 2) r) g
      have hL : (∫⁻ A, (matBox (M 0) (M 2) r).indicator g (r • A))
          = ENNReal.ofReal ((r ^ 2) ^ (-e)) * ∫⁻ W in matBox (M 0) (M 2) 1, g W := by
        have hpt : ∀ A : Fin (M 0) → Fin (M 2) → ℝ,
            (matBox (M 0) (M 2) r).indicator g (r • A)
              = (matBox (M 0) (M 2) 1).indicator
                  (fun A => ENNReal.ofReal ((r ^ 2) ^ (-e)) * g A) A := by
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
    have hli : LinearIndependent ℝ rowF := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hcoord : ∀ j : Fin (M 1), ∑ i, c i * F i j = 0 := by
        intro j
        have h0 : (∑ i, c i • rowF i) j = (0 : EuclideanSpace ℝ (Fin (M 1))) j := by rw [hc]
        simpa [hrowF, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h0
      set ee : Fin (M 0) ≃ Fin (min (M 0) (M 1)) := (finCongr (min_eq_left hwide)).symm with hee
      have hBunit : IsUnit ((leadingBlock M F).submatrix ee ee) :=
        (Matrix.isUnit_submatrix_equiv ee ee).mpr hF.2
      have hcb : c ᵥ* ((leadingBlock M F).submatrix ee ee) = 0 := by
        funext j
        have hj := hcoord (Fin.castLE (min_le_right (M 0) (M 1)) (ee j))
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
  -- assemble: Ke = C * K, finite, with the fixed-`F` bound via `fixedF_wide_cov_bound`.
  refine ⟨C * K, ENNReal.mul_lt_top (by rw [hCdef]; exact ENNReal.ofReal_lt_top) hKfin, ?_⟩
  intro F hF
  rw [hsplit F]
  have hb := fixedF_wide_cov_bound (m := M 0) (n := M 1) (p := M 2) hwide F hF.1 (hdet F hF) g hg
  calc ∫⁻ A₁ in matBox (M 1) (M 2) 1, g (rmatMul F A₁)
      ≤ ENNReal.ofReal (((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-(M 2 : ℝ) / 2))
          * (ENNReal.ofReal ((2 * (M 1 : ℝ)) ^ ((M 1 - M 0) * M 2))
              * ∫⁻ W in matBox (M 0) (M 2) (M 1 : ℝ), g W) := hb
    _ = ENNReal.ofReal (((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-(M 2 : ℝ) / 2)) * (C * K) := by
        rw [hCdef, hKdef]

/-! ## The `a=0` WIDE LOG cell -/

/-- **The `a=0` WIDE LOG arm of the front-collapse atom (critical density `M₂ = M₁ − M₀ + 1`).** For a
wide front (`M₀ ≤ M₁`) at the LOG density (`(M₂ : ℝ) = M₁ − M₀ + 1`), GIVEN the plain one-shorter strong
IH `hIH`, below the geometric threshold (`c' < ½·minAdm M`), the front-factor box integral over
`wingFrontBox M × paramsBoxM(tailChain M)` is finite. Proved by the Hölder exponent-trade (§ file
docstring). -/
theorem frontCollapse_wide_log_lt_top (M : Fin (L + 1 + 1 + 1) → ℕ)
    (hwide : M 0 ≤ M 1) (hlog : (M 2 : ℝ) = (M 1 : ℝ) - M 0 + 1)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    (∫⁻ F in wingFrontBox M, ∫⁻ A' in paramsBoxM (tailChain M) 1,
        ENNReal.ofReal ((frobSq (rmatMul F (prod (tailChain M) A'))) ^ (-(c' : ℝ)))) < ⊤ := by
  classical
  -- the entry-box enclosure of `wingFrontBox` (both branches use it).
  have hwFsub : wingFrontBox M ⊆ matBox (M 0) (M 1) 1 := fun F hF i k => hF.1 i k
  have hwFvol : volume (wingFrontBox M) < ⊤ :=
    lt_of_le_of_lt (measure_mono hwFsub) (volume_matBox_lt_top _ _ _)
  -- the front Gram determinant is nonnegative (Gram of the rows).
  have hdet_nonneg : ∀ F : Fin (M 0) → Fin (M 1) → ℝ,
      0 ≤ (Matrix.of F * (Matrix.of F)ᵀ).det := by
    intro F
    have h := Matrix.posSemidef_self_mul_conjTranspose (Matrix.of F)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h.det_nonneg
  rcases eq_or_lt_of_le c'.coe_nonneg with hc0 | hc0
  · -- `c' = 0`: integrand `≡ 1`, both boxes finite.
    have hgoal : (∫⁻ F in wingFrontBox M, ∫⁻ A' in paramsBoxM (tailChain M) 1,
          ENNReal.ofReal ((frobSq (rmatMul F (prod (tailChain M) A'))) ^ (-(c' : ℝ))))
        = ∫⁻ _F in wingFrontBox M, volume (paramsBoxM (tailChain M) 1) := by
      refine lintegral_congr fun F => ?_
      rw [← hc0]
      simp only [neg_zero, Real.rpow_zero, ENNReal.ofReal_one]
      exact setLIntegral_one _
    rw [hgoal, setLIntegral_const]
    exact ENNReal.mul_lt_top (paramsBoxM_volume_lt_top (tailChain M) 1) hwFvol
  · -- `0 < c'`: the Hölder exponent-trade.
    -- the reduced threshold `T` and the room from `saturated_threshold`.
    have hc'T : (c' : ℝ) < (minAdm (redChain (M 0) M) : ℝ) / 2 := by
      have h := saturated_threshold M c' hc'
      rwa [min_eq_left hwide] at h
    set T : ℝ := (minAdm (redChain (M 0) M) : ℝ) / 2 with hTdef
    have hc0pos : 0 < (c' : ℝ) := hc0
    have hTpos : 0 < T := lt_trans hc0pos hc'T
    -- the Hölder exponent `s ∈ (1, T/c')`.
    set s : ℝ := (1 + T / (c' : ℝ)) / 2 with hsdef
    have hTc0div : 1 < T / (c' : ℝ) := (one_lt_div hc0pos).mpr hc'T
    have hs1 : 1 < s := by rw [hsdef]; linarith
    have hs0 : (0 : ℝ) < s := lt_trans one_pos hs1
    have hval : s * (c' : ℝ) = ((c' : ℝ) + T) / 2 := by rw [hsdef]; field_simp
    have hsc : s * (c' : ℝ) < T := by rw [hval]; linarith
    -- the traded loss exponent `e = s·c'`, below the reduced threshold.
    set e : ℝ := s * (c' : ℝ) with hedef
    have he0 : 0 ≤ e := by rw [hedef]; exact le_of_lt (mul_pos hs0 hc0pos)
    have hered : e < (minAdm (redChain (M 0) M) : ℝ) / 2 := by rw [← hTdef]; exact hsc
    -- the traded density exponent `a = M₂/s < M₁ − M₀ + 1`.
    have hM01 : (M 0 : ℝ) ≤ (M 1 : ℝ) := by exact_mod_cast hwide
    have hM2pos : 0 < (M 2 : ℝ) := by rw [hlog]; linarith
    set a : ℝ := (M 2 : ℝ) / s with hadef
    have hbnd_a : a < (M 1 : ℝ) - (M 0 : ℝ) + 1 := by rw [← hlog]; exact div_lt_self hM2pos hs1
    -- the fixed-`F` absorption at `e` and the conjugate exponent.
    obtain ⟨Ke, hKe, habsorb⟩ := wide_fixedF_absorb M hwide hIH e he0 hered
    set sconj : ℝ := Real.conjExponent s with hsconjdef
    have hpq : Real.HolderConjugate s sconj := Real.HolderConjugate.conjExponent hs1
    have h1s : (0 : ℝ) ≤ 1 / s := le_of_lt (one_div_pos.mpr hs0)
    have h1sc : (0 : ℝ) ≤ 1 / sconj := le_of_lt (one_div_pos.mpr hpq.symm.pos)
    -- the `F`-independent constant.
    set Cconst : ℝ≥0∞ := Ke ^ (1 / s) * (volume (paramsBoxM (tailChain M) 1)) ^ (1 / sconj)
      with hCconstdef
    have hCconst : Cconst < ⊤ := by
      rw [hCconstdef]
      exact ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg h1s hKe.ne)
        (ENNReal.rpow_lt_top_of_nonneg h1sc (paramsBoxM_volume_lt_top (tailChain M) 1).ne)
    -- the density integrand measurability.
    have hDetMeas' : Measurable (fun F : Fin (M 0) → Fin (M 1) → ℝ =>
        ENNReal.ofReal (((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-a / 2))) := by
      have hdetcont : Continuous
          (fun F : Fin (M 0) → Fin (M 1) → ℝ => (Matrix.of F * (Matrix.of F)ᵀ).det) := by
        refine Continuous.matrix_det ?_
        exact continuous_matrix (fun i j => by
          simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
          fun_prop)
      exact ENNReal.measurable_ofReal.comp
        ((by fun_prop : Measurable (fun t : ℝ => t ^ (-a / 2))).comp hdetcont.measurable)
    -- the pointwise-in-`F` bound (Hölder + absorb).
    have hpoint : ∀ F ∈ wingFrontBox M,
        (∫⁻ A' in paramsBoxM (tailChain M) 1,
            ENNReal.ofReal (frobSq (rmatMul F (prod (tailChain M) A')) ^ (-(c' : ℝ))))
          ≤ ENNReal.ofReal (((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-a / 2)) * Cconst := by
      intro F hF
      -- measurability of the fixed-`F` loss integrand.
      have hf_meas : Measurable (fun A' : Params (tailChain M) =>
          ENNReal.ofReal (frobSq (rmatMul F (prod (tailChain M) A')) ^ (-(c' : ℝ)))) := by
        have hP : Continuous (fun A' : Params (tailChain M) => prod (tailChain M) A') :=
          continuous_prod (tailChain M)
        have hR : Continuous (fun A' : Params (tailChain M) =>
            rmatMul F (prod (tailChain M) A')) := by
          unfold rmatMul
          refine continuous_pi (fun i => continuous_pi (fun j => ?_))
          exact continuous_finset_sum _ (fun k _ => (continuous_const).mul (hP.matrix_elem k j))
        have hfrob : Continuous (fun A' : Params (tailChain M) =>
            frobSq (rmatMul F (prod (tailChain M) A'))) := by
          unfold frobSq
          exact continuous_finset_sum _ (fun i _ => continuous_finset_sum _
            (fun j _ => (hR.matrix_elem i j).pow 2))
        exact ENNReal.measurable_ofReal.comp
          (Measurable.comp (g := fun t : ℝ => t ^ (-(c' : ℝ))) (by fun_prop) hfrob.measurable)
      -- pointwise `(f A')^s = ofReal(frobSq^{-e})`.
      have hpt : ∀ A' : Params (tailChain M),
          (ENNReal.ofReal (frobSq (rmatMul F (prod (tailChain M) A')) ^ (-(c' : ℝ)))) ^ s
            = ENNReal.ofReal (frobSq (rmatMul F (prod (tailChain M) A')) ^ (-e)) := by
        intro A'
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (frobSq_nonneg _) _) hs0.le]
        congr 1
        rw [← Real.rpow_mul (frobSq_nonneg _)]
        congr 1
        rw [hedef]; ring
      -- the density power identity `(ofReal det^{-M₂/2})^{1/s} = ofReal det^{-a/2}`.
      have hdetpow : (ENNReal.ofReal (((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-(M 2 : ℝ) / 2))) ^ (1 / s)
          = ENNReal.ofReal (((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-a / 2)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hdet_nonneg F) _) h1s]
        congr 1
        rw [← Real.rpow_mul (hdet_nonneg F)]
        congr 1
        rw [hadef]; ring
      -- Hölder on the finite box `Ω`.
      have hhold : (∫⁻ A' in paramsBoxM (tailChain M) 1,
            ENNReal.ofReal (frobSq (rmatMul F (prod (tailChain M) A')) ^ (-(c' : ℝ))))
          ≤ (∫⁻ A' in paramsBoxM (tailChain M) 1,
              ENNReal.ofReal (frobSq (rmatMul F (prod (tailChain M) A')) ^ (-e))) ^ (1 / s)
            * (volume (paramsBoxM (tailChain M) 1)) ^ (1 / sconj) := by
        calc (∫⁻ A' in paramsBoxM (tailChain M) 1,
                ENNReal.ofReal (frobSq (rmatMul F (prod (tailChain M) A')) ^ (-(c' : ℝ))))
            = ∫⁻ A', ((fun A' => ENNReal.ofReal
                  (frobSq (rmatMul F (prod (tailChain M) A')) ^ (-(c' : ℝ))))
                * (fun _ : Params (tailChain M) => (1 : ℝ≥0∞))) A'
                ∂(volume.restrict (paramsBoxM (tailChain M) 1)) := by
              refine lintegral_congr fun A' => ?_; simp [Pi.mul_apply]
          _ ≤ (∫⁻ A', (fun A' => ENNReal.ofReal
                  (frobSq (rmatMul F (prod (tailChain M) A')) ^ (-(c' : ℝ)))) A' ^ s
                ∂(volume.restrict (paramsBoxM (tailChain M) 1))) ^ (1 / s)
              * (∫⁻ A', (fun _ : Params (tailChain M) => (1 : ℝ≥0∞)) A' ^ sconj
                ∂(volume.restrict (paramsBoxM (tailChain M) 1))) ^ (1 / sconj) :=
              ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpq hf_meas.aemeasurable
                measurable_const.aemeasurable
          _ = (∫⁻ A' in paramsBoxM (tailChain M) 1,
                  ENNReal.ofReal (frobSq (rmatMul F (prod (tailChain M) A')) ^ (-e))) ^ (1 / s)
                * (volume (paramsBoxM (tailChain M) 1)) ^ (1 / sconj) := by
              congr 1
              · congr 1; exact lintegral_congr hpt
              · congr 1; simp only [ENNReal.one_rpow]; exact setLIntegral_one _
      -- combine with the absorption bound.
      have hab := habsorb F hF
      calc (∫⁻ A' in paramsBoxM (tailChain M) 1,
              ENNReal.ofReal (frobSq (rmatMul F (prod (tailChain M) A')) ^ (-(c' : ℝ))))
          ≤ (∫⁻ A' in paramsBoxM (tailChain M) 1,
                ENNReal.ofReal (frobSq (rmatMul F (prod (tailChain M) A')) ^ (-e))) ^ (1 / s)
              * (volume (paramsBoxM (tailChain M) 1)) ^ (1 / sconj) := hhold
        _ ≤ (ENNReal.ofReal (((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-(M 2 : ℝ) / 2)) * Ke) ^ (1 / s)
              * (volume (paramsBoxM (tailChain M) 1)) ^ (1 / sconj) := by
            refine mul_le_mul' ?_ le_rfl
            exact ENNReal.rpow_le_rpow hab h1s
        _ = ENNReal.ofReal (((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-a / 2)) * Cconst := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ h1s, hdetpow, hCconstdef, mul_assoc]
    -- integrate the pointwise bound over `F`; the density integral converges by the real-`a` qbox.
    calc (∫⁻ F in wingFrontBox M, ∫⁻ A' in paramsBoxM (tailChain M) 1,
            ENNReal.ofReal (frobSq (rmatMul F (prod (tailChain M) A')) ^ (-(c' : ℝ))))
        ≤ ∫⁻ F in wingFrontBox M,
            ENNReal.ofReal (((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-a / 2)) * Cconst :=
          setLIntegral_mono (hDetMeas'.mul measurable_const) hpoint
      _ = Cconst * ∫⁻ F in wingFrontBox M,
            ENNReal.ofReal (((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-a / 2)) := by
          rw [← lintegral_const_mul' Cconst _ hCconst.ne]
          refine lintegral_congr fun F => ?_
          rw [mul_comm]
      _ ≤ Cconst * ∫⁻ F in matBox (M 0) (M 1) 1,
            ENNReal.ofReal (((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-a / 2)) :=
          mul_le_mul' le_rfl (lintegral_mono_set hwFsub)
      _ < ⊤ := ENNReal.mul_lt_top hCconst
          (front_gram_qbox_real_lt_top (M₀ := M 0) (M₁ := M 1) a hwide hbnd_a)

end DLNFibre.DLN.RLCT
