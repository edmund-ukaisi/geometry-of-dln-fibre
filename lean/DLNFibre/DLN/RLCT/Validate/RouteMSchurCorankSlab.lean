import DLNFibre.DLN.RLCT.Validate.RouteMSJProjRadial
import DLNFibre.DLN.RLCT.Validate.RouteMSchurWishartWeight
import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankResidual

set_option linter.style.longLine false

open MeasureTheory Set Matrix
open scoped ENNReal BigOperators InnerProductSpace

namespace DLNFibre.DLN.RLCT

/-! ## The corank slab: EuclideanSpace projection-radial core

`slab_projRadial` bounds, uniformly over a UNIT direction `â`, the box integral of
`(∑ₖ ⟨â, S_{·k}⟩²)^{-1/2}`. Viewing `S`'s `p` columns stacked in `EuclideanSpace ℝ (Fin (n·p))`,
`∑ₖ ⟨â, S_{·k}⟩² = ‖P_V(flatten S)‖²` for the `p`-dimensional subspace `V` spanned by the orthonormal
column-frame `{ê_k}` (`ê_k = â placed in column k`); the exponent `-1/2` reads as `-1` on the norm,
so the banked uniform-in-subspace projection bound `projection_rpow_lintegral_uniform` (valid at
`a = 1 < p = r`) gives the constant. Non-spectral. -/

/-- Column-`k` placement of `â`: the `n × p` matrix with column `k` equal to `â`, others zero.
Its flatten is the orthonormal frame vector `ê k`. -/
private def slabCol {n p : ℕ} (â : Fin n → ℝ) (k : Fin p) : Fin n → Fin p → ℝ :=
  fun j l => if l = k then â j else 0

/-- The flatten-space inner product is the Frobenius inner product of the two matrices. -/
private theorem slab_flatInner {n p : ℕ} (A B : Fin n → Fin p → ℝ) :
    ⟪WithLp.toLp 2 (eMatFlat n p A), WithLp.toLp 2 (eMatFlat n p B)⟫_ℝ
      = ∑ a, ∑ l, A a l * B a l := by
  have h0 : ⟪WithLp.toLp 2 (eMatFlat n p A), WithLp.toLp 2 (eMatFlat n p B)⟫_ℝ
      = dotProduct (eMatFlat n p B) (star (eMatFlat n p A)) := rfl
  rw [h0]
  simp only [dotProduct, Pi.star_apply, star_trivial]
  rw [show (∑ m, eMatFlat n p B m * eMatFlat n p A m)
        = ∑ m, (fun jl : (_ : Fin n) × Fin p => A jl.1 jl.2 * B jl.1 jl.2)
                ((sigFlatEquiv n p).symm m)
      from Finset.sum_congr rfl (fun m _ => by rw [eMatFlat_apply, eMatFlat_apply]; ring)]
  rw [Equiv.sum_comp (sigFlatEquiv n p).symm
        (fun jl : (_ : Fin n) × Fin p => A jl.1 jl.2 * B jl.1 jl.2)]
  rw [Fintype.sum_sigma]

/-- The frame vector `ê k` reads column `k`: `⟪ê k, flatten S⟫ = ∑ⱼ âⱼ Sⱼₖ`. -/
private theorem slab_inner_ek_S {n p : ℕ} (â : Fin n → ℝ) (S : Fin n → Fin p → ℝ) (k : Fin p) :
    ⟪WithLp.toLp 2 (eMatFlat n p (slabCol â k)), WithLp.toLp 2 (eMatFlat n p S)⟫_ℝ
      = ∑ j, â j * S j k := by
  rw [slab_flatInner]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [slabCol]
  rw [Finset.sum_eq_single k]
  · rw [if_pos rfl]
  · intro l _ hl; rw [if_neg hl, zero_mul]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- The column-frame `{ê k}` is orthonormal when `â` is a unit vector. -/
private theorem slab_orthonormal {n p : ℕ} (â : Fin n → ℝ) (hâ : ∑ j, (â j) ^ 2 = 1) :
    Orthonormal ℝ (fun k : Fin p => WithLp.toLp 2 (eMatFlat n p (slabCol â k))) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [slab_flatInner]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, ← hâ]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [slabCol]
    rw [show (∑ l, (if l = i then â a else 0) * (if l = i then â a else 0))
          = ∑ l, (if l = i then (â a) ^ 2 else 0) from Finset.sum_congr rfl (fun l _ => by
            rcases eq_or_ne l i with h | h
            · rw [if_pos h, if_pos h]; ring
            · rw [if_neg h, if_neg h]; ring)]
    rw [Finset.sum_ite_eq' Finset.univ i (fun _ => (â a) ^ 2), if_pos (Finset.mem_univ i)]
  · rw [if_neg hij]
    refine Finset.sum_eq_zero (fun a _ => ?_)
    refine Finset.sum_eq_zero (fun l _ => ?_)
    simp only [slabCol]
    rcases eq_or_ne l i with h1 | h1
    · rcases eq_or_ne l j with h2 | h2
      · exact absurd (h1.symm.trans h2) hij
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

private theorem slab_projRadial {n p : ℕ} (hp : 2 ≤ p) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ â : Fin n → ℝ, (∑ j, (â j) ^ 2) = 1 →
      (∫⁻ S in matBox n p 1,
          ENNReal.ofReal ((∑ k, (∑ j, â j * S j k) ^ 2) ^ (-(1 : ℝ) / 2))) ≤ C := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- `n = 0`: the hypothesis `∑ⱼ âⱼ² = 1` is impossible (empty sum), so the bound is vacuous.
    refine ⟨1, by simp, fun â hâ => ?_⟩
    subst hn0
    rw [Fin.sum_univ_zero] at hâ
    exact absurd hâ (by norm_num)
  · set q := n * p with hq
    obtain ⟨C, hCtop, hC⟩ :=
      projection_rpow_lintegral_uniform q p (by omega) (Nat.le_mul_of_pos_left p hn)
        (a := 1) (by exact_mod_cast (show (1 : ℕ) < p by omega)) ((q : ℝ) + 1)
    refine ⟨C, hCtop, fun â hâ => ?_⟩
    -- the orthonormal column-frame and its span
    set ê : Fin p → EuclideanSpace ℝ (Fin q) :=
      fun k => WithLp.toLp 2 (eMatFlat n p (slabCol â k)) with hê
    have hon : Orthonormal ℝ ê := slab_orthonormal â hâ
    have hli : LinearIndependent ℝ ê := hon.linearIndependent
    set V : Submodule ℝ (EuclideanSpace ℝ (Fin q)) := Submodule.span ℝ (Set.range ê) with hV
    have hmem : ∀ i, ê i ∈ V := fun i => Submodule.subset_span (Set.mem_range_self i)
    have hfr : Module.finrank ℝ V = p := by
      rw [hV, finrank_span_eq_card hli, Fintype.card_fin]
    -- an orthonormal basis of `V` whose vectors are the `ê i`
    have hspan_coe : (⇑(Module.Basis.span hli) : Fin p → V)
        = fun i => (⟨ê i, hmem i⟩ : V) :=
      funext (fun i => Module.Basis.span_apply hli i)
    have hon' : Orthonormal ℝ ⇑(Module.Basis.span hli) := by
      rw [hspan_coe]; exact hon.codRestrict V hmem
    set b : OrthonormalBasis (Fin p) ℝ V := (Module.Basis.span hli).toOrthonormalBasis hon' with hb
    have hbcoe : ∀ i, ((b i : EuclideanSpace ℝ (Fin q))) = ê i := by
      intro i
      have h1 : b i = Module.Basis.span hli i :=
        congrFun (Module.Basis.coe_toOrthonormalBasis (Module.Basis.span hli) hon') i
      rw [h1]
      exact Module.Basis.coe_span_apply hli i
    -- the measure-preserving flatten to `EuclideanSpace ℝ (Fin q)`
    set Φ : (Fin n → Fin p → ℝ) → EuclideanSpace ℝ (Fin q) :=
      fun S => WithLp.toLp 2 (eMatFlat n p S) with hΦ
    have hΦmp : MeasurePreserving Φ volume volume :=
      (PiLp.volume_preserving_toLp (Fin q)).comp (measurePreserving_eMatFlat n p)
    have hΦemb : MeasurableEmbedding Φ :=
      (MeasurableEquiv.toLp 2 (Fin q → ℝ)).measurableEmbedding.comp
        (eMatFlat n p).measurableEmbedding
    -- projection norm² as a sum of squared inner products with the frame
    have hproj_sq : ∀ w : EuclideanSpace ℝ (Fin q),
        ‖V.starProjection w‖ ^ 2 = ∑ i, (⟪(b i : EuclideanSpace ℝ (Fin q)), w⟫_ℝ) ^ 2 := by
      intro w
      rw [Submodule.starProjection_apply, Submodule.norm_coe,
        ← b.sum_sq_inner_right (V.orthogonalProjection w)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Submodule.inner_orthogonalProjection_eq_of_mem_left]
    -- pointwise: `‖P_V (Φ S)‖² = ∑ₖ (∑ⱼ âⱼ Sⱼₖ)²`
    have hnorm_sq : ∀ S : Fin n → Fin p → ℝ,
        ‖V.starProjection (Φ S)‖ ^ 2 = ∑ k, (∑ j, â j * S j k) ^ 2 := by
      intro S
      rw [hproj_sq (Φ S)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hbcoe i, show ⟪ê i, Φ S⟫_ℝ = ∑ j, â j * S j i from slab_inner_ek_S â S i]
    -- the `rpow` bridge `base^{-1/2} = ‖P_V(Φ S)‖^{-1}`
    have hkey : ∀ S : Fin n → Fin p → ℝ,
        (∑ k, (∑ j, â j * S j k) ^ 2) ^ (-(1 : ℝ) / 2)
          = ‖V.starProjection (Φ S)‖ ^ (-(1 : ℝ)) := by
      intro S
      rw [← hnorm_sq S, ← Real.rpow_natCast ‖V.starProjection (Φ S)‖ 2,
        ← Real.rpow_mul (norm_nonneg _),
        show ((2 : ℕ) : ℝ) * (-(1 : ℝ) / 2) = -(1 : ℝ) by norm_num]
    -- the box flattens into the enclosing ball
    have hsub : matBox n p 1 ⊆ Φ ⁻¹' (Metric.ball (0 : EuclideanSpace ℝ (Fin q)) ((q : ℝ) + 1)) := by
      intro S hS
      simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right]
      have hsq : ‖Φ S‖ ^ 2 ≤ (q : ℝ) := by
        show ‖WithLp.toLp 2 (eMatFlat n p S)‖ ^ 2 ≤ (q : ℝ)
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
        calc ∑ m, ‖(WithLp.toLp 2 (eMatFlat n p S)) m‖ ^ 2
            ≤ ∑ _m : Fin q, (1 : ℝ) := by
              refine Finset.sum_le_sum (fun m _ => ?_)
              rw [show (WithLp.toLp 2 (eMatFlat n p S)) m = eMatFlat n p S m from rfl,
                eMatFlat_apply, Real.norm_eq_abs, sq_abs]
              have hmm := hS ((sigFlatEquiv n p).symm m).1 ((sigFlatEquiv n p).symm m).2
              rw [Set.mem_Icc] at hmm
              nlinarith [hmm.1, hmm.2]
          _ = (q : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      nlinarith [norm_nonneg (Φ S), hsq, Nat.cast_nonneg (α := ℝ) q]
    -- assemble
    calc ∫⁻ S in matBox n p 1, ENNReal.ofReal ((∑ k, (∑ j, â j * S j k) ^ 2) ^ (-(1 : ℝ) / 2))
        = ∫⁻ S in matBox n p 1, ENNReal.ofReal (‖V.starProjection (Φ S)‖ ^ (-(1 : ℝ))) := by
          refine setLIntegral_congr_fun (matBox_measurableSet n p 1) (fun S _ => ?_)
          rw [hkey S]
      _ ≤ ∫⁻ S in Φ ⁻¹' (Metric.ball (0 : EuclideanSpace ℝ (Fin q)) ((q : ℝ) + 1)),
            ENNReal.ofReal (‖V.starProjection (Φ S)‖ ^ (-(1 : ℝ))) := lintegral_mono_set hsub
      _ = ∫⁻ w in Metric.ball (0 : EuclideanSpace ℝ (Fin q)) ((q : ℝ) + 1),
            ENNReal.ofReal (‖V.starProjection w‖ ^ (-(1 : ℝ))) :=
          hΦmp.setLIntegral_comp_preimage_emb hΦemb
            (fun w => ENNReal.ofReal (‖V.starProjection w‖ ^ (-(1 : ℝ))))
            (Metric.ball 0 ((q : ℝ) + 1))
      _ ≤ C := hC V hfr.ge

theorem corankSlab_charge_sint_le {n p : ℕ} (hp : 2 ≤ p) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ Acor : Fin 1 → Fin n → ℝ,
      (∫⁻ S in matBox n p 1, ENNReal.ofReal ((chargeGramDet Acor S) ^ (-(1 : ℝ) / 2)))
        ≤ C * ENNReal.ofReal ((frobSq Acor) ^ (-(1 : ℝ) / 2)) := by
  obtain ⟨C, hCtop, hC⟩ := slab_projRadial (n := n) (p := p) hp
  refine ⟨C, hCtop, fun Acor => ?_⟩
  set a : Fin n → ℝ := Acor 0 with ha
  set A2 : ℝ := ∑ j, (a j) ^ 2 with hA2
  have hA2nn : 0 ≤ A2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hCG : ∀ S : Fin n → Fin p → ℝ,
      chargeGramDet Acor S = ∑ k, (∑ j, a j * S j k) ^ 2 := by
    intro S
    rw [chargeGramDet_one, frobSq, Fin.sum_univ_one]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [rmatMul]
  have hfr : frobSq Acor = A2 := by
    rw [frobSq, Fin.sum_univ_one]
  rw [hfr]
  rcases eq_or_lt_of_le hA2nn with hA0 | hApos
  · have haz : ∀ j, a j = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (a j))).mp hA0.symm
      exact fun j => pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp (this j (Finset.mem_univ j))
    have hcg0 : ∀ S : Fin n → Fin p → ℝ, chargeGramDet Acor S = 0 := by
      intro S; rw [hCG]; refine Finset.sum_eq_zero (fun k _ => ?_)
      rw [Finset.sum_eq_zero (fun j _ => by rw [haz j, zero_mul])]; ring
    have hlhs : (∫⁻ S in matBox n p 1,
        ENNReal.ofReal ((chargeGramDet Acor S) ^ (-(1 : ℝ) / 2))) = 0 := by
      rw [← lintegral_zero (μ := volume.restrict (matBox n p 1))]
      refine lintegral_congr (fun S => ?_)
      rw [hcg0 S, Real.zero_rpow (by norm_num), ENNReal.ofReal_zero]
    rw [hlhs, ← hA0, Real.zero_rpow (by norm_num), ENNReal.ofReal_zero, mul_zero]
  · set r : ℝ := Real.sqrt A2 with hr
    have hrpos : 0 < r := Real.sqrt_pos.mpr hApos
    set â : Fin n → ℝ := fun j => a j / r with hâ
    have hâsum : (∑ j, (â j) ^ 2) = 1 := by
      simp only [hâ, div_pow]
      rw [← Finset.sum_div, ← hA2, hr, Real.sq_sqrt hA2nn, div_self (ne_of_gt hApos)]
    have hfac : ∀ S : Fin n → Fin p → ℝ,
        chargeGramDet Acor S = A2 * (∑ k, (∑ j, â j * S j k) ^ 2) := by
      intro S
      rw [hCG, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have : (∑ j, a j * S j k) = r * (∑ j, â j * S j k) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hâ]; field_simp
      rw [this, mul_pow, hr, Real.sq_sqrt hA2nn]
    have hcalc : (∫⁻ S in matBox n p 1, ENNReal.ofReal ((chargeGramDet Acor S) ^ (-(1 : ℝ) / 2)))
        = ENNReal.ofReal (A2 ^ (-(1 : ℝ) / 2))
            * ∫⁻ S in matBox n p 1,
                ENNReal.ofReal ((∑ k, (∑ j, â j * S j k) ^ 2) ^ (-(1 : ℝ) / 2)) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr (fun S => ?_)
      rw [hfac S, Real.mul_rpow hA2nn (by positivity), ENNReal.ofReal_mul (by positivity)]
    rw [hcalc, mul_comm]
    exact mul_le_mul_right' (hC â hâsum) _

end DLNFibre.DLN.RLCT
