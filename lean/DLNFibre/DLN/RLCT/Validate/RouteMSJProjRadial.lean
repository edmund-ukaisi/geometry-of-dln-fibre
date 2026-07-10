import DLNFibre.DLN.RLCT.Validate.RouteMSJRadialInt
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJProjRadial` — uniform projection radial bound (piece "P2")

**Thread `genm-catI-p2-proj`, the Cat I good-stratum uniform-in-subspace bound.** For a fixed
exponent `a < r` and radius `R`, the radial integral of `‖proj_U w‖^{−a}` over the `q`-ball is
bounded by a constant `C < ⊤` that is **uniform over all subspaces `U` of dimension `≥ r`**.

The mechanism. For a fixed `U`, the ambient space splits isometrically as
`E ≃ᵢ WithLp 2 (U × Uᗮ)` (`Submodule.orthogonalDecomposition`); composing the two coordinate
reprs folds this into a single isometry `E ≃ᵢ WithLp 2 (𝔼^d × 𝔼^e)`
(`d = finrank U`, `e = finrank Uᗮ`), which is measure preserving into `𝔼^d × 𝔼^e` (via
`WithLp.volume_preserving_ofLp`). The integrand reads only the `𝔼^d`-factor, whose norm equals
`‖proj_U w‖`; the ball `{‖w‖<R}` maps into `ball_{𝔼^d} R ×ˢ ball_{𝔼^e} R` (projections are
norm-nonincreasing), so enlarging the domain and splitting the product gives
`≤ (∫_{ball_{𝔼^d}} ‖x‖^{−a}) · vol(ball_{𝔼^e})`. The radial factor is `< ⊤` (`a < r ≤ d`,
`RouteMSJRadialInt.lintegral_norm_rpow_neg_ball_lt_top`) and the volume factor is `< ⊤`
(bounded ball). Summing over the finitely many possible dimensions `d ∈ [r,q]`, `e ∈ [0,q]`
gives the uniform constant.

S2-FREE: pure Mathlib analysis. Intended axiom footprint `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Metric
open scoped ENNReal

/-- The coordinate-space radial value `∫⁻_{ball_{𝔼^d} R} ‖x‖^{−a}` (finite when `a < d`). -/
private noncomputable def radVal (a R : ℝ) (d : ℕ) : ℝ≥0∞ :=
  ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R, ENNReal.ofReal (‖x‖ ^ (-a))

/-- The coordinate-space ball volume `vol(ball_{𝔼^k} R)` (always finite). -/
private noncomputable def volVal (R : ℝ) (k : ℕ) : ℝ≥0∞ :=
  volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R)

/-- **Product-space marginal split** for a first-coordinate-only integrand. -/
private theorem setLIntegral_prod_fst_split (a R : ℝ) (d e : ℕ) :
    (∫⁻ p in (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R
                ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin e)) R),
        ENNReal.ofReal (‖p.1‖ ^ (-a)))
    = radVal a R d * volVal R e := by
  have h1 : (∫⁻ p in (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R
                ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin e)) R),
        ENNReal.ofReal (‖p.1‖ ^ (-a)))
      = ∫⁻ p, ENNReal.ofReal (‖p.1‖ ^ (-a)) * 1
          ∂((volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R)).prod
            (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin e)) R))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    simp only [mul_one]
  rw [h1, lintegral_prod_mul (f := fun x : EuclideanSpace ℝ (Fin d) ↦ ENNReal.ofReal (‖x‖ ^ (-a)))
      (g := fun _ : EuclideanSpace ℝ (Fin e) ↦ (1 : ℝ≥0∞)) (by fun_prop) aemeasurable_const,
    lintegral_one, Measure.restrict_apply_univ]
  rfl

/-- **Per-subspace projection radial bound.** For a fixed `U` with `finrank U = d` and
`finrank Uᗮ = e`, the projection radial integral is `≤ radVal a R d * volVal R e`. -/
private theorem projection_rpow_lintegral_le_single {q : ℕ} (a R : ℝ)
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin q))) :
    (∫⁻ w in Metric.ball (0 : EuclideanSpace ℝ (Fin q)) R,
        ENNReal.ofReal (‖U.starProjection w‖ ^ (-a)))
    ≤ radVal a R (Module.finrank ℝ U) * volVal R (Module.finrank ℝ Uᗮ) := by
  set d := Module.finrank ℝ U with hd
  set e := Module.finrank ℝ Uᗮ with he
  set bU := stdOrthonormalBasis ℝ U with hbU
  set bV := stdOrthonormalBasis ℝ (Uᗮ) with hbV
  -- single composite isometry into the coordinate product (avoids measures on ↥U, ↥Uᗮ)
  set Φ : EuclideanSpace ℝ (Fin q) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e)) :=
    U.orthogonalDecomposition.trans (LinearIsometryEquiv.withLpProdCongr 2 bU.repr bV.repr)
    with hΦ
  set T : EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e) :=
    fun w ↦ WithLp.ofLp (Φ w) with hT_def
  have hT : MeasurePreserving T volume volume :=
    (WithLp.volume_preserving_ofLp (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin e))).comp
      Φ.measurePreserving
  -- norm bridges: the two components read the projections
  have hnorm : ∀ w, ‖U.starProjection w‖ = ‖(T w).1‖ := by
    intro w
    rw [hT_def]
    simp only [hΦ, LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.withLpProdCongr_apply, WithLp.toLp_fst,
      Submodule.fst_orthogonalDecomposition_apply, LinearIsometryEquiv.norm_map]
    rw [Submodule.starProjection_apply, Submodule.norm_coe]
  have hnorm2 : ∀ w, ‖Uᗮ.starProjection w‖ = ‖(T w).2‖ := by
    intro w
    rw [hT_def]
    simp only [hΦ, LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.withLpProdCongr_apply, WithLp.toLp_snd,
      Submodule.snd_orthogonalDecomposition_apply, LinearIsometryEquiv.norm_map]
    rw [Submodule.starProjection_apply, Submodule.norm_coe]
  -- ball inclusion (projections norm-nonincreasing)
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin q)) R ⊆
      T ⁻¹' (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R
              ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin e)) R) := by
    intro w hw
    rw [mem_ball_zero_iff] at hw
    simp only [Set.mem_preimage, Set.mem_prod, mem_ball_zero_iff]
    refine ⟨?_, ?_⟩
    · calc ‖(T w).1‖ = ‖U.starProjection w‖ := (hnorm w).symm
        _ ≤ ‖w‖ := U.norm_starProjection_apply_le w
        _ < R := hw
    · calc ‖(T w).2‖ = ‖Uᗮ.starProjection w‖ := (hnorm2 w).symm
        _ ≤ ‖w‖ := Uᗮ.norm_starProjection_apply_le w
        _ < R := hw
  have hF : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e) ↦
      ENNReal.ofReal (‖p.1‖ ^ (-a))) := by fun_prop
  calc (∫⁻ w in Metric.ball (0 : EuclideanSpace ℝ (Fin q)) R,
          ENNReal.ofReal (‖U.starProjection w‖ ^ (-a)))
      = ∫⁻ w in Metric.ball (0 : EuclideanSpace ℝ (Fin q)) R,
          ENNReal.ofReal (‖(T w).1‖ ^ (-a)) :=
        lintegral_congr (fun w ↦ by rw [hnorm w])
    _ ≤ ∫⁻ w in T ⁻¹' (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R
            ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin e)) R),
          ENNReal.ofReal (‖(T w).1‖ ^ (-a)) := lintegral_mono_set hsub
    _ = ∫⁻ p in (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R
            ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin e)) R),
          ENNReal.ofReal (‖p.1‖ ^ (-a)) :=
        hT.setLIntegral_comp_preimage (measurableSet_ball.prod measurableSet_ball) hF
    _ = radVal a R d * volVal R e := setLIntegral_prod_fst_split a R d e

/-- **Uniform-in-subspace projection radial bound (piece "P2").** For `a < r`, there is a finite
constant `C` bounding `∫⁻_{ball R} ‖proj_U w‖^{−a}` uniformly over all subspaces `U` of
`𝔼^q` with `finrank U ≥ r` (here `r ≤ q`, `r ≥ 1`). -/
theorem projection_rpow_lintegral_uniform (q r : ℕ) (hr : 1 ≤ r) (hrq : r ≤ q)
    {a : ℝ} (ha : a < r) (R : ℝ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ U : Submodule ℝ (EuclideanSpace ℝ (Fin q)),
        r ≤ Module.finrank ℝ U →
        (∫⁻ w in Metric.ball (0 : EuclideanSpace ℝ (Fin q)) R,
          ENNReal.ofReal (‖U.starProjection w‖ ^ (-a))) ≤ C := by
  refine ⟨(∑ d ∈ Finset.Icc r q, radVal a R d) * (∑ k ∈ Finset.range (q + 1), volVal R k),
    ?_, ?_⟩
  · -- finiteness of the uniform constant
    apply ENNReal.mul_lt_top
    · rw [ENNReal.sum_lt_top]
      intro d hd
      rw [Finset.mem_Icc] at hd
      have h1d : 1 ≤ d := le_trans hr hd.1
      have had : a < (d : ℝ) := lt_of_lt_of_le ha (by exact_mod_cast hd.1)
      exact lintegral_norm_rpow_neg_ball_lt_top h1d had R
    · rw [ENNReal.sum_lt_top]
      intro k _
      exact measure_ball_lt_top
  · -- the uniform bound, subspace by subspace
    intro U hU
    have hdq : Module.finrank ℝ U ≤ q := by
      have := Submodule.finrank_le U
      rwa [finrank_euclideanSpace_fin] at this
    have heq : Module.finrank ℝ Uᗮ ≤ q := by
      have := Submodule.finrank_le Uᗮ
      rwa [finrank_euclideanSpace_fin] at this
    have hd_mem : Module.finrank ℝ U ∈ Finset.Icc r q := Finset.mem_Icc.mpr ⟨hU, hdq⟩
    have he_mem : Module.finrank ℝ Uᗮ ∈ Finset.range (q + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le heq)
    refine (projection_rpow_lintegral_le_single a R U).trans ?_
    exact mul_le_mul' (Finset.single_le_sum (fun i _ ↦ zero_le _) hd_mem)
      (Finset.single_le_sum (fun i _ ↦ zero_le _) he_mem)

end DLNFibre.DLN.RLCT
