import DLNFibre.DLN.RLCT.Validate.RouteMSJMonomialLower
import DLNFibre.DLN.RLCT.Validate.RouteMSJRadialPolar
import DLNFibre.DLN.RLCT.Validate.Case222CoverGETail
import DLNFibre.DLN.RLCT.Foundations.S1RadialMorse
import DLNFibre.DLN.RLCT.Foundations.S1Cover

/-!
# `DLNFibre.DLN.RLCT.Validate.RegionGlueModelRead` — the per-leaf monomialised-integrand model read

The analytic core of `region_glue`'s per-leaf step, on the flat coordinates `Fin N → ℝ` and
decoupled from the engine carrier: after the area-formula change of variables the leaf integrand is
bounded (via the `LeafPullback` squeeze) by

    (∏_k |x (dc k)|^{e_k}) · (∑_i (x (rc i))²)^{-c'}       (dc, rc injective + disjoint index maps)

over the bounded flat cube. This module proves that model integral is finite for `e_k > −1` and
`c' < nr/2` (`c' > 0`) — the SEPARATED read the elder-ratified gate verdict maps to banked 1-D reads.

**Route (split-free, via AM-GM).** The joint Morse factor `(∑_i x_{rc i}²)^{-c'}` is dominated
coordinate-wise by `nr^{-c'} · ∏_i |x_{rc i}|^{-2c'/nr}` (`geom_mean_le_arith_mean_weighted`, uniform
weights `1/nr`), per-axis exponent `−2c'/nr > −1 ⟺ c' < nr/2`. So the whole model integrand is `≤` a
single product of per-axis `rpow`s over ALL coordinates (divisor exponents `e_k`, Morse exponents
`−2c'/nr`, spectator exponents `0`), and `prod_abs_rpow_cube_lt_top` closes it — no Tonelli.

**The domination is A.E., not pointwise.** At a point where some (not all) `x_{rc i} = 0` the LHS is
finite but the RHS product carries a `0^{neg} = 0` factor, so the bound FAILS there; it holds only
off `⋃_i {x_{rc i} = 0}`, a finite union of coordinate hyperplanes, each `volume`-null
(`Measure.pi_hyperplane`). `lintegral_mono_ae` absorbs the null exceptional set.

Bottom-up bricks: `abs_rpow_lintegral_Icc_lt_top` (1-D, symmetric interval) →
`prod_abs_rpow_cube_lt_top` (product over the closed cube) → the AM-GM domination + the model read.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

/-- **Product `rpow` read over the closed cube.** For `f_j > −1` on every axis, the product of
per-axis `rpow`s has finite `∫⁻` over the closed cube `[−R,R]^d` (`R > 0`). The `[−R,R]` companion
of the banked `prod_rpow_lintegral_Ioo_box_lt_top`: the SAME `piFinSuccAbove` factoring, with the
symmetric 1-D base `abs_rpow_lintegral_Icc_lt_top`. -/
theorem prod_abs_rpow_cube_lt_top : ∀ {d : ℕ} (R : ℝ) (_hR : 0 < R) (f : Fin d → ℝ)
    (_hf : ∀ j, -1 < f j),
    ∫⁻ x in cubeBox d R, ENNReal.ofReal (∏ j, |x j| ^ (f j)) < ⊤
  | 0, R, _hR, f, _hf => by
      simp only [Finset.univ_eq_empty, Finset.prod_empty, ENNReal.ofReal_one, setLIntegral_one]
      rw [cubeBox, volume_pi_pi]; simp
  | (n + 1), R, hR, f, hf => by
      classical
      have hof : ∀ x : Fin (n + 1) → ℝ, ENNReal.ofReal (∏ j, |x j| ^ (f j))
          = ∏ j, ENNReal.ofReal (|x j| ^ (f j)) :=
        fun x => ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) _)
      simp_rw [hof]
      set ee := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 with hee
      have hsymapp : ∀ x (y : Fin n → ℝ), ee.symm (x, y) = Fin.insertNth 0 x y := fun x y => by
        rw [hee, MeasurableEquiv.piFinSuccAbove_symm_apply]; exact List.ofFn_inj.mp rfl
      have hmpS : MeasurePreserving ee.symm (volume : Measure (ℝ × (Fin n → ℝ))) volume := by
        have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
        rwa [show (volume : Measure (ℝ × (Fin n → ℝ))) = (volume : Measure ℝ).prod volume from
          Measure.volume_eq_prod _ _] at h
      have hpre : ee.symm ⁻¹' (cubeBox (n + 1) R)
          = (Set.Icc (-R) R) ×ˢ cubeBox n R := by
        ext p; obtain ⟨x, y⟩ := p
        simp only [cubeBox, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod,
          hsymapp]
        constructor
        · intro hall
          refine ⟨?_, fun k => ?_⟩
          · have := hall 0; rwa [Fin.insertNth_apply_same] at this
          · have := hall (Fin.succAbove 0 k); rwa [Fin.insertNth_apply_succAbove] at this
        · rintro ⟨h0, hrest⟩ j
          rcases Fin.eq_self_or_eq_succAbove 0 j with rfl | ⟨k, rfl⟩
          · rwa [Fin.insertNth_apply_same]
          · rw [Fin.insertNth_apply_succAbove]; exact hrest k
      have htrans := hmpS.setLIntegral_comp_preimage_emb (MeasurableEquiv.measurableEmbedding _)
        (fun x : Fin (n + 1) → ℝ => ∏ j, ENNReal.ofReal (|x j| ^ (f j))) (cubeBox (n + 1) R)
      rw [hpre] at htrans
      rw [← htrans]
      have hfac : ∀ x (y : Fin n → ℝ),
          (∏ j, ENNReal.ofReal (|ee.symm (x, y) j| ^ (f j)))
            = ENNReal.ofReal (|x| ^ (f 0))
              * ∏ k, ENNReal.ofReal (|y k| ^ (f (Fin.succAbove 0 k))) := by
        intro x y
        simp_rw [hsymapp]
        rw [Fin.prod_univ_succAbove _ 0, Fin.insertNth_apply_same]
        simp_rw [Fin.insertNth_apply_succAbove]
      simp_rw [hfac]
      rw [show (volume : Measure (ℝ × (Fin n → ℝ))) = (volume : Measure ℝ).prod volume from
        Measure.volume_eq_prod _ _]
      rw [setLIntegral_prod _ (by
        apply Measurable.aemeasurable; apply Measurable.mul
        · exact (by fun_prop :
            Measurable (fun p : ℝ × (Fin n → ℝ) => ENNReal.ofReal (|p.1| ^ (f 0))))
        · apply Finset.measurable_prod; intro k _; fun_prop)]
      have hinner : ∀ x, (∫⁻ y in cubeBox n R,
          ENNReal.ofReal (|x| ^ (f 0)) * ∏ k, ENNReal.ofReal (|y k| ^ (f (Fin.succAbove 0 k)))
          ∂(volume : Measure (Fin n → ℝ)))
          = ENNReal.ofReal (|x| ^ (f 0))
            * (∫⁻ y in cubeBox n R, ∏ k, ENNReal.ofReal (|y k| ^ (f (Fin.succAbove 0 k)))
                ∂(volume : Measure (Fin n → ℝ))) :=
        fun x => lintegral_const_mul _ (by apply Finset.measurable_prod; intro k _; fun_prop)
      simp only [hinner]
      rw [lintegral_mul_const _
        (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal (|x| ^ (f 0))))]
      have hIH : ∫⁻ y in cubeBox n R, ENNReal.ofReal (∏ k, |y k| ^ (f (Fin.succAbove 0 k))) < ⊤ :=
        prod_abs_rpow_cube_lt_top R hR (fun k => f (Fin.succAbove 0 k))
          (fun k => hf (Fin.succAbove 0 k))
      have hIH' : ∫⁻ y in cubeBox n R,
          ∏ k, ENNReal.ofReal (|y k| ^ (f (Fin.succAbove 0 k))) < ⊤ := by
        rw [show (fun y : Fin n → ℝ => ∏ k, ENNReal.ofReal (|y k| ^ (f (Fin.succAbove 0 k))))
            = fun y : Fin n → ℝ => ENNReal.ofReal (∏ k, |y k| ^ (f (Fin.succAbove 0 k))) from
          funext (fun y => (ENNReal.ofReal_prod_of_nonneg
            (fun k _ => Real.rpow_nonneg (abs_nonneg _) _)).symm)]
        exact hIH
      have hax : ∫⁻ x in Set.Icc (-R) R, ENNReal.ofReal (|x| ^ (f 0)) < ⊤ :=
        abs_rpow_lintegral_Icc_lt_top R hR (f 0) (hf 0)
      exact ENNReal.mul_lt_top hax hIH'

/-- **Two-family exponent assembly (pointwise, all `x`).** For injective `dc`, `rc` with disjoint
ranges into `Fin d`, any per-axis exponent `g` agreeing with `e` on the divisor coords, with `f` on
the residual coords, and `0` off both, collapses the two-family product of per-axis `rpow`s to the
single all-axis product `∏_j |x j|^{g j}`. Reindexing of the PRODUCT (via `Finset.prod_image`/
`prod_union`/`prod_subset`), not the exponent — so `x_j = 0` axes are fine (`|·|^0 = 1`). -/
theorem prod_two_family_eq {d nd nr : ℕ} (dc : Fin nd → Fin d) (rc : Fin nr → Fin d)
    (hdc : Function.Injective dc) (hrc : Function.Injective rc)
    (hdisj : Disjoint (Set.range dc) (Set.range rc))
    (e : Fin nd → ℝ) (f : ℝ) (g : Fin d → ℝ)
    (hgd : ∀ k, g (dc k) = e k) (hgr : ∀ i, g (rc i) = f)
    (hg0 : ∀ j, (∀ k, dc k ≠ j) → (∀ i, rc i ≠ j) → g j = 0)
    (x : Fin d → ℝ) :
    (∏ k, |x (dc k)| ^ (e k)) * (∏ i, |x (rc i)| ^ f) = ∏ j, |x j| ^ (g j) := by
  classical
  set Sd : Finset (Fin d) := Finset.univ.image dc with hSd
  set Sr : Finset (Fin d) := Finset.univ.image rc with hSr
  have hdisjF : Disjoint Sd Sr := by
    rw [Finset.disjoint_left]
    intro j hjd hjr
    rw [hSd, Finset.mem_image] at hjd
    rw [hSr, Finset.mem_image] at hjr
    obtain ⟨k, -, hk⟩ := hjd
    obtain ⟨i, -, hi⟩ := hjr
    exact Set.disjoint_left.mp hdisj ⟨k, hk⟩ ⟨i, hi⟩
  have hprodD : (∏ j ∈ Sd, |x j| ^ (g j)) = ∏ k, |x (dc k)| ^ (e k) := by
    rw [hSd, Finset.prod_image (fun a _ b _ hab => hdc hab)]
    exact Finset.prod_congr rfl (fun k _ => by rw [hgd k])
  have hprodR : (∏ j ∈ Sr, |x j| ^ (g j)) = ∏ i, |x (rc i)| ^ f := by
    rw [hSr, Finset.prod_image (fun a _ b _ hab => hrc hab)]
    exact Finset.prod_congr rfl (fun i _ => by rw [hgr i])
  have hrest : ∏ j, |x j| ^ (g j) = ∏ j ∈ Sd ∪ Sr, |x j| ^ (g j) := by
    symm
    apply Finset.prod_subset (Finset.subset_univ _)
    intro j _ hj
    rw [Finset.mem_union] at hj
    push_neg at hj
    obtain ⟨hjd, hjr⟩ := hj
    have hgj : g j = 0 := by
      refine hg0 j (fun k hk => hjd ?_) (fun i hi => hjr ?_)
      · rw [hSd, Finset.mem_image]; exact ⟨k, Finset.mem_univ _, hk⟩
      · rw [hSr, Finset.mem_image]; exact ⟨i, Finset.mem_univ _, hi⟩
    rw [hgj, Real.rpow_zero]
  rw [hrest, Finset.prod_union hdisjF, hprodD, hprodR]

/-- **Coordinate-wise Morse domination (all-nonzero fibre).** For `c' > 0`, `nr ≥ 1`, and `y` with
every `y i ≠ 0`, the joint Morse factor is `≤` the product of per-axis powers — AM-GM with uniform
weights `1/nr` gives `∏ |y i|^{2/nr} ≤ (∑ y i²)/nr`, then `t ↦ t^{-c'}` (antitone, both sides `> 0`)
flips it. Off `{∃ i, y i = 0}` — null upstream (`Measure.pi_hyperplane`) — this is the squeeze feeding
`prod_abs_rpow_cube_lt_top`. -/
theorem sumSq_rpow_neg_le {nr : ℕ} (hnr : 0 < nr) (c' : ℝ) (hc' : 0 < c')
    (y : Fin nr → ℝ) (hy : ∀ i, y i ≠ 0) :
    (∑ i, (y i) ^ 2) ^ (-c') ≤ (nr : ℝ) ^ (-c') * ∏ i, |y i| ^ (-2 * c' / (nr : ℝ)) := by
  have hnrR : (0 : ℝ) < nr := by exact_mod_cast hnr
  -- AM-GM (uniform weights), with both sides rewritten to closed form
  have hAM : (∏ i, |y i| ^ ((2 : ℝ) / nr)) ≤ (∑ i, (y i) ^ 2) / nr := by
    have h := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ : Fin nr => 1 / (nr : ℝ))
      (fun i => (y i) ^ 2) (fun i _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp)
      (fun i _ => by positivity)
    have hL : (∏ i, ((y i) ^ 2) ^ (1 / (nr : ℝ))) = ∏ i, |y i| ^ ((2 : ℝ) / nr) :=
      Finset.prod_congr rfl (fun i _ => by
        rw [← sq_abs (y i), ← Real.rpow_two |y i|, ← Real.rpow_mul (abs_nonneg _), mul_one_div])
    have hR : (∑ i, (1 / (nr : ℝ)) * (y i) ^ 2) = (∑ i, (y i) ^ 2) / nr := by
      rw [← Finset.mul_sum, one_div_mul_eq_div]
    rwa [hL, hR] at h
  -- positivity of the two sides
  have hPpos : (0 : ℝ) < ∏ i, |y i| ^ ((2 : ℝ) / nr) :=
    Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (abs_pos.mpr (hy i)) _)
  have hSpos : (0 : ℝ) < ∑ i, (y i) ^ 2 := by
    refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨⟨0, hnr⟩, Finset.mem_univ _, ?_⟩
    have := hy ⟨0, hnr⟩; positivity
  -- the RHS is `(nr · P)^{-c'}`
  have hRHS : (nr : ℝ) ^ (-c') * (∏ i, |y i| ^ (-2 * c' / (nr : ℝ)))
      = ((nr : ℝ) * ∏ i, |y i| ^ ((2 : ℝ) / nr)) ^ (-c') := by
    rw [Real.mul_rpow hnrR.le hPpos.le,
      ← Real.finset_prod_rpow Finset.univ (fun i => |y i| ^ ((2 : ℝ) / nr))
        (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)]
    congr 1
    exact Finset.prod_congr rfl (fun i _ => by
      rw [← Real.rpow_mul (abs_nonneg _)]; congr 1; ring)
  rw [hRHS]
  -- antitone `t ↦ t^{-c'}` on `0 < nr·P ≤ S`
  have hnrP : (0 : ℝ) < (nr : ℝ) * ∏ i, |y i| ^ ((2 : ℝ) / nr) := mul_pos hnrR hPpos
  have hle : (nr : ℝ) * (∏ i, |y i| ^ ((2 : ℝ) / nr)) ≤ ∑ i, (y i) ^ 2 := by
    rw [mul_comm]; exact (le_div_iff₀ hnrR).mp hAM
  rw [Real.rpow_neg hSpos.le, Real.rpow_neg hnrP.le, ← one_div, ← one_div]
  exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hnrP _)
    (Real.rpow_le_rpow hnrP.le hle hc'.le)

/-- **The per-leaf model read (flat coordinates).** For injective/disjoint divisor `dc` and residual
`rc` coordinate maps into `Fin d`, divisor exponents `e_k > −1`, `c' > 0` below `nr/2` (`nr ≥ 1` the
Morse rank), the monomialised leaf integrand
`(∏_k |x_{dc k}|^{e_k}) · (∑_i x_{rc i}²)^{-c'}` has finite `∫⁻` over the closed cube `[−R,R]^d`.
Route: AM-GM domination of the Morse factor (a.e., off the coordinate hyperplanes) + the two-family
reindex collapse to `∏_j |x j|^{G j}` (`G_j > −1` everywhere), closed by `prod_abs_rpow_cube_lt_top`. -/
theorem model_read_lt_top {d : ℕ} (R : ℝ) (hR : 0 < R)
    {nd nr : ℕ} (hnr0 : 0 < nr) (dc : Fin nd → Fin d) (rc : Fin nr → Fin d)
    (hdc : Function.Injective dc) (hrc : Function.Injective rc)
    (hdisj : Disjoint (Set.range dc) (Set.range rc))
    (e : Fin nd → ℝ) (he : ∀ k, -1 < e k)
    (c' : ℝ) (hc' : 0 < c') (hnr : c' < (nr : ℝ) / 2) :
    ∫⁻ x in cubeBox d R,
        ENNReal.ofReal ((∏ k, |x (dc k)| ^ (e k)) * (∑ i, (x (rc i)) ^ 2) ^ (-c')) < ⊤ := by
  classical
  have hnrR : (0 : ℝ) < nr := by exact_mod_cast hnr0
  -- the per-axis assembled exponent
  set g : Fin d → ℝ :=
    fun j => (∑ k, if dc k = j then e k else 0) + (∑ i, if rc i = j then -2 * c' / (nr : ℝ) else 0)
    with hgdef
  have hgd : ∀ k₀, g (dc k₀) = e k₀ := fun k₀ => by
    show (∑ k, if dc k = dc k₀ then e k else 0)
        + (∑ i, if rc i = dc k₀ then -2 * c' / (nr : ℝ) else 0) = e k₀
    rw [Finset.sum_eq_single k₀ (fun k _ hk => if_neg (fun h => hk (hdc h)))
        (fun h => absurd (Finset.mem_univ k₀) h), if_pos rfl,
      Finset.sum_eq_zero (fun i _ => if_neg (fun h =>
        Set.disjoint_left.mp hdisj ⟨k₀, rfl⟩ ⟨i, h⟩)), add_zero]
  have hgr : ∀ i₀, g (rc i₀) = -2 * c' / (nr : ℝ) := fun i₀ => by
    show (∑ k, if dc k = rc i₀ then e k else 0)
        + (∑ i, if rc i = rc i₀ then -2 * c' / (nr : ℝ) else 0) = -2 * c' / (nr : ℝ)
    rw [Finset.sum_eq_zero (fun k _ => if_neg (fun h =>
        Set.disjoint_left.mp hdisj ⟨k, h⟩ ⟨i₀, rfl⟩)),
      Finset.sum_eq_single i₀ (fun i _ hi => if_neg (fun h => hi (hrc h)))
        (fun h => absurd (Finset.mem_univ i₀) h), if_pos rfl, zero_add]
  have hg0 : ∀ j, (∀ k, dc k ≠ j) → (∀ i, rc i ≠ j) → g j = 0 := fun j hjd hjr => by
    show (∑ k, if dc k = j then e k else 0) + (∑ i, if rc i = j then -2 * c' / (nr : ℝ) else 0) = 0
    rw [Finset.sum_eq_zero (fun k _ => if_neg (hjd k)),
      Finset.sum_eq_zero (fun i _ => if_neg (hjr i)), add_zero]
  have hf0pos : -1 < -2 * c' / (nr : ℝ) := by
    rw [lt_div_iff₀ hnrR]; linarith [hnr]
  have hgpos : ∀ j, -1 < g j := by
    intro j
    by_cases hjd : ∃ k, dc k = j
    · obtain ⟨k, rfl⟩ := hjd; rw [hgd k]; exact he k
    · by_cases hjr : ∃ i, rc i = j
      · obtain ⟨i, rfl⟩ := hjr; rw [hgr i]; exact hf0pos
      · push_neg at hjd hjr; rw [hg0 j hjd hjr]; norm_num
  -- a.e. every residual coordinate is nonzero (finite union of null coordinate hyperplanes)
  have hae : ∀ᵐ x : (Fin d → ℝ), ∀ i : Fin nr, x (rc i) ≠ 0 := by
    rw [MeasureTheory.ae_all_iff]
    intro i
    have h := MeasureTheory.Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) (rc i) (0 : ℝ)
    rwa [← MeasureTheory.volume_pi] at h
  -- finiteness of the dominating integral
  have hfin : ∫⁻ x in cubeBox d R,
      ENNReal.ofReal ((nr : ℝ) ^ (-c') * ∏ j, |x j| ^ (g j)) < ⊤ := by
    have hcubeM : MeasurableSet (cubeBox d R) := by
      rw [cubeBox]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
    rw [setLIntegral_congr_fun hcubeM (fun x _ => by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg nr) _)]),
      lintegral_const_mul _ (by fun_prop)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (prod_abs_rpow_cube_lt_top R hR g hgpos)
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hfin
  filter_upwards [ae_restrict_of_ae hae] with x hx
  apply ENNReal.ofReal_le_ofReal
  calc (∏ k, |x (dc k)| ^ (e k)) * (∑ i, (x (rc i)) ^ 2) ^ (-c')
      ≤ (∏ k, |x (dc k)| ^ (e k))
          * ((nr : ℝ) ^ (-c') * ∏ i, |x (rc i)| ^ (-2 * c' / (nr : ℝ))) :=
        mul_le_mul_of_nonneg_left (sumSq_rpow_neg_le hnr0 c' hc' (fun i => x (rc i)) hx)
          (Finset.prod_nonneg (fun k _ => Real.rpow_nonneg (abs_nonneg _) _))
    _ = (nr : ℝ) ^ (-c')
          * ((∏ k, |x (dc k)| ^ (e k)) * ∏ i, |x (rc i)| ^ (-2 * c' / (nr : ℝ))) := by ring
    _ = (nr : ℝ) ^ (-c') * ∏ j, |x j| ^ (g j) := by
        rw [prod_two_family_eq dc rc hdc hrc hdisj e (-2 * c' / (nr : ℝ)) g hgd hgr hg0]

end DLNFibre.DLN.RLCT
