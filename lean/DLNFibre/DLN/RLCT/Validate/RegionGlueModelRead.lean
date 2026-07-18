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

end DLNFibre.DLN.RLCT
