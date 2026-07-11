import DLNFibre.DLN.RLCT.Validate.RouteMSJOnePeel334
import Mathlib.MeasureTheory.Integral.Pi

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJCorankQ` — the corank-`q` coupled majorant (route S)

**Thread `genm-sj5-schur` (aoyagi-full), the `cell_{q≥2}` brick of the shared `g(Q)` (cert #131,
`corankq-cert.md`).** The `q`-block generalization of the banked corank-2 rung
(`RouteMSJOnePeel334.onePeelIntegral_lt_top`, width-general in `(h₀,h₁,m₀,m₁)`): the tail product `Q`
has exactly `q` collapsing singular directions, the loss is the **block-additive** corner sum, and the
box integral is finite for `c' < ½·Σ_i(h_i+1) = ½(D_q + d_q)`.

## The two load-bearing soundness pieces (cert §2 — the RLCT-collapse is REAL, avoided exactly)

1. **ADD, not MIN.** The loss is the ADDITIVE (indicator / block-diagonal) corner `Σ_i u_i²·U_i`
   (`qCornerSliceAtUnits`), NOT the multiplicative `radialAttach` (one shared divisor → the MIN
   `min_i (h_i+1)/2 = 3/2` undershoot, banked `sjSlice334_symmetric_undershoot`). The charges ADD:
   `½·Σ_i(h_i+1)`.
2. **The `{U_i=0}` locus is integrated JOINTLY with its transverse charge, NOT deleted.** A vanishing
   unit is a GENUINE RLCT-collapse (Codex-exhibited: `D=1 → λ = 2 < 7/2`, or `λ=1/2`). It is rescued
   ONLY by the proved product-rank tube charge `D_q` (#127), here encoded as the per-block deep-codim
   hypothesis `h_i ≤ m_i` (`d_k = m_k+1 ≥ h_k+1`); the units enter as squared deep-data norms
   `U_i = ‖X_i‖²` and the weighted AM-GM at the min-cut weights `w_i = (h_i+1)/Σ(h_j+1)` decouples the
   `u`-charge from the deep-block codim, both binding at the SAME `c' < ½·Σ(h_j+1)`.

## What lands here

* **`qCornerSliceAtUnits`** — the `q`-block additive corner slice `∫_{[0,1]^q} (Σ_i u_i²U_i)^{−c'}·∏|u_i|^{h_i}`.
  `qCornerSliceAtUnits_two_eq` — the fidelity bridge: at `q=2` it is the banked `cornerSliceAtUnits`.
* **`qCornerSliceAtUnits_le`** — the `q`-ary weighted-AM-GM decoupling (generalizes `cornerSliceAtUnits_le`
  via `Real.geom_mean_le_arith_mean_weighted`). [HOLE — the q-ary pointwise AM-GM + separation]
* **`qPeelIntegral`, `qPeelIntegral_lt_top`** — the joint integral over the deep boxes and its finiteness
  for `c' < ½·Σ(h_i+1)` under the per-block codim gate `h_i ≤ m_i`. Generalizes `onePeelIntegral_lt_top`.
  [HOLE — the q-fold Tonelli into the deep-Morse boxes + the u-monomial box, per cert §2/§4(iii)]
* **`qPeel_threshold_eq_half_minAdm_334`** — the charge anchor: at `q=2`, `½·Σ(![3,2]_i+1) = 7/2 = ½·minAdm(3,3,3,4)`.

The corank-2 rung is banked end-to-end (`corner334` fixed-slice + `onePeel334` joint); this module lifts
the JOINT rung to general `q` — the `(q−1)`-fold iteration is folded into the single `q`-ary AM-GM +
`q`-fold Tonelli (the cert's "iterated corner blow-up" realized as one weighted-AM-GM decoupling).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Real
open scoped ENNReal BigOperators

/-! ## 1. The `q`-block additive corner slice -/

/-- **The `q`-block additive corner slice at explicit units.** `∫_{[0,1]^q} (Σ_i u_i²·U_i)^{−c'}·∏_i|u_i|^{h_i}`
— the ADDITIVE (block-diagonal) corner (cert §1); the `q=2` case is the banked `cornerSliceAtUnits`. -/
noncomputable def qCornerSliceAtUnits (q : ℕ) (h : Fin q → ℕ) (U : Fin q → ℝ) (c' : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in unitBox q,
    ENNReal.ofReal ((∑ i, u i ^ 2 * U i) ^ (-c') * ∏ i, |u i| ^ (h i))

/-- **Fidelity bridge (q = 2).** `qCornerSliceAtUnits 2 ![h0,h1] ![U0,U1]` is the banked two-block
`cornerSliceAtUnits h0 h1 U0 U1` (the `Fin 2` sum/product unfold). -/
theorem qCornerSliceAtUnits_two_eq (h0 h1 : ℕ) (U0 U1 : ℝ) (c' : ℝ) :
    qCornerSliceAtUnits 2 ![h0, h1] ![U0, U1] c' = cornerSliceAtUnits h0 h1 U0 U1 c' := by
  unfold qCornerSliceAtUnits cornerSliceAtUnits
  refine lintegral_congr (fun u => ?_)
  congr 1
  rw [Fin.sum_univ_two, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-! ## 2. The `q`-ary weighted-AM-GM decoupling (soundness piece 1: ADD, not MIN) -/

/-- **The `q`-ary weighted-AM-GM slice bound (the codim-decoupling).** For strictly positive units `U_i`
and min-cut weights `w_i ≥ 0` summing to `1`, the additive corner slice is dominated by a product of a
deep-unit power in each block times a separated `u`-monomial box integral. The pointwise engine is the
`q`-ary weighted AM-GM `∏(u_i²U_i)^{w_i} ≤ Σ w_i u_i²U_i ≤ Σ u_i²U_i`
(`Real.geom_mean_le_arith_mean_weighted`), generalizing the banked two-block `cornerSliceAtUnits_le`.
The deep powers `∏ U_i^{−w_i c'}` factor out (constant in `u`), leaving the `u`-monomial that carries
the binding threshold. -/
theorem qCornerSliceAtUnits_le (q : ℕ) (h : Fin q → ℕ) (c' : ℝ) (hc0 : 0 ≤ c')
    (w : Fin q → ℝ) (hw : ∀ i, 0 ≤ w i) (hwle : ∀ i, w i ≤ 1) (hwsum : ∑ i, w i = 1)
    (U : Fin q → ℝ) (hU : ∀ i, 0 < U i) :
    qCornerSliceAtUnits q h U c'
      ≤ (∏ i, ENNReal.ofReal (U i ^ (-(w i * c'))))
        * ∫⁻ u in Set.univ.pi (fun _ : Fin q => Set.Ioo (0 : ℝ) 1),
            ENNReal.ofReal (∏ i, |u i| ^ ((h i : ℝ) - 2 * w i * c')) := by
  unfold qCornerSliceAtUnits
  rw [restrict_unitBox_eq_open q]
  -- pointwise domination on the open box (all `u_i > 0`), via the q-ary weighted AM-GM
  have hbound : (fun u : Fin q → ℝ =>
        ENNReal.ofReal ((∑ i, u i ^ 2 * U i) ^ (-c') * ∏ i, |u i| ^ (h i)))
      ≤ᵐ[volume.restrict (Set.univ.pi (fun _ : Fin q => Set.Ioo (0 : ℝ) 1))]
      (fun u : Fin q → ℝ =>
        ENNReal.ofReal (∏ i, U i ^ (-(w i * c')))
          * ENNReal.ofReal (∏ i, |u i| ^ ((h i : ℝ) - 2 * w i * c'))) := by
    refine ae_restrict_of_forall_mem (MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)) ?_
    intro u hu
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at hu
    have hupos : ∀ i, 0 < u i := fun i => (hu i).1
    dsimp only
    rw [← ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hU i).le _))]
    apply ENNReal.ofReal_le_ofReal
    -- notation: `z i = u_i² U_i > 0`, `P = ∏ z_i^{w_i} > 0`, and `P ≤ Σ z_i` (AM-GM + w ≤ 1)
    have hz : ∀ i, 0 < u i ^ 2 * U i := fun i => mul_pos (pow_pos (hupos i) 2) (hU i)
    have hgm : ∏ i, (u i ^ 2 * U i) ^ w i ≤ ∑ i, w i * (u i ^ 2 * U i) :=
      Real.geom_mean_le_arith_mean_weighted Finset.univ w (fun i => u i ^ 2 * U i)
        (fun i _ => hw i) hwsum (fun i _ => (hz i).le)
    have hwle_sum : ∑ i, w i * (u i ^ 2 * U i) ≤ ∑ i, u i ^ 2 * U i :=
      Finset.sum_le_sum (fun i _ => by
        have := (hz i).le
        nlinarith [hwle i, this])
    have hPpos : 0 < ∏ i, (u i ^ 2 * U i) ^ w i :=
      Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hz i) _)
    have hPS : ∏ i, (u i ^ 2 * U i) ^ w i ≤ ∑ i, u i ^ 2 * U i := le_trans hgm hwle_sum
    have hrp : (∑ i, u i ^ 2 * U i) ^ (-c')
        ≤ (∏ i, (u i ^ 2 * U i) ^ w i) ^ (-c') :=
      Real.rpow_le_rpow_of_nonpos hPpos hPS (by linarith)
    -- per-factor expansion `((u_i²U_i)^{w_i})^{−c'} = U_i^{−w_i c'} · |u_i|^{−2 w_i c'}`
    have hfac : ∀ i, ((u i ^ 2 * U i) ^ w i) ^ (-c')
        = U i ^ (-(w i * c')) * |u i| ^ (-(2 * w i * c')) := by
      intro i
      have hui : (0 : ℝ) ≤ u i := (hupos i).le
      have hu2U : (0 : ℝ) ≤ u i ^ 2 * U i := (hz i).le
      rw [abs_of_pos (hupos i), ← Real.rpow_mul hu2U,
        Real.mul_rpow (sq_nonneg (u i)) (hU i).le,
        ← Real.rpow_natCast (u i) 2, ← Real.rpow_mul hui, mul_comm]
      congr 1
      · congr 1; ring
      · congr 1; push_cast; ring
    -- expand `P^{−c'} = (∏ U_i^{−w_i c'}) · ∏ |u_i|^{−2 w_i c'}`
    have hPexp : (∏ i, (u i ^ 2 * U i) ^ w i) ^ (-c')
        = (∏ i, U i ^ (-(w i * c'))) * ∏ i, |u i| ^ (-(2 * w i * c')) :=
      calc (∏ i, (u i ^ 2 * U i) ^ w i) ^ (-c')
          = ∏ i, ((u i ^ 2 * U i) ^ w i) ^ (-c') :=
            (Real.finset_prod_rpow Finset.univ (fun i => (u i ^ 2 * U i) ^ w i)
              (fun i _ => Real.rpow_nonneg (hz i).le _) (-c')).symm
        _ = ∏ i, (U i ^ (-(w i * c')) * |u i| ^ (-(2 * w i * c'))) :=
            Finset.prod_congr rfl (fun i _ => hfac i)
        _ = (∏ i, U i ^ (-(w i * c'))) * ∏ i, |u i| ^ (-(2 * w i * c')) :=
            Finset.prod_mul_distrib
    -- fold the Jacobian `∏ |u_i|^{h_i}` into `∏ |u_i|^{h_i − 2 w_i c'}`
    have hjac : (∏ i, |u i| ^ (-(2 * w i * c'))) * ∏ i, |u i| ^ (h i)
        = ∏ i, |u i| ^ ((h i : ℝ) - 2 * w i * c') := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [← Real.rpow_natCast (|u i|) (h i),
        ← Real.rpow_add (abs_pos.mpr (ne_of_gt (hupos i)))]
      congr 1; push_cast; ring
    calc (∑ i, u i ^ 2 * U i) ^ (-c') * ∏ i, |u i| ^ (h i)
        ≤ (∏ i, (u i ^ 2 * U i) ^ w i) ^ (-c') * ∏ i, |u i| ^ (h i) :=
          mul_le_mul_of_nonneg_right hrp (Finset.prod_nonneg (fun i _ => by positivity))
      _ = (∏ i, U i ^ (-(w i * c'))) * ((∏ i, |u i| ^ (-(2 * w i * c'))) * ∏ i, |u i| ^ (h i)) := by
          rw [hPexp]; ring
      _ = (∏ i, U i ^ (-(w i * c'))) * ∏ i, |u i| ^ ((h i : ℝ) - 2 * w i * c') := by rw [hjac]
  calc ∫⁻ u in Set.univ.pi (fun _ : Fin q => Set.Ioo (0 : ℝ) 1),
          ENNReal.ofReal ((∑ i, u i ^ 2 * U i) ^ (-c') * ∏ i, |u i| ^ (h i))
      ≤ ∫⁻ u in Set.univ.pi (fun _ : Fin q => Set.Ioo (0 : ℝ) 1),
          ENNReal.ofReal (∏ i, U i ^ (-(w i * c')))
            * ENNReal.ofReal (∏ i, |u i| ^ ((h i : ℝ) - 2 * w i * c')) := lintegral_mono_ae hbound
    _ = ENNReal.ofReal (∏ i, U i ^ (-(w i * c')))
          * ∫⁻ u in Set.univ.pi (fun _ : Fin q => Set.Ioo (0 : ℝ) 1),
            ENNReal.ofReal (∏ i, |u i| ^ ((h i : ℝ) - 2 * w i * c')) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = (∏ i, ENNReal.ofReal (U i ^ (-(w i * c'))))
          * ∫⁻ u in Set.univ.pi (fun _ : Fin q => Set.Ioo (0 : ℝ) 1),
            ENNReal.ofReal (∏ i, |u i| ^ ((h i : ℝ) - 2 * w i * c')) := by
        rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (hU i).le _)]

/-! ## 3. The joint integral over the deep data + its finiteness (soundness piece 2: transverse charge) -/

/-- **The `q`-block joint peel integral.** The `q`-block corner slice with each unit cast as the squared
Euclidean norm `U_i = ∑_j (X i j)²` of a deep-data block `X i ∈ [−T,T]^{m_i+1}`, integrated over the
product of deep boxes. This is the corner slice integrated over the deep data JOINTLY (cert §2, the
`{U_i=0}` locus NOT deleted); the blocks are the orthogonal deep coordinates. Generalizes
`onePeelIntegral` from 2 blocks to `q`. -/
noncomputable def qPeelIntegral (q : ℕ) (h m : Fin q → ℕ) (T c' : ℝ) : ℝ≥0∞ :=
  ∫⁻ X in Set.univ.pi (fun i => morseBox (m i + 1) T),
    qCornerSliceAtUnits q h (fun i => ∑ j, (X i) j ^ 2) c'

/-- **The corank-`q` joint finiteness (route S headline).** The joint peel integral is finite for every
`c' < ½·Σ_i(h_i+1)` as soon as every block's vanishing-locus codimension is full enough — the per-block
gate `h_i ≤ m_i` (`d_i = m_i+1 ≥ h_i+1`), which is the PROVED transverse product-rank charge `D_q`
(#127) supplied per collapse direction. The binding threshold `½·Σ(h_i+1) = ½(D_q+d_q)` comes from the
`u`-marginals; the deep Morse integrals (the codim rescue) are non-binding under the gate. Proof:
`q`-ary weighted AM-GM at the min-cut weights `w_i=(h_i+1)/Σ(h_j+1)` (`qCornerSliceAtUnits_le`) + `q`-fold
Tonelli factoring into the `q` deep-Morse box integrals and the `u`-monomial box integral. -/
theorem qPeelIntegral_lt_top (q : ℕ) (h m : Fin q → ℕ) (hcod : ∀ i, h i ≤ m i)
    (T : ℝ) (hT : 0 < T) (c' : ℝ) (hc0 : 0 ≤ c')
    (hc' : c' < (∑ i, ((h i : ℝ) + 1)) / 2) :
    qPeelIntegral q h m T c' < ⊤ := by
  -- `q = 0` is vacuous (`hc'` forces `c' < 0`, contra `hc0`)
  rcases Nat.eq_zero_or_pos q with hq | hq
  · exfalso; subst hq; simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_div] at hc'; linarith
  haveI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  -- min-cut weights `w i = (h i + 1) / s`, `s = Σ (h j + 1)`
  set s : ℝ := ∑ i, ((h i : ℝ) + 1) with hs_def
  have hs : 0 < s := Finset.sum_pos (fun i _ => by positivity) Finset.univ_nonempty
  set w : Fin q → ℝ := fun i => ((h i : ℝ) + 1) / s with hw_def
  have hw : ∀ i, 0 ≤ w i := fun i => by rw [hw_def]; positivity
  have hwsum : ∑ i, w i = 1 := by
    rw [hw_def]; simp only; rw [← Finset.sum_div, ← hs_def, div_self (ne_of_gt hs)]
  have hwpos : ∀ i, 0 < w i := fun i => by rw [hw_def]; positivity
  have hwle : ∀ i, w i ≤ 1 := by
    intro i; rw [hw_def]; simp only
    rw [div_le_one hs]
    calc (h i : ℝ) + 1 ≤ ∑ j, ((h j : ℝ) + 1) :=
          Finset.single_le_sum (f := fun j => (h j : ℝ) + 1) (fun j _ => by positivity)
            (Finset.mem_univ i)
      _ = s := hs_def.symm
  have h2cs : 2 * c' < s := by rw [hs_def]; linarith [hc']
  -- axis-exponent bound `2 w_i c' < h_i + 1` and the codim threshold `w_i c' < (m_i+1)/2`
  have hw2 : ∀ i, 2 * w i * c' < (h i : ℝ) + 1 := by
    intro i
    have hws : w i * s = (h i : ℝ) + 1 := by rw [hw_def]; field_simp
    have hstep : w i * (2 * c') < w i * s := mul_lt_mul_of_pos_left h2cs (hwpos i)
    rw [hws] at hstep; nlinarith [hstep]
  have hwm : ∀ i, w i * c' < ((m i : ℝ) + 1) / 2 := by
    intro i
    have hle : (h i : ℝ) + 1 ≤ (m i : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right (hcod i) 1
    nlinarith [hw2 i, hle]
  have he : ∀ i, (-1 : ℝ) < (h i : ℝ) - 2 * w i * c' := fun i => by linarith [hw2 i]
  -- the `u`-monomial box factor `Iu < ⊤`
  set Iu : ℝ≥0∞ := ∫⁻ u in Set.univ.pi (fun _ : Fin q => Set.Ioo (0 : ℝ) 1),
      ENNReal.ofReal (∏ i, |u i| ^ ((h i : ℝ) - 2 * w i * c')) with hIu_def
  have hIu : Iu < ⊤ := by
    rw [hIu_def]
    exact prod_rpow_lintegral_Ioo_box_lt_top 1 one_pos (fun i => (h i : ℝ) - 2 * w i * c') he
  set boxPi : Set ((i : Fin q) → (Fin (m i + 1) → ℝ)) :=
    Set.univ.pi (fun i => morseBox (m i + 1) T) with hboxPi_def
  -- the deep-block product integral is finite (bridge to `Integrable.fin_nat_prod`)
  have hbox : ∫⁻ X in boxPi,
      ∏ i, ENNReal.ofReal ((∑ j, (X i) j ^ 2) ^ (-(w i * c'))) < ⊤ := by
    set G : (i : Fin q) → (Fin (m i + 1) → ℝ) → ℝ :=
      fun i Xi => (∑ j, (Xi) j ^ 2) ^ (-(w i * c')) with hG_def
    have hGnn : ∀ i (Xi : Fin (m i + 1) → ℝ), 0 ≤ G i Xi :=
      fun i Xi => Real.rpow_nonneg (by positivity) _
    have hGint : ∀ i, Integrable (G i) (volume.restrict (morseBox (m i + 1) T)) := by
      intro i
      have hmeas : Measurable (G i) := by rw [hG_def]; fun_prop
      refine ⟨hmeas.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun Xi => hGnn i Xi))]
      exact sumSqND_box_lt_top (m i) T hT (w i * c') (hwm i)
    have hint : Integrable (fun X => ∏ i, G i (X i)) (volume.restrict boxPi) := by
      rw [hboxPi_def, MeasureTheory.volume_pi, Measure.restrict_pi_pi]
      exact Integrable.fin_nat_prod hGint
    have hPnn : 0 ≤ᵐ[volume.restrict boxPi] (fun X => ∏ i, G i (X i)) :=
      Filter.Eventually.of_forall (fun X => Finset.prod_nonneg (fun i _ => hGnn i (X i)))
    calc ∫⁻ X in boxPi, ∏ i, ENNReal.ofReal ((∑ j, (X i) j ^ 2) ^ (-(w i * c')))
        = ∫⁻ X in boxPi, ENNReal.ofReal (∏ i, G i (X i)) := by
          refine lintegral_congr (fun X => ?_)
          rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hGnn i (X i))]
      _ = ENNReal.ofReal (∫ X in boxPi, ∏ i, G i (X i)) :=
          (ofReal_integral_eq_lintegral_ofReal hint hPnn).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  -- a.e. every deep block is nonzero (the `{U_i = 0}` locus is null; NOT deleted — integrated jointly)
  have hae : ∀ᵐ X ∂(volume.restrict boxPi), ∀ i, (∑ j, (X i) j ^ 2) ≠ 0 := by
    refine ae_restrict_of_ae ?_
    rw [MeasureTheory.volume_pi]
    have hnull : ∀ i, Measure.pi (fun i => (volume : Measure (Fin (m i + 1) → ℝ)))
        {X | (∑ j, (X i) j ^ 2) = 0} = 0 := by
      intro i
      have hset : {X : (i : Fin q) → (Fin (m i + 1) → ℝ) | (∑ j, (X i) j ^ 2) = 0}
          = (Function.eval i) ⁻¹' {v : Fin (m i + 1) → ℝ | (∑ j, v j ^ 2) = 0} := rfl
      rw [hset]
      refine Measure.pi_eval_preimage_null _ ?_
      have hsingle : {v : Fin (m i + 1) → ℝ | (∑ j, v j ^ 2) = 0} = {0} := by
        ext v
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)]
        constructor
        · intro hv; funext j; exact pow_eq_zero_iff (by norm_num) |>.1 (hv j (Finset.mem_univ j))
        · intro hv j _; rw [hv]; simp
      rw [hsingle]; exact measure_singleton 0
    rw [ae_iff]
    refine measure_mono_null (fun X hX => ?_) (measure_iUnion_null (fun i => hnull i))
    simp only [Set.mem_setOf_eq, not_forall, not_not] at hX
    obtain ⟨i, hi⟩ := hX
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  -- assemble: AM-GM decoupling (a.e.), pull `Iu` out, both factors finite
  calc qPeelIntegral q h m T c'
      = ∫⁻ X in boxPi, qCornerSliceAtUnits q h (fun i => ∑ j, (X i) j ^ 2) c' := rfl
    _ ≤ ∫⁻ X in boxPi,
          (∏ i, ENNReal.ofReal ((∑ j, (X i) j ^ 2) ^ (-(w i * c')))) * Iu := by
        refine lintegral_mono_ae (hae.mono (fun X hX => ?_))
        exact qCornerSliceAtUnits_le q h c' hc0 w hw hwle hwsum (fun i => ∑ j, (X i) j ^ 2)
          (fun i => lt_of_le_of_ne (by positivity) (Ne.symm (hX i)))
    _ = (∫⁻ X in boxPi, ∏ i, ENNReal.ofReal ((∑ j, (X i) j ^ 2) ^ (-(w i * c')))) * Iu :=
        lintegral_mul_const' _ _ hIu.ne
    _ < ⊤ := ENNReal.mul_lt_top hbox hIu

/-! ## 4. Fidelity + charge anchors -/

/-- **Charge anchor (q = 2, `(3,3,3,4)`).** The corank-2 threshold `½·Σ_i(![3,2]_i+1) = 7/2` equals
`½·minAdm(3,3,3,4)` — the additive charges reproduce the banked `onePeel334` threshold. -/
theorem qPeel_threshold_eq_half_minAdm_334 :
    (∑ i, (((![3, 2] : Fin 2 → ℕ) i : ℝ) + 1)) / 2 = (minAdm (![3, 3, 3, 4] : Fin 4 → ℕ) : ℝ) / 2 := by
  rw [sjSlice334_minAdm_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  norm_num

/-- **Non-vacuity of the threshold form.** For a nonempty collapse set the additive threshold is
positive, so the finiteness claim is not vacuous. -/
example : (0 : ℝ) < (∑ i, (((![3, 2] : Fin 2 → ℕ) i : ℝ) + 1)) / 2 := by
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  norm_num

/-- **Per-block codim anchor (q = 2, `(3,3,3,4)`) — obligation-1 concrete.** The corank-2 joint peel
integral is finite for every `c' < 7/2` at the GENUINE PER-DIRECTION codims `m = ![7,3]` — `m₀ = 7`
(the `(w₁,w₂)`-block) and `m₁ = 3` (the `v̄`-block), each carrying its OWN product-rank codim (#127's
per-direction `D_q`), NOT an unallocated total nor a uniform `max`. This is the per-block allocation the
reshape/casting must respect (else the product-vs-free `7/2` vs `9/2` distinction is lost); it reproduces
the banked `onePeel334_cleanCoords_lt_top` threshold. The gate `hcod` here is `3 ≤ 7 ∧ 2 ≤ 3` — each
Jacobian power `h_i` bounded by its own block codim `m_i`. -/
theorem qPeel_334_lt_top (T : ℝ) (hT : 0 < T) (c' : ℝ) (hc0 : 0 ≤ c') (hc' : c' < 7 / 2) :
    qPeelIntegral 2 ![3, 2] ![7, 3] T c' < ⊤ := by
  refine qPeelIntegral_lt_top 2 ![3, 2] ![7, 3] (fun i => by fin_cases i <;> norm_num)
    T hT c' hc0 ?_
  have hsum : (∑ i, (((![3, 2] : Fin 2 → ℕ) i : ℝ) + 1)) = 7 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    norm_num
  rw [hsum]; exact hc'

end DLNFibre.DLN.RLCT
