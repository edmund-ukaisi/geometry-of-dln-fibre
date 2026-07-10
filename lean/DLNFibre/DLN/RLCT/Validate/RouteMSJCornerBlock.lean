import DLNFibre.DLN.RLCT.Validate.RouteMSJMonomialLower
import Mathlib.Analysis.MeanInequalities

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJCornerBlock` — the `Fin d`-block corner-blow-up finiteness

**Thread `genm-corndblock`.** The **width-general (`Fin d`)** binding-corner endpoint for a
depth-`d` flag: the `d`-block generalization of the banked TWO-block corner-blow-up crux
`RouteMSJSlice334.sjSlice_corner_two_block_lt_top`.

## The corner model

After the `d` radial blow-ups of block dimensions `hᵢ+1` (each contributing an accumulated Jacobian
power `hᵢ` and a loss term of radial order `2`, all sharing the deep factor), the binding corner
`u₀ = ⋯ = u_{d-1} = 0` carries the local model

    G  ≃  ∑ᵢ uᵢ² · Uᵢ,          measure  (∏ᵢ |uᵢ|^{hᵢ}) du,

with residual **units** `Uᵢ` bounded below by a positive constant `a` on the generic-downstream
chart (the §8 brick, supplied here as the hypothesis `a ≤ Uᵢ`, exactly as the banked terminal
endpoint supplies its `hunit`).

## The threshold `½·∑(hᵢ+1)` (= ½·codim-sum) and why the corner binds

Looking at a single face `{uᵢ=0}` in isolation gives the misleading boundary abscissa `(hᵢ+1)/2`;
their minimum is the multi-matrix engine's **undershoot**. The binding zero is the **corner**
`u = 0`, where all `d` codimensions ADD: the corner blow-up accumulates the Jacobian powers onto ONE
terminal divisor while the loss stays order `2`, giving the branch threshold `½·∑ᵢ(hᵢ+1)`.

## The Lean realisation — `d`-ary weighted AM-GM to a separated monomial

Rather than perform the general-width change-of-variables Jacobian explicitly (the deferred
mountain), the corner is resolved analytically by **weighted** AM-GM with the min-cut weights
`wᵢ = (hᵢ+1)/∑ⱼ(hⱼ+1)`:

    ∑ᵢ uᵢ²  ≥  ∑ᵢ wᵢ uᵢ²  ≥  ∏ᵢ (uᵢ²)^{wᵢ}  =  ∏ᵢ |uᵢ|^{2wᵢ},

so `(∑ᵢ uᵢ²·Uᵢ)^{−c'}` (after the units' lower bound `a`) is dominated by the **separated** monomial
`∏ᵢ |uᵢ|^{−2wᵢc'}`, and the integrand by `∏ᵢ |uᵢ|^{hᵢ−2wᵢc'}` — landing on the banked
`RouteMSJMonomialLower.prod_rpow_lintegral_Ioo_box_lt_top`. Each axis exponent `hᵢ−2wᵢc'` exceeds
`−1` **iff** `2wᵢc' < hᵢ+1`, i.e. `c' < ½·∑ⱼ(hⱼ+1)` — the weights `wᵢ` are exactly the direction
where all `d` axis constraints coincide at that threshold. This is the analytic form of "the
codimensions add on the terminal exceptional divisor".

S2-FREE: no `monomial_rlct`, no `cited_aoyagi_dln`. The `rlct = ½·codim` reading stays Cited; this
proves box-finiteness at the branch threshold only. Axiom-clean `[propext, Classical.choice,
Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Real
open scoped ENNReal BigOperators

/-- **The width-general (`Fin d`) corner-blow-up finiteness.** For `d` radial blow-ups of block
dimensions `hᵢ+1` (accumulated Jacobian powers `hᵢ`, each loss term of radial order `2`) sharing the
deep factor, the binding corner local model `(∑ᵢ uᵢ²·Uᵢ)^{−c'}` with Jacobian `∏ᵢ |uᵢ|^{hᵢ}` and
residual units `Uᵢ` bounded below by `a>0` has finite `∫⁻` over the unit box for every
`c' < ½·∑ᵢ(hᵢ+1)` — the branch threshold where all `d` codimensions ADD. Proof: dominate by the
separated monomial via weighted AM-GM at the **min-cut weights** `wᵢ = (hᵢ+1)/∑ⱼ(hⱼ+1)`, the unique
direction where every axis constraint coincides at `½·∑ⱼ(hⱼ+1)`; the dominator is box-integrable
there (`prod_rpow_lintegral_Ioo_box_lt_top`). This is the analytic form of "the codimensions add on
the terminal exceptional divisor".

All `d` lower bounds `a ≤ Uᵢ` are needed — each corner chart `uⱼ = u_i·τ` needs `Uᵢ > 0`. (The
constant `a` is the unit lower-bound, distinct from any chart pivot scalar.) The width-general
change-of-variables Jacobian is bypassed: the weighted-AM-GM domination is Jacobian-free. -/
theorem sjSlice_corner_block_lt_top (d : ℕ) (h : Fin d → ℕ)
    (c' : NNReal) (hc' : (c' : ℝ) < (∑ i, ((h i : ℝ) + 1)) / 2)
    (U : Fin d → (Fin d → ℝ) → ℝ) (a : ℝ) (ha : 0 < a)
    (hU : ∀ i, ∀ u ∈ unitBox d, a ≤ U i u) :
    ∫⁻ u in unitBox d,
        ENNReal.ofReal ((∑ i, u i ^ 2 * U i u) ^ (-(c' : ℝ))
          * (∏ i, |u i| ^ h i)) < ⊤ := by
  set cc : ℝ := (c' : ℝ) with hcc_def
  have hcc0 : 0 ≤ cc := c'.coe_nonneg
  set s : ℝ := ∑ i, ((h i : ℝ) + 1) with hs_def
  have hs : 0 < s := by linarith
  have hsne : s ≠ 0 := ne_of_gt hs
  -- min-cut weights `wᵢ = (hᵢ+1)/s`
  set w : Fin d → ℝ := fun i => ((h i : ℝ) + 1) / s with hw_def
  have hwpos : ∀ i, 0 < w i := fun i => by simp only [hw_def]; positivity
  have hwsum : ∑ i, w i = 1 := by
    simp only [hw_def, ← Finset.sum_div, ← hs_def]
    exact div_self hsne
  have hwle : ∀ i, w i ≤ 1 := fun i => by
    rw [hw_def, div_le_one hs, hs_def]
    exact Finset.single_le_sum (f := fun j => (h j : ℝ) + 1)
      (fun j _ => by positivity) (Finset.mem_univ i)
  -- axis-exponent bounds `2·wᵢ·c' < hᵢ+1` (⟺ `c' < s/2 = ½·∑(hⱼ+1)`)
  have h2ccs : 2 * cc < s := by linarith
  have hws : ∀ i, w i * s = (h i : ℝ) + 1 := fun i => by simp only [hw_def]; field_simp
  have hwlt : ∀ i, 2 * w i * cc < (h i : ℝ) + 1 := fun i => by
    have hstep : w i * (2 * cc) < w i * s := mul_lt_mul_of_pos_left h2ccs (hwpos i)
    rw [hws i] at hstep; nlinarith [hstep]
  -- the separated-monomial axis exponents `eᵢ = hᵢ − 2wᵢc'`, all `> −1`
  set e : Fin d → ℝ := fun i => (h i : ℝ) - 2 * w i * cc with he_def
  have he : ∀ i, (-1 : ℝ) < e i := fun i => by simp only [he_def]; linarith [hwlt i]
  -- the dominating separated-monomial integral is finite on the open box
  have hfin : ∫⁻ u in Set.univ.pi (fun _ : Fin d => Set.Ioo (0 : ℝ) 1),
      ENNReal.ofReal (∏ j, |u j| ^ (e j)) < ⊤ :=
    prod_rpow_lintegral_Ioo_box_lt_top 1 one_pos e he
  rw [restrict_unitBox_eq_open d]
  -- pointwise domination `ofReal (F u) ≤ ofReal (a^{-c'}) · ofReal (∏ⱼ |uⱼ|^{eⱼ})` on the open box
  have hbound : (fun u => ENNReal.ofReal
        ((∑ i, u i ^ 2 * U i u) ^ (-cc) * (∏ i, |u i| ^ h i)))
      ≤ᵐ[volume.restrict (Set.univ.pi (fun _ : Fin d => Set.Ioo (0 : ℝ) 1))]
      (fun u => ENNReal.ofReal (a ^ (-cc)) * ENNReal.ofReal (∏ j, |u j| ^ (e j))) := by
    refine ae_restrict_of_forall_mem (MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)) ?_
    intro u hu
    dsimp only
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at hu
    have hupos : ∀ i, 0 < u i := fun i => (hu i).1
    have hX : ∀ i, 0 < |u i| := fun i => abs_pos.mpr (ne_of_gt (hupos i))
    have hsqX : ∀ i, u i ^ 2 = |u i| ^ 2 := fun i => (sq_abs (u i)).symm
    have humem : u ∈ unitBox d := by
      simp only [unitBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
      intro j; exact ⟨(hu j).1.le, (hu j).2.le⟩
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ a ^ (-cc))]
    apply ENNReal.ofReal_le_ofReal
    -- `d`-ary weighted AM-GM at the min-cut weights: `∏ᵢ |uᵢ|^{2wᵢ} ≤ ∑ᵢ |uᵢ|²`
    have hgm : ∏ i, |u i| ^ (2 * w i) ≤ ∑ i, |u i| ^ 2 := by
      have hbase := Real.geom_mean_le_arith_mean_weighted Finset.univ w (fun i => |u i| ^ 2)
        (fun i _ => (hwpos i).le) hwsum (fun i _ => sq_nonneg _)
      have e1 : ∀ i, (|u i| ^ 2 : ℝ) ^ (w i) = |u i| ^ (2 * w i) := fun i => by
        rw [← Real.rpow_natCast (|u i|) 2, ← Real.rpow_mul (abs_nonneg _)]; norm_num
      calc ∏ i, |u i| ^ (2 * w i)
          = ∏ i, (|u i| ^ 2 : ℝ) ^ (w i) := Finset.prod_congr rfl (fun i _ => (e1 i).symm)
        _ ≤ ∑ i, w i * (|u i| ^ 2 : ℝ) := hbase
        _ ≤ ∑ i, |u i| ^ 2 :=
            Finset.sum_le_sum (fun i _ => mul_le_of_le_one_left (sq_nonneg _) (hwle i))
    -- lower bound on the loss base
    have hbb : a * (∏ i, |u i| ^ (2 * w i)) ≤ ∑ i, u i ^ 2 * U i u := by
      calc a * (∏ i, |u i| ^ (2 * w i))
          ≤ a * (∑ i, |u i| ^ 2) := mul_le_mul_of_nonneg_left hgm ha.le
        _ = ∑ i, a * |u i| ^ 2 := by rw [Finset.mul_sum]
        _ ≤ ∑ i, u i ^ 2 * U i u := Finset.sum_le_sum (fun i _ => by
              rw [hsqX i, mul_comm a (|u i| ^ 2)]
              exact mul_le_mul_of_nonneg_left (hU i u humem) (sq_nonneg _))
    have hprodnn : (0 : ℝ) ≤ ∏ i, |u i| ^ (2 * w i) :=
      Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
    have hbpos : 0 < a * (∏ i, |u i| ^ (2 * w i)) :=
      mul_pos ha (Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hX i) _))
    -- rpow antitone at exponent `−c' ≤ 0`
    have hrp : (∑ i, u i ^ 2 * U i u) ^ (-cc)
        ≤ (a * (∏ i, |u i| ^ (2 * w i))) ^ (-cc) :=
      Real.rpow_le_rpow_of_nonpos hbpos hbb (by linarith)
    -- expand the dominating power × the Jacobian into the separated monomial
    have hexp : (a * ∏ i, |u i| ^ (2 * w i)) ^ (-cc) * (∏ i, |u i| ^ h i)
        = a ^ (-cc) * ∏ i, |u i| ^ (e i) := by
      rw [Real.mul_rpow ha.le hprodnn,
        ← Real.finset_prod_rpow Finset.univ (fun i => |u i| ^ (2 * w i))
          (fun i _ => Real.rpow_nonneg (abs_nonneg _) _) (-cc),
        mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      rw [← Real.rpow_mul (abs_nonneg (u i)), ← Real.rpow_natCast (|u i|) (h i),
        ← Real.rpow_add (hX i),
        show 2 * w i * -cc + ((h i : ℕ) : ℝ) = e i from by simp only [he_def]; ring]
    calc (∑ i, u i ^ 2 * U i u) ^ (-cc) * (∏ i, |u i| ^ h i)
        ≤ (a * ∏ i, |u i| ^ (2 * w i)) ^ (-cc) * (∏ i, |u i| ^ h i) :=
          mul_le_mul_of_nonneg_right hrp (by positivity)
      _ = a ^ (-cc) * ∏ i, |u i| ^ (e i) := hexp
  calc ∫⁻ u in Set.univ.pi (fun _ : Fin d => Set.Ioo (0 : ℝ) 1),
          ENNReal.ofReal ((∑ i, u i ^ 2 * U i u) ^ (-cc) * (∏ i, |u i| ^ h i))
      ≤ ∫⁻ u in Set.univ.pi (fun _ : Fin d => Set.Ioo (0 : ℝ) 1),
          ENNReal.ofReal (a ^ (-cc)) * ENNReal.ofReal (∏ j, |u j| ^ (e j)) :=
        lintegral_mono_ae hbound
    _ = ENNReal.ofReal (a ^ (-cc)) * ∫⁻ u in Set.univ.pi (fun _ : Fin d => Set.Ioo (0 : ℝ) 1),
          ENNReal.ofReal (∏ j, |u j| ^ (e j)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-- **Recovery of the banked TWO-block corner crux.** Instantiating the width-general
`sjSlice_corner_block_lt_top` at `d = 2` with `h = ![h₀,h₁]`, `U = ![U₀,U₁]` reproduces the banked
`RouteMSJSlice334.sjSlice_corner_two_block_lt_top` statement verbatim (the explicit two-term sum
`u₀²·U₀ + u₁²·U₁` and the two-factor Jacobian `|u₀|^{h₀}·|u₁|^{h₁}`), at the same threshold
`(h₀+h₁+2)/2 = ½·∑(hᵢ+1)`. This certifies the generalization subsumes the 2-block case. -/
theorem sjSlice_corner_block_recovers_two_block (h0 h1 : ℕ)
    (c' : NNReal) (hc' : (c' : ℝ) < ((h0 : ℝ) + (h1 : ℝ) + 2) / 2)
    (U0 U1 : (Fin 2 → ℝ) → ℝ) (a : ℝ) (ha : 0 < a)
    (hU0 : ∀ u ∈ unitBox 2, a ≤ U0 u) (hU1 : ∀ u ∈ unitBox 2, a ≤ U1 u) :
    ∫⁻ u in unitBox 2,
        ENNReal.ofReal ((u 0 ^ 2 * U0 u + u 1 ^ 2 * U1 u) ^ (-(c' : ℝ))
          * (|u 0| ^ h0 * |u 1| ^ h1)) < ⊤ := by
  have hfun : (fun u : Fin 2 → ℝ => ENNReal.ofReal
        ((∑ i, u i ^ 2 * (![U0, U1] i) u) ^ (-(c' : ℝ)) * (∏ i, |u i| ^ (![h0, h1] i))))
      = (fun u : Fin 2 → ℝ => ENNReal.ofReal
        ((u 0 ^ 2 * U0 u + u 1 ^ 2 * U1 u) ^ (-(c' : ℝ)) * (|u 0| ^ h0 * |u 1| ^ h1))) := by
    funext u
    simp only [Fin.sum_univ_two, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← hfun]
  refine sjSlice_corner_block_lt_top 2 ![h0, h1] c' ?_ ![U0, U1] a ha ?_
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith [hc']
  · rw [Fin.forall_fin_two]
    exact ⟨by simpa using hU0, by simpa using hU1⟩

/-- **Non-vacuity witness.** With trivial units `Uᵢ = 1` (`a = 1`) and any block profile `h`, the
`d`-block corner crux is the concrete integral `∫⁻ (∑ᵢ uᵢ²)^{−c'}·∏ᵢ|uᵢ|^{hᵢ}` — finite for
`c' < ½·∑ᵢ(hᵢ+1)`, confirming the hypotheses are jointly satisfiable (the finiteness is not
vacuously true). -/
example (d : ℕ) (h : Fin d → ℕ) (c' : NNReal) (hc' : (c' : ℝ) < (∑ i, ((h i : ℝ) + 1)) / 2) :
    ∫⁻ u in unitBox d,
        ENNReal.ofReal ((∑ i, u i ^ 2 * 1) ^ (-(c' : ℝ)) * (∏ i, |u i| ^ h i)) < ⊤ :=
  sjSlice_corner_block_lt_top d h c' hc' (fun _ _ => 1) 1 one_pos (fun _ _ _ => le_refl 1)

end DLNFibre.DLN.RLCT
