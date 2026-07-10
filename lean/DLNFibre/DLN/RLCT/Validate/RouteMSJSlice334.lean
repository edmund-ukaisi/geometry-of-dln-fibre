import DLNFibre.DLN.RLCT.Validate.RouteMSJMonomialLower
import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit
import Mathlib.Analysis.MeanInequalities

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJSlice334` — the `(3,3,3,4)` corank-2 corner-blow-up crux

**Thread `genm-sjslice`, Stage 2 (S,J) native resolution, FIRST vertical slice.** This module
formalises the single load-bearing **crux** of the `(3,3,3,4)` corank-2 `(S,J)` resolution vertical
(pen-and-paper certificate `expeditions/2026-06-20-aoyagi-full/threads/genm-vslice/cert.md`, §5): the
finiteness of the *binding corner* local model after the two radial blow-ups.

## The corner model (vslice cert §5)

Front-split → pivot-chart cover → Schur block split → depth reduction → the two radial blow-ups
(the `2×2` corank block `Γ = u₀·Γ̂`, Jacobian `|u₀|³`, and the boundary-1 row `v = u₁·v̄`, Jacobian
`|u₁|²`) leave the loss in the shape of a **sum of two order-2 radial terms sharing the deep factor**:

    G  ≃  u₀² · U₀  +  u₁² · U₁,          measure  |u₀|³ · |u₁|² du₀ du₁,

with `U₀ = ‖w₁A₂‖² + δ²‖w₂A₂‖²` and `U₁ = a²‖v̄A₂‖²` the residual **units** (bounded below by a
positive constant on the generic-downstream chart — the named §8 brick, supplied here as the
hypothesis `a ≤ Uᵢ`, exactly as the banked terminal endpoint
`RouteMSJTerminal.terminal_monomial_mul_unit_lintegral_lt_top` supplies its `hunit`).

## The threshold `7/2 = ½·minAdm(3,3,3,4)` and why the corner (not a boundary) binds

Looking at `{u₀=0}` or `{u₁=0}` in isolation gives the misleading boundary abscissae `4/2 = 2` and
`3/2` — their min `3/2` is the two-matrix engine's **undershoot** (the symmetric AM-GM below). The
binding zero is the **corner** `u₀=u₁=0`, where the two codimensions ADD: `4 + 3 = 7`. The corner
blow-up `u₁ = u₀τ` accumulates the Jacobian powers `3 + 2 + 1 = 6` onto ONE terminal divisor while
the loss stays order `2`, giving the branch threshold `(6+1)/2 = 7/2 = ½·minAdm(3,3,3,4)`.

## The Lean realisation — weighted AM-GM to a separated monomial (the Newton-polygon content)

Rather than perform the change-of-variables Jacobian explicitly (the general-width CoV is the
deferred mountain), the corner is resolved analytically by **weighted** AM-GM with the min-cut
weights `(4/7, 3/7)`:

    u₀² + u₁²  ≥  (4/7)u₀² + (3/7)u₁²  ≥  (u₀²)^{4/7}(u₁²)^{3/7}  =  |u₀|^{8/7} |u₁|^{6/7},

so `(u₀²+u₁²)^{−c'}` is dominated by the **separated** monomial `|u₀|^{−8c'/7}|u₁|^{−6c'/7}`, and the
integrand by `|u₀|^{3−8c'/7} |u₁|^{2−6c'/7}` — landing on the banked
`RouteMSJMonomialLower.prod_rpow_lintegral_Ioo_box_lt_top`. Both axis exponents exceed `−1` **iff**
`c' < 7/2`; the weights `(4/7,3/7)` are exactly the direction where both constraints coincide. This is
the analytic form of "the codimensions add on the terminal exceptional divisor". Note the *symmetric*
weights `(1/2,1/2)` (basic AM-GM `u₀²+u₁² ≥ 2|u₀||u₁|`, dominator `|u₀|^{3−c'}|u₁|^{2−c'}`) would give
only `c' < 3` (the min of `4` and `3`) — the min-undershoot; the *weighted* step, where BOTH axis
constraints coincide at `7/2`, is what reaches the true branch threshold `½·minAdm(3,3,3,4)`
(`sjSlice334_minAdm_eq`, `sjSlice334_corner_lintegral_lt_top_of_lt_half_minAdm`).

S2-FREE: no `monomial_rlct`, no `cited_aoyagi_dln`. The `rlct = ½·codim` reading stays Cited; this
proves box-finiteness at the branch threshold only.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Real
open scoped ENNReal BigOperators

/-- **The width-general two-block corner-blow-up finiteness (vslice cert §9, M-generic).** For two
radial blow-ups of block dimensions `h₀+1`, `h₁+1` (accumulated Jacobian powers `h₀, h₁`, each loss
term order `2`) sharing the deep factor, the binding corner local model
`(u₀²·U₀ + u₁²·U₁)^{−c'}` with Jacobian `|u₀|^{h₀}·|u₁|^{h₁}` and residual units `U₀,U₁` bounded below
by `a>0` has finite `∫⁻` over the unit box for every `c' < (h₀+h₁+2)/2` — the branch threshold where
the two codimensions ADD. Proof: dominate by the separated monomial via weighted AM-GM at the
**min-cut weights** `w = ((h₀+1)/(h₀+h₁+2), (h₁+1)/(h₀+h₁+2))`, the unique direction where both axis
constraints coincide at `(h₀+h₁+2)/2`; the dominator is box-integrable there
(`prod_rpow_lintegral_Ioo_box_lt_top`). This is the analytic form of "the codimensions add on the
terminal exceptional divisor". -/
theorem sjSlice_corner_two_block_lt_top (h0 h1 : ℕ)
    (c' : NNReal) (hc' : (c' : ℝ) < ((h0 : ℝ) + (h1 : ℝ) + 2) / 2)
    (U0 U1 : (Fin 2 → ℝ) → ℝ) (a : ℝ) (ha : 0 < a)
    (hU0 : ∀ u ∈ unitBox 2, a ≤ U0 u) (hU1 : ∀ u ∈ unitBox 2, a ≤ U1 u) :
    ∫⁻ u in unitBox 2,
        ENNReal.ofReal ((u 0 ^ 2 * U0 u + u 1 ^ 2 * U1 u) ^ (-(c' : ℝ))
          * (|u 0| ^ h0 * |u 1| ^ h1)) < ⊤ := by
  set cc : ℝ := (c' : ℝ) with hcc_def
  have hcc0 : 0 ≤ cc := c'.coe_nonneg
  set s : ℝ := (h0 : ℝ) + (h1 : ℝ) + 2 with hs_def
  have hs : 0 < s := by rw [hs_def]; positivity
  -- min-cut weights `w₀ = (h₀+1)/s`, `w₁ = (h₁+1)/s`
  set w0 : ℝ := ((h0 : ℝ) + 1) / s with hw0_def
  set w1 : ℝ := ((h1 : ℝ) + 1) / s with hw1_def
  have hw0pos : 0 < w0 := by rw [hw0_def]; positivity
  have hw1pos : 0 < w1 := by rw [hw1_def]; positivity
  have hwsum : w0 + w1 = 1 := by rw [hw0_def, hw1_def]; field_simp; rw [hs_def]; ring
  have hw0le : w0 ≤ 1 := by
    rw [hw0_def, div_le_one hs, hs_def]; linarith [(Nat.cast_nonneg h1 : (0 : ℝ) ≤ (h1 : ℝ))]
  have hw1le : w1 ≤ 1 := by
    rw [hw1_def, div_le_one hs, hs_def]; linarith [(Nat.cast_nonneg h0 : (0 : ℝ) ≤ (h0 : ℝ))]
  -- the axis-exponent bounds `2·wᵢ·c' < hᵢ+1` (⟺ `c' < s/2 = (h₀+h₁+2)/2`)
  have h2ccs : 2 * cc < s := by rw [hs_def]; linarith [hc']
  have hw0s : w0 * s = (h0 : ℝ) + 1 := by rw [hw0_def]; field_simp
  have hw1s : w1 * s = (h1 : ℝ) + 1 := by rw [hw1_def]; field_simp
  have hw0lt : 2 * w0 * cc < (h0 : ℝ) + 1 := by
    have hstep : w0 * (2 * cc) < w0 * s := mul_lt_mul_of_pos_left h2ccs hw0pos
    rw [hw0s] at hstep; nlinarith [hstep]
  have hw1lt : 2 * w1 * cc < (h1 : ℝ) + 1 := by
    have hstep : w1 * (2 * cc) < w1 * s := mul_lt_mul_of_pos_left h2ccs hw1pos
    rw [hw1s] at hstep; nlinarith [hstep]
  -- the separated-monomial axis exponents `(h₀ − 2w₀c', h₁ − 2w₁c')`
  set e : Fin 2 → ℝ := ![(h0 : ℝ) - 2 * w0 * cc, (h1 : ℝ) - 2 * w1 * cc] with he_def
  have he : ∀ j, (-1 : ℝ) < e j := by
    rw [Fin.forall_fin_two, he_def]
    refine ⟨?_, ?_⟩ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      linarith [hw0lt, hw1lt]
  -- the dominating separated-monomial integral is finite on the open box
  have hfin : ∫⁻ u in Set.univ.pi (fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1),
      ENNReal.ofReal (∏ j, |u j| ^ (e j)) < ⊤ :=
    prod_rpow_lintegral_Ioo_box_lt_top 1 one_pos e he
  rw [restrict_unitBox_eq_open 2]
  -- pointwise domination `ofReal (F u) ≤ ofReal (a^{-c'}) · ofReal (∏ⱼ |uⱼ|^{eⱼ})` on the open box
  have hbound : (fun u => ENNReal.ofReal
        ((u 0 ^ 2 * U0 u + u 1 ^ 2 * U1 u) ^ (-cc) * (|u 0| ^ h0 * |u 1| ^ h1)))
      ≤ᵐ[volume.restrict (Set.univ.pi (fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1))]
      (fun u => ENNReal.ofReal (a ^ (-cc)) * ENNReal.ofReal (∏ j, |u j| ^ (e j))) := by
    refine ae_restrict_of_forall_mem (MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)) ?_
    intro u hu
    dsimp only
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at hu
    have hx : 0 < u 0 := (hu 0).1
    have hy : 0 < u 1 := (hu 1).1
    have humem : u ∈ unitBox 2 := by
      simp only [unitBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
      intro j; exact ⟨(hu j).1.le, (hu j).2.le⟩
    have hU0a := hU0 u humem
    have hU1a := hU1 u humem
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ a ^ (-cc))]
    apply ENNReal.ofReal_le_ofReal
    rw [Fin.prod_univ_two]
    simp only [he_def, Matrix.cons_val_zero, Matrix.cons_val_one]
    -- work with `X = |u 0|`, `Y = |u 1|` (both positive); `u 0 ^ 2 = X ^ 2`, etc.
    set X : ℝ := |u 0| with hX_def
    set Y : ℝ := |u 1| with hY_def
    have hXpos : 0 < X := by rw [hX_def]; exact abs_pos.mpr (ne_of_gt hx)
    have hYpos : 0 < Y := by rw [hY_def]; exact abs_pos.mpr (ne_of_gt hy)
    have hsqX : u 0 ^ 2 = X ^ 2 := by rw [hX_def, sq_abs]
    have hsqY : u 1 ^ 2 = Y ^ 2 := by rw [hY_def, sq_abs]
    rw [hsqX, hsqY]
    -- weighted AM-GM at the min-cut weights: `X^{2w₀} Y^{2w₁} ≤ X² + Y²`
    have hgm : X ^ (2 * w0) * Y ^ (2 * w1) ≤ X ^ 2 + Y ^ 2 := by
      have h1 := Real.geom_mean_le_arith_mean2_weighted hw0pos.le hw1pos.le
        (sq_nonneg X) (sq_nonneg Y) hwsum
      have e1 : (X ^ 2 : ℝ) ^ w0 = X ^ (2 * w0) := by
        rw [← Real.rpow_natCast X 2, ← Real.rpow_mul hXpos.le]; norm_num
      have e2 : (Y ^ 2 : ℝ) ^ w1 = Y ^ (2 * w1) := by
        rw [← Real.rpow_natCast Y 2, ← Real.rpow_mul hYpos.le]; norm_num
      rw [e1, e2] at h1
      have hax : w0 * X ^ 2 ≤ X ^ 2 := mul_le_of_le_one_left (sq_nonneg X) hw0le
      have hay : w1 * Y ^ 2 ≤ Y ^ 2 := mul_le_of_le_one_left (sq_nonneg Y) hw1le
      linarith [h1, hax, hay]
    -- lower bound on the loss base
    have hbb : a * (X ^ (2 * w0) * Y ^ (2 * w1)) ≤ X ^ 2 * U0 u + Y ^ 2 * U1 u := by
      have s1 : X ^ 2 * a ≤ X ^ 2 * U0 u := mul_le_mul_of_nonneg_left hU0a (sq_nonneg X)
      have s2 : Y ^ 2 * a ≤ Y ^ 2 * U1 u := mul_le_mul_of_nonneg_left hU1a (sq_nonneg Y)
      have hle1 : a * (X ^ (2 * w0) * Y ^ (2 * w1)) ≤ a * (X ^ 2 + Y ^ 2) :=
        mul_le_mul_of_nonneg_left hgm ha.le
      nlinarith [s1, s2, hle1]
    have hbpos : 0 < a * (X ^ (2 * w0) * Y ^ (2 * w1)) := by positivity
    -- rpow antitone at exponent `−c' ≤ 0`
    have hrp : (X ^ 2 * U0 u + Y ^ 2 * U1 u) ^ (-cc)
        ≤ (a * (X ^ (2 * w0) * Y ^ (2 * w1))) ^ (-cc) :=
      Real.rpow_le_rpow_of_nonpos hbpos hbb (by linarith)
    -- expand the dominating power × the Jacobian into the separated monomial (exponents pinned;
    -- rpow is not `ring`-aware, so exponent equalities are discharged as explicit rewrites)
    have hexp : (a * (X ^ (2 * w0) * Y ^ (2 * w1))) ^ (-cc) * (X ^ h0 * Y ^ h1)
        = a ^ (-cc) * (X ^ ((h0 : ℝ) - 2 * w0 * cc) * Y ^ ((h1 : ℝ) - 2 * w1 * cc)) := by
      rw [Real.mul_rpow ha.le (by positivity), Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul hXpos.le, ← Real.rpow_mul hYpos.le,
        ← Real.rpow_natCast X h0, ← Real.rpow_natCast Y h1,
        show a ^ (-cc) * (X ^ (2 * w0 * -cc) * Y ^ (2 * w1 * -cc))
              * (X ^ ((h0 : ℕ) : ℝ) * Y ^ ((h1 : ℕ) : ℝ))
            = a ^ (-cc) * ((X ^ (2 * w0 * -cc) * X ^ ((h0 : ℕ) : ℝ))
                * (Y ^ (2 * w1 * -cc) * Y ^ ((h1 : ℕ) : ℝ))) from by ring,
        ← Real.rpow_add hXpos, ← Real.rpow_add hYpos,
        show 2 * w0 * -cc + ((h0 : ℕ) : ℝ) = (h0 : ℝ) - 2 * w0 * cc from by push_cast; ring,
        show 2 * w1 * -cc + ((h1 : ℕ) : ℝ) = (h1 : ℝ) - 2 * w1 * cc from by push_cast; ring]
    calc (X ^ 2 * U0 u + Y ^ 2 * U1 u) ^ (-cc) * (X ^ h0 * Y ^ h1)
        ≤ (a * (X ^ (2 * w0) * Y ^ (2 * w1))) ^ (-cc) * (X ^ h0 * Y ^ h1) :=
          mul_le_mul_of_nonneg_right hrp (by positivity)
      _ = a ^ (-cc) * (X ^ ((h0 : ℝ) - 2 * w0 * cc) * Y ^ ((h1 : ℝ) - 2 * w1 * cc)) := hexp
  calc ∫⁻ u in Set.univ.pi (fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1),
          ENNReal.ofReal ((u 0 ^ 2 * U0 u + u 1 ^ 2 * U1 u) ^ (-cc) * (|u 0| ^ h0 * |u 1| ^ h1))
      ≤ ∫⁻ u in Set.univ.pi (fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1),
          ENNReal.ofReal (a ^ (-cc)) * ENNReal.ofReal (∏ j, |u j| ^ (e j)) :=
        lintegral_mono_ae hbound
    _ = ENNReal.ofReal (a ^ (-cc)) * ∫⁻ u in Set.univ.pi (fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1),
          ENNReal.ofReal (∏ j, |u j| ^ (e j)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-- **The `(3,3,3,4)` corank-2 corner-blow-up crux (vslice cert §5).** The binding corner local model
`(u₀²·U₀ + u₁²·U₁)^{−c'}` with the accumulated radial Jacobian `|u₀|³·|u₁|²` (block dims `4`, `3`;
Jacobian powers `3`, `2`) and residual units `U₀,U₁` bounded below by `a > 0`, finite over the unit
box for every `c' < 7/2 = ½·minAdm(3,3,3,4)`. The instantiation of the width-general
`sjSlice_corner_two_block_lt_top` at `(h₀,h₁) = (3,2)`, where `(h₀+h₁+2)/2 = 7/2`. -/
theorem sjSlice334_corner_lintegral_lt_top
    (c' : NNReal) (hc' : (c' : ℝ) < 7 / 2)
    (U0 U1 : (Fin 2 → ℝ) → ℝ) (a : ℝ) (ha : 0 < a)
    (hU0 : ∀ u ∈ unitBox 2, a ≤ U0 u) (hU1 : ∀ u ∈ unitBox 2, a ≤ U1 u) :
    ∫⁻ u in unitBox 2,
        ENNReal.ofReal ((u 0 ^ 2 * U0 u + u 1 ^ 2 * U1 u) ^ (-(c' : ℝ))
          * (|u 0| ^ 3 * |u 1| ^ 2)) < ⊤ :=
  sjSlice_corner_two_block_lt_top 3 2 c' (by push_cast; linarith [hc']) U0 U1 a ha hU0 hU1

/-- **Non-vacuity witness.** With the trivial units `U₀ = U₁ = 1` (`a = 1`), the corner crux is the
concrete integral `∫⁻ (u₀²+u₁²)^{−c'}·|u₀|³|u₁|²` of the pen-and-paper `vslice_corner.py` — finite for
`c' < 7/2`, confirming the hypotheses are jointly satisfiable (the finiteness is not vacuously true). -/
example (c' : NNReal) (hc' : (c' : ℝ) < 7 / 2) :
    ∫⁻ u in unitBox 2,
        ENNReal.ofReal ((u 0 ^ 2 * 1 + u 1 ^ 2 * 1) ^ (-(c' : ℝ)) * (|u 0| ^ 3 * |u 1| ^ 2)) < ⊤ :=
  sjSlice334_corner_lintegral_lt_top c' hc' (fun _ => 1) (fun _ => 1) 1 one_pos
    (fun _ _ => le_refl 1) (fun _ _ => le_refl 1)

/-! ## Tie to the charge — the threshold `7/2` IS `½·minAdm(3,3,3,4)` -/

/-- **The `(3,3,3,4)` charge is `7`.** `minAdm ![3,3,3,4] = 7`, the branch charge `[4,3,0]` summing to
the binding corank-2 cut (vslice cert §6). Via the banked layer-peeling recursion
`minAdmRec_eq_minAdm` + kernel `decide` (the pattern of `RouteM3333.lean`). This is the geometric
input to the branch threshold; the corner crux is finite below `½·minAdm = 7/2`. -/
theorem sjSlice334_minAdm_eq : minAdm (![3, 3, 3, 4] : Fin 4 → ℕ) = 7 := by
  rw [← minAdmRec_eq_minAdm]; decide

/-- **The corner crux at the charge-stated threshold `½·minAdm(3,3,3,4)`.** Identical to
`sjSlice334_corner_lintegral_lt_top` with the threshold written as `½·minAdm ![3,3,3,4]` rather than
the literal `7/2` — the honest "branch threshold = ½·minAdm" statement that the concrete corner
resolution reproduces (validating the pinned exponent bookkeeping,
`threads/genm-covdesign/sjjoint-exponents-cert.md` §2). -/
theorem sjSlice334_corner_lintegral_lt_top_of_lt_half_minAdm
    (c' : NNReal) (hc' : (c' : ℝ) < (minAdm (![3, 3, 3, 4] : Fin 4 → ℕ) : ℝ) / 2)
    (U0 U1 : (Fin 2 → ℝ) → ℝ) (a : ℝ) (ha : 0 < a)
    (hU0 : ∀ u ∈ unitBox 2, a ≤ U0 u) (hU1 : ∀ u ∈ unitBox 2, a ≤ U1 u) :
    ∫⁻ u in unitBox 2,
        ENNReal.ofReal ((u 0 ^ 2 * U0 u + u 1 ^ 2 * U1 u) ^ (-(c' : ℝ))
          * (|u 0| ^ 3 * |u 1| ^ 2)) < ⊤ := by
  refine sjSlice334_corner_lintegral_lt_top c' ?_ U0 U1 a ha hU0 hU1
  rw [sjSlice334_minAdm_eq] at hc'
  norm_num at hc' ⊢
  linarith

end DLNFibre.DLN.RLCT
