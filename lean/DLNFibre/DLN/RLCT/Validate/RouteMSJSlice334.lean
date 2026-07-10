import DLNFibre.DLN.RLCT.Validate.RouteMSJMonomialLower
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
weights `(1/2,1/2)` (basic AM-GM `u₀²+u₁² ≥ 2|u₀||u₁|`) would give only `c' < 3`, the min-undershoot —
the weighted step is load-bearing (`sjSlice334_symmetric_undershoot`).

S2-FREE: no `monomial_rlct`, no `cited_aoyagi_dln`. The `rlct = ½·codim` reading stays Cited; this
proves box-finiteness at the branch threshold only.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Real
open scoped ENNReal BigOperators

/-- **The `(3,3,3,4)` corank-2 corner-blow-up crux (vslice cert §5).** The binding corner local model
`(u₀²·U₀ + u₁²·U₁)^{−c'}` with the accumulated radial Jacobian `|u₀|³·|u₁|²` and residual units
`U₀,U₁` bounded below by `a > 0` on the box, has finite `∫⁻` over the unit box for every
`c' < 7/2 = ½·minAdm(3,3,3,4)`. The threshold is the branch charge `(4+3+... = 7)/2` realised at the
corner where the two codimensions add. Proof: dominate by the separated monomial
`|u₀|^{3−8c'/7}|u₁|^{2−6c'/7}` (weighted AM-GM, min-cut weights `(4/7,3/7)`), which is box-integrable
iff `c' < 7/2` (`prod_rpow_lintegral_Ioo_box_lt_top`). -/
theorem sjSlice334_corner_lintegral_lt_top
    (c' : NNReal) (hc' : (c' : ℝ) < 7 / 2)
    (U0 U1 : (Fin 2 → ℝ) → ℝ) (a : ℝ) (ha : 0 < a)
    (hU0 : ∀ u ∈ unitBox 2, a ≤ U0 u) (hU1 : ∀ u ∈ unitBox 2, a ≤ U1 u) :
    ∫⁻ u in unitBox 2,
        ENNReal.ofReal ((u 0 ^ 2 * U0 u + u 1 ^ 2 * U1 u) ^ (-(c' : ℝ))
          * (|u 0| ^ 3 * |u 1| ^ 2)) < ⊤ := by
  set cc : ℝ := (c' : ℝ) with hcc_def
  have hcc0 : 0 ≤ cc := c'.coe_nonneg
  -- the separated-monomial axis exponents `(3 − 8c'/7, 2 − 6c'/7)`
  set e : Fin 2 → ℝ := ![3 - 8 / 7 * cc, 2 - 6 / 7 * cc] with he_def
  have he : ∀ j, (-1 : ℝ) < e j := by
    rw [Fin.forall_fin_two, he_def]
    refine ⟨?_, ?_⟩ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
      linarith [hc']
  -- the dominating separated-monomial integral is finite on the open box
  have hfin : ∫⁻ u in Set.univ.pi (fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1),
      ENNReal.ofReal (∏ j, |u j| ^ (e j)) < ⊤ :=
    prod_rpow_lintegral_Ioo_box_lt_top 1 one_pos e he
  rw [restrict_unitBox_eq_open 2]
  -- pointwise domination `ofReal (F u) ≤ ofReal (a^{-c'}) · ofReal (∏ⱼ |uⱼ|^{eⱼ})` on the open box
  have hbound : (fun u => ENNReal.ofReal
        ((u 0 ^ 2 * U0 u + u 1 ^ 2 * U1 u) ^ (-cc) * (|u 0| ^ 3 * |u 1| ^ 2)))
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
    simp only [he_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    -- work with `X = |u 0|`, `Y = |u 1|` (both positive); `u 0 ^ 2 = X ^ 2`, etc.
    set X : ℝ := |u 0| with hX_def
    set Y : ℝ := |u 1| with hY_def
    have hXpos : 0 < X := by rw [hX_def]; exact abs_pos.mpr (ne_of_gt hx)
    have hYpos : 0 < Y := by rw [hY_def]; exact abs_pos.mpr (ne_of_gt hy)
    have hsqX : u 0 ^ 2 = X ^ 2 := by rw [hX_def, sq_abs]
    have hsqY : u 1 ^ 2 = Y ^ 2 := by rw [hY_def, sq_abs]
    rw [hsqX, hsqY]
    -- weighted AM-GM: `X^{8/7} Y^{6/7} ≤ X² + Y²`
    have hgm : X ^ (8 / 7 : ℝ) * Y ^ (6 / 7 : ℝ) ≤ X ^ 2 + Y ^ 2 := by
      have h1 := Real.geom_mean_le_arith_mean2_weighted (by norm_num : (0 : ℝ) ≤ 4 / 7)
        (by norm_num : (0 : ℝ) ≤ 3 / 7) (sq_nonneg X) (sq_nonneg Y) (by norm_num)
      have e1 : (X ^ 2 : ℝ) ^ (4 / 7 : ℝ) = X ^ (8 / 7 : ℝ) := by
        rw [← Real.rpow_natCast X 2, ← Real.rpow_mul hXpos.le]; norm_num
      have e2 : (Y ^ 2 : ℝ) ^ (3 / 7 : ℝ) = Y ^ (6 / 7 : ℝ) := by
        rw [← Real.rpow_natCast Y 2, ← Real.rpow_mul hYpos.le]; norm_num
      rw [e1, e2] at h1
      nlinarith [h1, sq_nonneg X, sq_nonneg Y]
    -- lower bound on the loss base
    have hbb : a * (X ^ (8 / 7 : ℝ) * Y ^ (6 / 7 : ℝ)) ≤ X ^ 2 * U0 u + Y ^ 2 * U1 u := by
      have s1 : X ^ 2 * a ≤ X ^ 2 * U0 u := mul_le_mul_of_nonneg_left hU0a (sq_nonneg X)
      have s2 : Y ^ 2 * a ≤ Y ^ 2 * U1 u := mul_le_mul_of_nonneg_left hU1a (sq_nonneg Y)
      have hle1 : a * (X ^ (8 / 7 : ℝ) * Y ^ (6 / 7 : ℝ)) ≤ a * (X ^ 2 + Y ^ 2) :=
        mul_le_mul_of_nonneg_left hgm ha.le
      nlinarith [s1, s2, hle1]
    have hbpos : 0 < a * (X ^ (8 / 7 : ℝ) * Y ^ (6 / 7 : ℝ)) := by positivity
    -- rpow antitone at exponent `−c' ≤ 0`
    have hrp : (X ^ 2 * U0 u + Y ^ 2 * U1 u) ^ (-cc)
        ≤ (a * (X ^ (8 / 7 : ℝ) * Y ^ (6 / 7 : ℝ))) ^ (-cc) :=
      Real.rpow_le_rpow_of_nonpos hbpos hbb (by linarith)
    -- expand the dominating power × the Jacobian into the separated monomial (exponents pinned;
    -- rpow is not `ring`-aware, so exponent equalities are discharged as explicit rewrites)
    have hexp : (a * (X ^ (8 / 7 : ℝ) * Y ^ (6 / 7 : ℝ))) ^ (-cc) * (X ^ 3 * Y ^ 2)
        = a ^ (-cc) * (X ^ (3 - 8 / 7 * cc) * Y ^ (2 - 6 / 7 * cc)) := by
      rw [Real.mul_rpow ha.le (by positivity), Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul hXpos.le, ← Real.rpow_mul hYpos.le,
        ← Real.rpow_natCast X 3, ← Real.rpow_natCast Y 2,
        show a ^ (-cc) * (X ^ (8 / 7 * -cc) * Y ^ (6 / 7 * -cc)) * (X ^ ((3 : ℕ) : ℝ) * Y ^ ((2 : ℕ) : ℝ))
            = a ^ (-cc) * ((X ^ (8 / 7 * -cc) * X ^ ((3 : ℕ) : ℝ))
                * (Y ^ (6 / 7 * -cc) * Y ^ ((2 : ℕ) : ℝ))) from by ring,
        ← Real.rpow_add hXpos, ← Real.rpow_add hYpos,
        show 8 / 7 * -cc + ((3 : ℕ) : ℝ) = 3 - 8 / 7 * cc from by push_cast; ring,
        show 6 / 7 * -cc + ((2 : ℕ) : ℝ) = 2 - 6 / 7 * cc from by push_cast; ring]
    calc (X ^ 2 * U0 u + Y ^ 2 * U1 u) ^ (-cc) * (X ^ 3 * Y ^ 2)
        ≤ (a * (X ^ (8 / 7 : ℝ) * Y ^ (6 / 7 : ℝ))) ^ (-cc) * (X ^ 3 * Y ^ 2) :=
          mul_le_mul_of_nonneg_right hrp (by positivity)
      _ = a ^ (-cc) * (X ^ (3 - 8 / 7 * cc) * Y ^ (2 - 6 / 7 * cc)) := hexp
  calc ∫⁻ u in Set.univ.pi (fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1),
          ENNReal.ofReal ((u 0 ^ 2 * U0 u + u 1 ^ 2 * U1 u) ^ (-cc) * (|u 0| ^ 3 * |u 1| ^ 2))
      ≤ ∫⁻ u in Set.univ.pi (fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1),
          ENNReal.ofReal (a ^ (-cc)) * ENNReal.ofReal (∏ j, |u j| ^ (e j)) :=
        lintegral_mono_ae hbound
    _ = ENNReal.ofReal (a ^ (-cc)) * ∫⁻ u in Set.univ.pi (fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1),
          ENNReal.ofReal (∏ j, |u j| ^ (e j)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end DLNFibre.DLN.RLCT
