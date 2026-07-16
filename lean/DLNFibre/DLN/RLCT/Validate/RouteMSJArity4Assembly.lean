import DLNFibre.DLN.RLCT.Validate.RouteMSJFrontChargeBox
import DLNFibre.DLN.RLCT.Validate.RouteMSJResolution

set_option linter.style.longLine false

/-!
# `RouteMSJArity4Assembly` — the coupled-incidence assembly skeleton (arity ≥ 4)

**Thread `genm-3abase` (aoyagi-full Stage 2), the coupled-incidence route CAPSTONE skeleton.** Wires the
coupled-route bricks into the box-finiteness `routeMLayerBoxIntegral M c' 1 < ⊤` for a `≥ 4`-width chain
`M` at a NONDEGENERATE binding cut `t` (`t + 1 ≤ min(M₀,M₁)`). Write `r = min(M₀−t, M₁−t)` for the shell
range; the shells are `j : Fin (r+1)`.

## Contents
* `rpow_neg_le_one_add`, `routeMLayerBoxIntegral_exponent_mono` — the **all-`c'` monotone domination**:
  `box(c₀) ≤ vol(box) + box(c')` for `0 ≤ c₀ ≤ c'`. Reduces finiteness for all `c' < ½·minAdm` to
  finiteness at ONE `c'` in the top window (since `vol(box) < ⊤`, banked). Removes the top-`c'`-window
  restriction below — not a scope loss.
* `routeMBox_arity4_lt_top_of_coupled` — the per-`c'` box-finiteness from the coupled bricks as hypotheses.

## The coupled bricks (hypotheses)
* `hG1` — **G1** (tpeel, `RouteMSJTPeel`): `box ≤ ∑_j ∑_ρ ∑_κ shellSpineIntegrand M (t+j) κ ε r j c'`
  (front-split + outer singular-shell cover + inner co-null pivot-chart cover + freed CoV).
* `hfin` — **item 4** (corankrec ← couplerad), the sole hypothesis of `G2`, **SCOPED to BINDING SHELLS
  `1 ≤ j < r`**. Codex red-team (couplerad): the item-4 chartwise charge-domination `C ≥ floor` holds on
  binding shells (`1 ≤ j < r`, + rank-genericity), NOT at the boundary shells `j = 0` or `j = r`. (Codex
  CE `(6,8,5,5)`: `C₅ = 18 <` floor `19` — the NON-binding cut `u = 5 < t★ = 6`, out of scope; exact scan
  = 0 below-floor over 4386 in-scope binding-shell cells.) So `hfin` carries `1 ≤ j < r`, matching
  corankrec's target.
* `hbdryFin` — the **boundary shells** `j = 0` and `j = r`: the front-charge box at `u = t` and `u = t+r`.
  Held as a hypothesis — item-4 does not cover them. Expected EASIER (banked handling): `j = 0` the bulk /
  generic-rank shell (entry / hsector); `j = r` the saturated / degenerate boundary (`a = M₀−u = 0` or
  `b = M₁−u = 0`, higher-codim / near-null; SD-7). The `shellSpineIntegrand_le_layerBox` a-fortiori is the
  WRONG direction for finiteness — the boundary discharge is a separate small build, not that lemma.

The wiring: `hG1 → LINK → G2` on binding shells, `hG1 → LINK → hbdryFin` on boundary shells, then a finite
triple sum. NATIVE (no `cited_aoyagi_dln`).

## Scope (caveats next to the claim)
Per-`c'`, and `hc'` is the LINK's block-charge lower bound `(M₀−(t+j))(M₁−(t+j))/2 < c'` at every shell
(binding at `j = 0`: `(M₀−t)(M₁−t)/2 < c'`) — the **top `c'` window**. `routeMLayerBoxIntegral_exponent_mono`
removes it (all-`c'` from one-`c'`). `htb`/`hbind` require a nondegenerate binding cut (existence banked;
nondegeneracy a further ℕ fact). Full arity-≥4 `(□)` = `RouteMBoxThresholdFinite M` adds the
binding-nondegeneracy, the boundary discharge (`hbdryFin`), and the banked strong-induction wrapper
`routeMBoxThresholdFinite_of_step`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory DeepAtlas
open scoped ENNReal BigOperators

variable {L : ℕ}

/-! ## All-`c'` monotone domination (removes the top-`c'`-window restriction) -/

/-- **Pointwise exponent domination**: `x^(−c₀) ≤ 1 + x^(−c')` for `0 ≤ x`, `0 ≤ c₀ ≤ c'`. On `x ≥ 1`,
`x^(−c₀) ≤ 1`; on `0 < x < 1`, `x^(−c₀) ≤ x^(−c')` (larger negative exponent, base `< 1`); on `x = 0`,
`x^(−c₀) ≤ 1`. -/
theorem rpow_neg_le_one_add {x : ℝ} (hx : 0 ≤ x) {c₀ c' : ℝ} (hc₀ : 0 ≤ c₀) (hle : c₀ ≤ c') :
    x ^ (-c₀) ≤ 1 + x ^ (-c') := by
  have hnn : 0 ≤ x ^ (-c') := Real.rpow_nonneg hx _
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · -- x = 0
    have h0 : (0 : ℝ) ^ (-c₀) ≤ 1 := by
      rcases eq_or_lt_of_le hc₀ with hc00 | hc0pos
      · rw [← hc00, neg_zero, Real.rpow_zero]
      · rw [Real.zero_rpow (by linarith : -c₀ ≠ 0)]; norm_num
    rw [← hx0]; rw [← hx0] at hnn; linarith
  · rcases le_total x 1 with hx1 | hx1
    · -- 0 < x ≤ 1
      have : x ^ (-c₀) ≤ x ^ (-c') :=
        Real.rpow_le_rpow_of_exponent_ge hxpos hx1 (by linarith)
      linarith
    · -- x ≥ 1
      have : x ^ (-c₀) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
      linarith

/-- **All-`c'` monotone domination for the layer-product box integral.** For `0 ≤ c₀ ≤ c'`,
`box(c₀) ≤ vol(box) + box(c')`. Since `vol(paramsBoxM M 1) < ⊤` (banked `paramsBoxM_volume_lt_top`),
finiteness at one exponent `c'` yields finiteness at every smaller `c₀ ≥ 0` — the top-`c'`-window
restriction of the coupled skeleton is not a scope loss. -/
theorem routeMLayerBoxIntegral_exponent_mono (M : Fin (L + 1) → ℕ) {c₀ c' : ℝ}
    (hc₀ : 0 ≤ c₀) (hle : c₀ ≤ c') :
    routeMLayerBoxIntegral M c₀ 1 ≤ volume (paramsBoxM M 1) + routeMLayerBoxIntegral M c' 1 := by
  have hfrob : ∀ A : Params M, 0 ≤ frobSq (prod M A) := fun A =>
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  calc routeMLayerBoxIntegral M c₀ 1
      = ∫⁻ A in paramsBoxM M 1, ENNReal.ofReal ((frobSq (prod M A)) ^ (-c₀)) := rfl
    _ ≤ ∫⁻ A in paramsBoxM M 1, (1 + ENNReal.ofReal ((frobSq (prod M A)) ^ (-c'))) := by
        refine lintegral_mono (fun A => ?_)
        rw [← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add zero_le_one (Real.rpow_nonneg (hfrob A) _)]
        exact ENNReal.ofReal_le_ofReal (rpow_neg_le_one_add (hfrob A) hc₀ hle)
    _ = (∫⁻ _ in paramsBoxM M 1, (1 : ℝ≥0∞))
          + ∫⁻ A in paramsBoxM M 1, ENNReal.ofReal ((frobSq (prod M A)) ^ (-c')) := by
        rw [lintegral_add_left measurable_const]
    _ = volume (paramsBoxM M 1) + routeMLayerBoxIntegral M c' 1 := by
        rw [setLIntegral_const, one_mul]; rfl

/-- **All-`c'` from a top window.** `RouteMBoxThresholdFinite M` (box finite for every
`c' < ½·minAdm M`) follows from box-finiteness on any TOP window `(lo, ½·minAdm M)` with `lo < ½·minAdm M`.
For a target `c₀ < ½·minAdm`, pick `c'` strictly between `max(lo, c₀)` and `½·minAdm` (`exists_between`),
bound `box(c₀) ≤ vol(box) + box(c')` (`routeMLayerBoxIntegral_exponent_mono`), and both terms are finite
(`paramsBoxM_volume_lt_top`, `hwin`). This is the wrapper that turns the coupled skeleton's per-`c'`,
top-window output into the full threshold predicate; the coupled route supplies `hwin` with
`lo = (M₀−t)(M₁−t)/2`. Arity-agnostic, NATIVE. -/
theorem routeMBoxThresholdFinite_of_window (M : Fin (L + 1) → ℕ) (lo : ℝ)
    (hlo : lo < (minAdm M : ℝ) / 2)
    (hwin : ∀ c' : ℝ, lo < c' → c' < (minAdm M : ℝ) / 2 →
        routeMLayerBoxIntegral M c' 1 < ⊤) :
    RouteMBoxThresholdFinite M := by
  intro c₀ hc₀
  obtain ⟨c', hlt1, hlt2⟩ := exists_between (max_lt hlo hc₀)
  have hc₀c' : (c₀ : ℝ) ≤ c' := le_of_lt (lt_of_le_of_lt (le_max_right lo (c₀ : ℝ)) hlt1)
  have hloc' : lo < c' := lt_of_le_of_lt (le_max_left lo (c₀ : ℝ)) hlt1
  refine lt_of_le_of_lt
    (routeMLayerBoxIntegral_exponent_mono M (c₀.coe_nonneg) hc₀c') ?_
  exact ENNReal.add_lt_top.mpr ⟨paramsBoxM_volume_lt_top M 1, hwin c' hloc' hlt2⟩

/-! ## The coupled-incidence assembly skeleton -/

/-- **The coupled-incidence assembly skeleton (arity ≥ 4, per-`c'`, binding-shell-scoped).** Given G1
(`hG1`), item 4 scoped to binding shells (`hfin`, `1 ≤ j < r`), and the boundary-shell finiteness
(`hbdryFin`, `j = 0` / `j = r`), the box integral is finite. Wires `shellSpine_le_frontCharge_binding`
(LINK) uniformly, dispatching each shell's front-charge box to G2 (`frontChargeBox_lt_top_of_hfin`, binding
shells) or `hbdryFin` (boundary shells). NATIVE. See the module docstring for the scope. -/
theorem routeMBox_arity4_lt_top_of_coupled
    (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ) (ε c' : ℝ)
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i) (htb : t + 1 ≤ min (M 0) (M 1))
    (hbind : minAdm M = peelCharge M t + minAdm (redChain t M))
    (hc' : ∀ j : Fin (min (M 0 - t) (M 1 - t) + 1),
        ((M 0 - (t + (j : ℕ)) : ℕ) : ℝ) * ((M 1 - (t + (j : ℕ)) : ℕ) : ℝ) / 2 < c')
    (hG1 : routeMLayerBoxIntegral M c' 1
        ≤ ∑ j : Fin (min (M 0 - t) (M 1 - t) + 1),
            ∑ _ρ : Fin (t + (j : ℕ)) ↪ Fin (M 0),
              ∑ κ : Fin (t + (j : ℕ)) ↪ Fin (M 1),
                shellSpineIntegrand M (t + (j : ℕ)) κ ε (min (M 0 - t) (M 1 - t)) j c')
    (hfin : ∀ (j : Fin (min (M 0 - t) (M 1 - t) + 1)),
        1 ≤ (j : ℕ) → (j : ℕ) < min (M 0 - t) (M 1 - t) →
        ∀ i : CRIndex (dropHead (redChain (t + (j : ℕ)) M)),
        ∫⁻ p in (paramsBoxM (redChain (t + (j : ℕ)) M) 1 ×ˢ matBox (M 1 - (t + (j : ℕ))) (M 2) 1)
            ∩ projDeep M (t + (j : ℕ)) ⁻¹'
              (deepCell (dropHead (redChain (t + (j : ℕ)) M)) (dropHead (redChain (t + (j : ℕ)) M) 0) L
                le_rfl (dropHead (redChain (t + (j : ℕ)) M) (Fin.last L)) i
                (fun _ => (1 : Matrix (Fin (dropHead (redChain (t + (j : ℕ)) M) (Fin.last L)))
                  (Fin (dropHead (redChain (t + (j : ℕ)) M) (Fin.last L))) ℝ))),
          frontChargeIntegrand M (t + (j : ℕ)) c' p < ⊤)
    (hbdryFin : ∀ (j : Fin (min (M 0 - t) (M 1 - t) + 1)),
        (j : ℕ) = 0 ∨ (j : ℕ) = min (M 0 - t) (M 1 - t) →
        ∫⁻ p in paramsBoxM (redChain (t + (j : ℕ)) M) 1 ×ˢ matBox (M 1 - (t + (j : ℕ))) (M 2) 1,
          frontChargeIntegrand M (t + (j : ℕ)) c' p < ⊤) :
    routeMLayerBoxIntegral M c' 1 < ⊤ := by
  refine lt_of_le_of_lt hG1 ?_
  refine ENNReal.sum_lt_top.mpr (fun j _ => ?_)
  refine ENNReal.sum_lt_top.mpr (fun _ρ _ => ?_)
  refine ENNReal.sum_lt_top.mpr (fun κ _ => ?_)
  have hjr : (j : ℕ) ≤ min (M 0 - t) (M 1 - t) := Nat.lt_succ_iff.mp j.isLt
  refine lt_of_le_of_lt
    (shellSpine_le_frontCharge_binding M t (j : ℕ) κ ε c' hjr (hc' j) ht1 hnd htb hbind) ?_
  by_cases hmid : 1 ≤ (j : ℕ) ∧ (j : ℕ) < min (M 0 - t) (M 1 - t)
  · exact frontChargeBox_lt_top_of_hfin M (t + (j : ℕ)) c' (hfin j hmid.1 hmid.2)
  · exact hbdryFin j (by omega)

end DLNFibre.DLN.RLCT
