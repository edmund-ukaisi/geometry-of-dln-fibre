import DLNFibre.DLN.RLCT.Validate.RouteMSJFrontChargeBox
import DLNFibre.DLN.RLCT.Validate.RouteMSJResolution
import DLNFibre.DLN.RLCT.Validate.RouteMSJBackPeel
import DLNFibre.DLN.RLCT.Validate.RouteMSchurRectCapB

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
* `hfin` — the sole hypothesis of `G2`, on ALL NON-SATURATED shells `j < r` (`u = t+j`). Its CONTENT splits
  by cut, for the caller: couplerad's item 4 (the chartwise charge-domination `C ≥ floor`) on the BINDING
  shells `1 ≤ j < r` (Codex red-team: holds there, + rank-genericity; CE `(6,8,5,5)` `C₅=18<19` was the
  non-binding cut `u=5<t★=6`, out of scope — exact scan 0 below-floor over 4386 in-scope cells); and
  schurrec's `ChargedRectSchurCore` at the GENERIC ENTRY shell `j = 0` (cut `u=t`, interior dims
  `a=M₀−t, b=M₁−t ≥ 1`, full deep rank — a genuinely CHARGED core, `a≥1`, converging with the front `a·b`
  charge; NB the uncharged `a<M₂−b+1` can sit at the edge `a+b=M₂+1` here, so `j=0` needs the CHARGED
  convergence, not the bare corank weight).
* `hbdryShell` — the **saturated shell** `j = r` only (`u = t+r = min(M₀,M₁)`, so `a=M₀−u=0` OR `b=M₁−u=0`):
  DIRECT `shellSpineIntegrand` finiteness (satred/satbuild's IH-fed brick — the LINK is inapplicable there,
  as it drops the singular-shell restriction). `j = 0` is NOT here — it has interior dims (see `hfin`).

The wiring: `hG1 → LINK → G2` on `j < r` (interior + generic entry `j=0`); `hbdryShell` DIRECT on `j=r`;
then a finite triple sum. NATIVE (no `cited_aoyagi_dln`).

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

/-- **The coupled-incidence assembly skeleton (arity ≥ 4, per-`c'`).** Given G1 (`hG1`), the per-cell
COUPLED-BOX finiteness `hcell` on ALL non-saturated shells `j < r`, and the saturated-shell finiteness
`hbdryShell` (`j = r`), the box integral is finite. Shells `j < r` go through the HONEST coupled-box route:
`shellSpine ≤[shellSpine_le_coupledBox, step 1, PROVEN unconditional] ∫coupledBox <[coupledBox_lt_top_of_cells]
⊤` — NOT the front-charge route, which is `+∞` at EDGE cells (`a+b=ρ+1`, where step-2's Γ→univ extension
manufactures the divergent `det(Q_bQ_bᵀ)^{−a/2}` charge). The SATURATED shell `j = r` (one of `a,b = 0`) is
bounded by DIRECT `shellSpineIntegrand` finiteness (`hbdryShell`, satred/satbuild's brick). `hcell`'s content
splits by CELL at the fill: IN-REGIME cells (`a+b≤ρ`) via `coupledCell_le_frontCell` (step 2) + item 4
(couplerad `1≤j<r` / schurrec entry `j=0`); EDGE cells (`a+b=ρ+1`) via (D)'s corank-one instance
(`edge_coupledBox_lt_top`). NATIVE. See the module docstring for the scope. -/
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
    (hcell : ∀ (j : Fin (min (M 0 - t) (M 1 - t) + 1)),
        (j : ℕ) < min (M 0 - t) (M 1 - t) →
        ∀ i : CRIndex (dropHead (redChain (t + (j : ℕ)) M)),
        ∫⁻ p in (paramsBoxM (redChain (t + (j : ℕ)) M) 1 ×ˢ matBox (M 1 - (t + (j : ℕ))) (M 2) 1)
            ∩ projDeep M (t + (j : ℕ)) ⁻¹'
              (deepCell (dropHead (redChain (t + (j : ℕ)) M)) (dropHead (redChain (t + (j : ℕ)) M) 0) L
                le_rfl (dropHead (redChain (t + (j : ℕ)) M) (Fin.last L)) i
                (fun _ => (1 : Matrix (Fin (dropHead (redChain (t + (j : ℕ)) M) (Fin.last L)))
                  (Fin (dropHead (redChain (t + (j : ℕ)) M) (Fin.last L))) ℝ))),
          coupledBoxIntegrand M (t + (j : ℕ)) c' p < ⊤)
    (hbdryShell : ∀ (j : Fin (min (M 0 - t) (M 1 - t) + 1))
        (κ : Fin (t + (j : ℕ)) ↪ Fin (M 1)),
        (j : ℕ) = min (M 0 - t) (M 1 - t) →
        shellSpineIntegrand M (t + (j : ℕ)) κ ε (min (M 0 - t) (M 1 - t)) j c' < ⊤) :
    routeMLayerBoxIntegral M c' 1 < ⊤ := by
  refine lt_of_le_of_lt hG1 ?_
  refine ENNReal.sum_lt_top.mpr (fun j _ => ?_)
  refine ENNReal.sum_lt_top.mpr (fun _ρ _ => ?_)
  refine ENNReal.sum_lt_top.mpr (fun κ _ => ?_)
  have hjr : (j : ℕ) ≤ min (M 0 - t) (M 1 - t) := Nat.lt_succ_iff.mp j.isLt
  by_cases hlt : (j : ℕ) < min (M 0 - t) (M 1 - t)
  · -- HONEST coupled-route interior: shellSpine ≤[step1, unconditional] ∫coupledBox <[coupledBox-G2] ⊤.
    -- (NOT via frontCharge, which is +∞ at edge cells a+b=ρ+1.) hcell splits at the fill: in-regime
    -- (a+b≤ρ) via coupledCell_le_frontCell + item 4; edge (a+b=ρ+1) via (D)'s corank-one instance.
    exact lt_of_le_of_lt
      (shellSpine_le_coupledBox M t (j : ℕ) κ ε c' hjr)
      (coupledBox_lt_top_of_cells M (t + (j : ℕ)) c' (hcell j hlt))
  · exact hbdryShell j κ (by omega)

/-! ## Per-`M` coupled closure (nondegenerate interior binding cut) -/

/-- **The coupled route delivers `RouteMBoxThresholdFinite M` for a nondegenerate interior binding cut.**
Wires the per-`c'` skeleton (`routeMBox_arity4_lt_top_of_coupled`) through the all-`c'` window wrapper
(`routeMBoxThresholdFinite_of_window`). The window's lower endpoint is `lo = (M₀−t)(M₁−t)/2 = peelCharge/2`;
its nonemptiness (`lo < ½·minAdm M`) is exactly `hred : 0 < minAdm (redChain t M)` (via `hbind`,
`minAdm M = peelCharge M t + minAdm (redChain t M)`). The skeleton's per-shell block-charge bound `hc'` at
each `j` follows from `lo < c'` by monotonicity `(M₀−(t+j))(M₁−(t+j)) ≤ (M₀−t)(M₁−t)`. Isolates the coupled
bricks `hG1` (tpeel), `hfin` (per-cell finiteness on ALL non-saturated shells `j<r`: couplerad's item 4 on
`1≤j<r` + schurrec's ChargedRectSchurCore at the generic entry `j=0`), `hbdryShell` (direct shellSpine
finiteness at the SATURATED shell `j=r`) as ∀-`c'` hypotheses. NATIVE. Does NOT use the arity-IH — this is the nondegenerate-interior case; the degenerate /
boundary-argmin chains are handled by the wrapper `routeMBoxThresholdFinite_of_step`'s strong induction. -/
theorem routeMBoxThresholdFinite_of_coupled
    (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ) (ε : ℝ)
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i) (htb : t + 1 ≤ min (M 0) (M 1))
    (hbind : minAdm M = peelCharge M t + minAdm (redChain t M))
    (hred : 0 < minAdm (redChain t M))
    (hG1 : ∀ c' : ℝ, routeMLayerBoxIntegral M c' 1
        ≤ ∑ j : Fin (min (M 0 - t) (M 1 - t) + 1),
            ∑ _ρ : Fin (t + (j : ℕ)) ↪ Fin (M 0),
              ∑ κ : Fin (t + (j : ℕ)) ↪ Fin (M 1),
                shellSpineIntegrand M (t + (j : ℕ)) κ ε (min (M 0 - t) (M 1 - t)) j c')
    (hcell : ∀ (c' : ℝ) (j : Fin (min (M 0 - t) (M 1 - t) + 1)),
        (j : ℕ) < min (M 0 - t) (M 1 - t) →
        ∀ i : CRIndex (dropHead (redChain (t + (j : ℕ)) M)),
        ∫⁻ p in (paramsBoxM (redChain (t + (j : ℕ)) M) 1 ×ˢ matBox (M 1 - (t + (j : ℕ))) (M 2) 1)
            ∩ projDeep M (t + (j : ℕ)) ⁻¹'
              (deepCell (dropHead (redChain (t + (j : ℕ)) M)) (dropHead (redChain (t + (j : ℕ)) M) 0) L
                le_rfl (dropHead (redChain (t + (j : ℕ)) M) (Fin.last L)) i
                (fun _ => (1 : Matrix (Fin (dropHead (redChain (t + (j : ℕ)) M) (Fin.last L)))
                  (Fin (dropHead (redChain (t + (j : ℕ)) M) (Fin.last L))) ℝ))),
          coupledBoxIntegrand M (t + (j : ℕ)) c' p < ⊤)
    (hbdryShell : ∀ (c' : ℝ) (j : Fin (min (M 0 - t) (M 1 - t) + 1))
        (κ : Fin (t + (j : ℕ)) ↪ Fin (M 1)),
        (j : ℕ) = min (M 0 - t) (M 1 - t) →
        shellSpineIntegrand M (t + (j : ℕ)) κ ε (min (M 0 - t) (M 1 - t)) j c' < ⊤) :
    RouteMBoxThresholdFinite M := by
  have hpeellt : ((M 0 - t) * (M 1 - t) : ℕ) < minAdm M := by
    rw [hbind, peelCharge]; omega
  have hpeelR : (((M 0 - t) * (M 1 - t) : ℕ) : ℝ) < (minAdm M : ℝ) := by exact_mod_cast hpeellt
  refine routeMBoxThresholdFinite_of_window M ((((M 0 - t) * (M 1 - t) : ℕ) : ℝ) / 2) (by linarith)
    (fun c' hlo hhi => ?_)
  refine routeMBox_arity4_lt_top_of_coupled M t ε c' ht1 hnd htb hbind ?_
    (hG1 c') (hcell c') (hbdryShell c')
  intro j
  have hmono : (M 0 - (t + (j : ℕ))) * (M 1 - (t + (j : ℕ))) ≤ (M 0 - t) * (M 1 - t) :=
    Nat.mul_le_mul (Nat.sub_le_sub_left (Nat.le_add_right t _) _)
      (Nat.sub_le_sub_left (Nat.le_add_right t _) _)
  have hmonoR : ((M 0 - (t + (j : ℕ)) : ℕ) : ℝ) * ((M 1 - (t + (j : ℕ)) : ℕ) : ℝ)
      ≤ ((M 0 - t : ℕ) : ℝ) * ((M 1 - t : ℕ) : ℝ) := by exact_mod_cast hmono
  rw [Nat.cast_mul] at hlo
  linarith

/-! ## The direct `SJStepHyp` conditional + the `∀-M` capstone -/

/-- **A nondegenerate interior binding cut with nontrivial reduced chain.** The precondition of the
coupled route (`routeMBoxThresholdFinite_of_coupled`): `1 ≤ t`, `t + 1 ≤ min(M₀,M₁)` (interior), the
binding equality, and `0 < minAdm (redChain t M)` (nonempty `c'`-window / nontrivial reduced chain). -/
def NondegBindingCut (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ) : Prop :=
  1 ≤ t ∧ t + 1 ≤ min (M 0) (M 1)
    ∧ minAdm M = peelCharge M t + minAdm (redChain t M) ∧ 0 < minAdm (redChain t M)

/-- **The binding-shell rank-genericity bound `a+b+1 ≤ deepTailMin M`** (corankrec's `hrankgen`, supplied
from banked BackPeel). For a `≥ 4`-width chain at a nondegenerate binding cut `t` and an INTERIOR shell
`1 ≤ j < r = min(M₀−t, M₁−t)`, the widths satisfy `(M₀−(t+j)) + (M₁−(t+j)) + 1 ≤ deepTailMin M`. Chain:
BackPeel gives a co-minimizing deeper rank `ρ` of `redChain t M` with `(M₀−t)+(M₁−t)−1 ≤ ρ`
(`minAdm_backPeel_cominimizer_ge`) and `ρ ≤ tailMin (redChain t M) = deepTailMin M` (both
`= min(M₂,…,M_{last})`, via `Fin.cons_succ`); so `(M₀−t)+(M₁−t)−1 ≤ deepTailMin M`, and the interior
shift (`j ≥ 1`, `j < r` so no truncation) gives `(M₀−(t+j))+(M₁−(t+j))+1 = (M₀−t)+(M₁−t)−2j+1 ≤ deepTailMin M`.
NATIVE (pure ℕ + banked BackPeel). -/
theorem bindingShell_rankgen (M : Fin (L + 1 + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (hcut : NondegBindingCut M t) (hj1 : 1 ≤ j) (hjr : j < min (M 0 - t) (M 1 - t)) :
    (M 0 - (t + j)) + (M 1 - (t + j)) + 1 ≤ deepTailMin M := by
  obtain ⟨-, htb, hbind, -⟩ := hcut
  obtain ⟨ρ, hρtail, hρcomin, -⟩ :=
    exists_minAdm_backPeel_cominimizer_corankWidth M t htb hbind
  have hge := minAdm_backPeel_cominimizer_ge M t htb hbind ρ hρtail hρcomin
  have htail_eq : tailMin (redChain t M) = deepTailMin M := rfl
  rw [htail_eq] at hρtail
  omega

/-- **Degenerate sub-case (zero width): a chain with any zero width is box-finite (vacuously).** If some
`M i = 0` then `minAdm M = 0` (via `minAdm_leading_zero` for `i = 0`, or `minAdm_le_head_mul_tailInf`
+ `Finset.inf'_le` for a tail index — the tail `inf'` has a `0` member), so the threshold `c' < ½·minAdm M
= 0` is unsatisfiable for `c' : NNReal` and `RouteMBoxThresholdFinite M` holds vacuously. Discharges the
zero-width branch of `hdegen`. NATIVE. -/
theorem routeMBoxThresholdFinite_of_zero_width (M : Fin (L + 1 + 1 + 1) → ℕ)
    (i : Fin (L + 1 + 1 + 1)) (hi : M i = 0) : RouteMBoxThresholdFinite M := by
  have hmin : minAdm M = 0 := by
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact minAdm_leading_zero M hi
    · have h2 : minAdm M ≤ M 0 * M j.succ :=
        le_trans (minAdm_le_head_mul_tailInf M)
          (by gcongr; exact Finset.inf'_le _ (Finset.mem_univ j))
      rw [hi, Nat.mul_zero] at h2
      exact Nat.le_zero.mp h2
  intro c' hc'
  rw [hmin] at hc'
  simp only [Nat.cast_zero, zero_div] at hc'
  exact absurd hc' (not_lt.mpr c'.coe_nonneg)

/-- **The direct `SJStepHyp` from the coupled route + the degenerate handler.** Dispatches by arity: at
ARITY 3 (`L=0`, the step's induction floor) it bottoms at the banked arity-3 `(□)`
`routeMBoxThresholdFinite_mnp` — the coupled route is arity ≥ 4 (`bindingShell_rankgen` is `Fin (L+1+1+1+1)`),
so it CANNOT fill arity 3. At ARITY ≥ 4 (`L=succ`) it case-splits each chain `M`: if `M` has all-positive
widths AND a nondegenerate interior binding cut, the coupled route (`hcoupled`, WHICH TAKES the arity-IH — the
saturated boundary shell `j=r` reduces to the reduced chain via the IH, satred's saturated brick) gives
box-finiteness; otherwise (degenerate width `M₀=1`/`M₁=1`, boundary-argmin, or a zero width) the degenerate
handler `hdegen` — also WITH the arity-IH — gives it. This is the honest isolate-every-hole step: `hcoupled` is discharged by
`routeMBoxThresholdFinite_of_coupled` (consuming hG1/hfin/hbdryShell, with the IH feeding hbdryShell at
`j=r`); `hdegen` is the degenerate reduction-to-shorter-chain (genuine hole, uses the IH). No route touches
the gammaPeel/`sjJointResolution` sorry. -/
theorem sjStepHyp_of_coupled
    (hcoupled : ∀ {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ),
        (∀ i, 1 ≤ M i) → NondegBindingCut M t →
        (∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M') → RouteMBoxThresholdFinite M)
    (hdegen : ∀ {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ),
        ¬ ((∀ i, 1 ≤ M i) ∧ ∃ t, NondegBindingCut M t) →
        (∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M') → RouteMBoxThresholdFinite M) :
    SJStepHyp := by
  intro L
  cases L with
  | zero =>
    -- ARITY 3 (the induction floor for the step): the coupled route is arity ≥ 4
    -- (`bindingShell_rankgen`, corankrec's hfin support, is typed `Fin (L+1+1+1+1)`), so it CANNOT
    -- fill arity 3. Bottom the arity-3 case at the banked arity-3 `(□)` `routeMBoxThresholdFinite_mnp`.
    intro M _hIH
    have hM : M = ![M 0, M 1, M 2] := by funext i; fin_cases i <;> rfl
    have hmnp := routeMBoxThresholdFinite_mnp (M 0) (M 1) (M 2)
    rwa [← hM] at hmnp
  | succ L' =>
    -- ARITY ≥ 4: the coupled route (nondeg interior binding cut) or the degenerate handler.
    intro M hIH
    by_cases h : (∀ i, 1 ≤ M i) ∧ ∃ t, NondegBindingCut M t
    · obtain ⟨hnd, t, hcut⟩ := h
      exact hcoupled M t hnd hcut hIH
    · exact hdegen M h hIH

/-- **The `∀-M` box-finiteness capstone, conditional on the coupled route + the degenerate handler.**
Feeds `sjStepHyp_of_coupled` and the banked `L = 1` free-matrix base (`sjBase1_freeMatrix`) into the
banked sorry-free strong-arity-induction wrapper `routeMBoxThresholdFinite_of_step`. The induction bottoms
HONESTLY at every arity: arity 0/1 vacuous + arity 2 (`sjBase1_freeMatrix`) via the wrapper, and arity 3
inside `sjStepHyp_of_coupled` at the banked `routeMBoxThresholdFinite_mnp` (the coupled route is arity ≥ 4).
So `(hcoupled ∧ hdegen) ⟹ RouteMBoxThresholdFinite M` for EVERY width vector `M` — the coupled-route form of `(□)`,
NATIVE (no `cited_aoyagi_dln`, no gammaPeel/`sjJointResolution` sorry). The remaining holes are exactly
`hcoupled` (= hG1 [tpeel] ∧ hfin [per-cell on `j<r`: couplerad item 4 on `1≤j<r` + schurrec's
ChargedRectSchurCore at the generic entry `j=0`] ∧ hbdryShell [saturated shell `j=r`: satred/satbuild's
IH-fed brick]) and `hdegen` (the degenerate reduction). `hcoupled` takes the arity-IH (threaded from
`sjStepHyp_of_coupled`) for the `j=r` saturated reduction. -/
theorem routeMBoxThresholdFinite_coupled
    (hcoupled : ∀ {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ),
        (∀ i, 1 ≤ M i) → NondegBindingCut M t →
        (∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M') → RouteMBoxThresholdFinite M)
    (hdegen : ∀ {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ),
        ¬ ((∀ i, 1 ≤ M i) ∧ ∃ t, NondegBindingCut M t) →
        (∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M') → RouteMBoxThresholdFinite M)
    {L : ℕ} (M : Fin (L + 1) → ℕ) : RouteMBoxThresholdFinite M :=
  routeMBoxThresholdFinite_of_step (sjStepHyp_of_coupled hcoupled hdegen) sjBase1_freeMatrix M

end DLNFibre.DLN.RLCT
