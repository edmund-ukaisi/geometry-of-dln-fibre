import DLNFibre.DLN.RLCT.Validate.MatMulFibre
import DLNFibre.DLN.RLCT.Validate.RouteM4422
import DLNFibre.DLN.RLCT.Foundations.S1SmoothBlock

/-!
# `RouteM4422Hfin` — the `(4,4,2,2)` upper-bound finiteness (the hfin atom, S2-FREE)

The `(4,4,2,2)` instance of the hfin upper bound: for `c' < ½·minAdm M4422 = 2`,

    ∫⁻_{routeMBaseNbhd M4422} |routeMCore M4422 x|^{−c'} < ⊤.

This is the `cover_le` premise of `routeMLayerCover_of_atoms` for `M = (4,4,2,2)`, the companion of the
banked box-divergence atom `routeM4422_box_diverges` (the lower bound, `RouteM4422.lean`).

## The route (Codex-steered iterated fibre, thread 29; NOT the rank-stratified recursion)

`routeMCore M4422 x = frobSq (A0·A1·A2)` (`A0 : 4×4`, `A1 : 4×2`, `A2 : 2×2`), the 28 free flat
coords over the box `(−1,1)^28`. Tonelli-integrate the fibres outside-in:

  ∫_{A2}∫_{A1}∫_{A0} frobSq(A0·A1·A2)^{−c'}
    ≤ C0 · ∫_{A2}∫_{A1} frobSq(A1·A2)^{−c'}      [`fibre_lintegral_mul_le`, X = A0, Y = A1·A2, p=4]
    ≤ C0·C1 · ∫_{A2} frobSq(A2)^{−c'}            [`fibre_lintegral_mul_le`, X = A1, Y = A2,   p=4]
    < ⊤                                          [`sumSqND_box_lt_top`, A2 a 4-dim Morse block, c'<2]

Each fibre bound's constant `C0, C1` is `Y`-independent and finite (`fibreConst`); the threshold is
`p/2 = 2` at every step (`p = 4` rows in each layer's left factor). S2-FREE: only the matrix-product
fibre engine + the radial Morse terminal (`radial_ball_iff`), no `monomial_rlct`.

## STATUS — the connecting plumbing is the honest residual

The whole analytic engine is banked **sorry-free and S2-free** (`[propext, Classical.choice,
Quot.sound]`, no `monomial_rlct`): the fibre lemma `fibre_lintegral_mul_le`, the radial-Morse terminal
`radial_morse_dominates_lt_top`/`sumSqND_box_lt_top`, the A2 leaf `frobSq22_box_lt_top`, and the
assembled 3-fold iterated fibre `triple_fibre_lt_top` (`MatMulFibre`, `S1RadialMorse`). The remaining
step — pinned as the single `sorry` below — is the measure-preserving identification of
`routeMCore M4422` over `(−1,1)^28` with `triple_fibre_lt_top` (the `paramsEquivFlat`/`Params M4422`
entry reshape + the open-⊆-closed box monotone bound + the `c' = 0` trivial split). The MATH is
complete (Codex-survived, numerically verified, thread 29); this is `Params`-reshape bookkeeping that
rides the banked `prod_M4422_eq_rmatMul` + `dlnLoss_M4422_eq_frobSq` product identities.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal BigOperators

/-! ## The `Params M4422` ↔ triple-matrix bridge (the loss as a matrix-product Frobenius square) -/

/-- `dlnLoss M4422 0 A = frobSq (prod M4422 A)` (the loss at target `0` is the squared Frobenius norm
of the layer product). -/
theorem dlnLoss_M4422_eq_frobSq (A : Params M4422) :
    dlnLoss M4422 0 A = frobSq (prod M4422 A) := by
  unfold dlnLoss frobSq
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [Matrix.sub_apply, Matrix.zero_apply, sub_zero]

/-- The layer product `prod M4422 A` as the iterated raw matrix product `rmatMul (rmatMul A₀ A₁) A₂`
(entrywise; associativity of the three-factor product, via `prod_three_layer4422`). -/
theorem prod_M4422_eq_rmatMul (A : Params M4422) :
    (fun i j => prod M4422 A i j)
      = rmatMul (rmatMul (fun i k => A 0 i k) (fun k k2 => A 1 k k2)) (fun k2 j => A 2 k2 j) := by
  funext i j
  rw [prod_three_layer4422 M4422 A i j]
  unfold rmatMul
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k2 _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k1 _ => ?_)
  ring

/-- **The triple-matrix iterated-fibre finiteness** `∫⁻_{A2}∫_{A1}∫_{A0} frobSq(A0·A1·A2)^{−c'} < ⊤`
for `0 < c' < 2`, each layer box `[−1,1]`. The iterated-fibre core: apply `fibre_lintegral_mul_le`
to the A0-fibre (`Y = A1·A2`, p=4), then the A1-fibre (`Y = A2`, p=4), terminating at the A2 4-dim
Morse leaf (`sumSqND_box_lt_top`). All S2-free; the constants are `Y`-independent. -/
theorem triple_fibre_lt_top (c' : ℝ) (hc0 : 0 < c') (hc' : c' < 2) :
    ∫⁻ A2 in matBox 2 2 1, ∫⁻ A1 in matBox 4 2 1, ∫⁻ A0 in matBox 4 4 1,
      ENNReal.ofReal ((frobSq (rmatMul (rmatMul A0 A1) A2)) ^ (-c')) < ⊤ := by
  -- A0-fibre: ∫_{A0} frobSq((A0·A1)·A2)^{−c'} ≤ C0·frobSq(A1·A2)^{−c'} (X=A0, Y=A1·A2, p=4,n=4,q=2)
  have hc2 : c' < (4 : ℕ) / 2 := by norm_num; linarith
  have hstep0 : ∀ (A1 : Fin 4 → Fin 2 → ℝ) (A2 : Fin 2 → Fin 2 → ℝ),
      ∫⁻ A0 in matBox 4 4 1, ENNReal.ofReal ((frobSq (rmatMul (rmatMul A0 A1) A2)) ^ (-c'))
        ≤ fibreConst 4 4 2 1 c' * ENNReal.ofReal ((frobSq (rmatMul A1 A2)) ^ (-c')) := by
    intro A1 A2
    -- rmatMul (rmatMul A0 A1) A2 = rmatMul A0 (rmatMul A1 A2) (associativity)
    have hassoc : ∀ A0 : Fin 4 → Fin 4 → ℝ,
        rmatMul (rmatMul A0 A1) A2 = rmatMul A0 (rmatMul A1 A2) := by
      intro A0; funext i j
      unfold rmatMul
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k2 _ => Finset.sum_congr rfl (fun k1 _ => by ring))
    calc ∫⁻ A0 in matBox 4 4 1, ENNReal.ofReal ((frobSq (rmatMul (rmatMul A0 A1) A2)) ^ (-c'))
        = ∫⁻ A0 in matBox 4 4 1, ENNReal.ofReal ((frobSq (rmatMul A0 (rmatMul A1 A2))) ^ (-c')) := by
          refine setLIntegral_congr_fun (matBox_measurableSet _ _ _) (fun A0 _ => ?_)
          rw [hassoc A0]
      _ ≤ fibreConst 4 4 2 1 c' * ENNReal.ofReal ((frobSq (rmatMul A1 A2)) ^ (-c')) :=
          fibre_lintegral_mul_le (by norm_num) (by norm_num) (by norm_num) 1 one_pos c' hc0 hc2
            (rmatMul A1 A2)
  -- A1-fibre: ∫_{A1} frobSq(A1·A2)^{−c'} ≤ C1·frobSq(A2)^{−c'} (X=A1, Y=A2, p=4,n=2,q=2)
  have hstep1 : ∀ (A2 : Fin 2 → Fin 2 → ℝ),
      ∫⁻ A1 in matBox 4 2 1, ENNReal.ofReal ((frobSq (rmatMul A1 A2)) ^ (-c'))
        ≤ fibreConst 4 2 2 1 c' * ENNReal.ofReal ((frobSq A2) ^ (-c')) := by
    intro A2
    exact fibre_lintegral_mul_le (by norm_num) (by norm_num) (by norm_num) 1 one_pos c' hc0 hc2 A2
  -- A2 leaf: ∫_{A2} frobSq(A2)^{−c'} < ⊤ (4-dim Morse, c' < 2 = 4/2)
  have hmeasA0 : ∀ (A1 : Fin 4 → Fin 2 → ℝ) (A2 : Fin 2 → Fin 2 → ℝ),
      Measurable (fun A0 : Fin 4 → Fin 4 → ℝ =>
        ENNReal.ofReal ((frobSq (rmatMul (rmatMul A0 A1) A2)) ^ (-c'))) := by
    intro A1 A2
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    unfold frobSq rmatMul; fun_prop
  have hmeasA1 : ∀ (A2 : Fin 2 → Fin 2 → ℝ),
      Measurable (fun A1 : Fin 4 → Fin 2 → ℝ =>
        ENNReal.ofReal ((frobSq (rmatMul A1 A2)) ^ (-c'))) := by
    intro A2
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    unfold frobSq rmatMul; fun_prop
  -- chain the three bounds via monotonicity of the inner integrals
  calc ∫⁻ A2 in matBox 2 2 1, ∫⁻ A1 in matBox 4 2 1, ∫⁻ A0 in matBox 4 4 1,
          ENNReal.ofReal ((frobSq (rmatMul (rmatMul A0 A1) A2)) ^ (-c'))
      ≤ ∫⁻ A2 in matBox 2 2 1, ∫⁻ A1 in matBox 4 2 1,
          fibreConst 4 4 2 1 c' * ENNReal.ofReal ((frobSq (rmatMul A1 A2)) ^ (-c')) := by
        refine lintegral_mono (fun A2 => lintegral_mono (fun A1 => hstep0 A1 A2))
    _ = fibreConst 4 4 2 1 c' * ∫⁻ A2 in matBox 2 2 1, ∫⁻ A1 in matBox 4 2 1,
          ENNReal.ofReal ((frobSq (rmatMul A1 A2)) ^ (-c')) := by
        rw [← lintegral_const_mul' _ _ (fibreConst_ne_top 4 4 2 1 c' one_pos hc2 (by norm_num) (by norm_num))]
        refine setLIntegral_congr_fun (matBox_measurableSet _ _ _) (fun A2 _ => ?_)
        rw [lintegral_const_mul' _ _ (fibreConst_ne_top 4 4 2 1 c' one_pos hc2 (by norm_num) (by norm_num))]
    _ ≤ fibreConst 4 4 2 1 c' * ∫⁻ A2 in matBox 2 2 1,
          fibreConst 4 2 2 1 c' * ENNReal.ofReal ((frobSq A2) ^ (-c')) := by
        refine mul_le_mul_left' (lintegral_mono (fun A2 => hstep1 A2)) _
    _ = fibreConst 4 4 2 1 c' * fibreConst 4 2 2 1 c'
          * ∫⁻ A2 in matBox 2 2 1, ENNReal.ofReal ((frobSq A2) ^ (-c')) := by
        rw [lintegral_const_mul' _ _
          (fibreConst_ne_top 4 2 2 1 c' one_pos hc2 (by norm_num) (by norm_num)), mul_assoc]
    _ < ⊤ := by
        apply ENNReal.mul_lt_top (ENNReal.mul_lt_top
          (fibreConst_lt_top 4 4 2 1 c' one_pos hc2 (by norm_num) (by norm_num))
          (fibreConst_lt_top 4 2 2 1 c' one_pos hc2 (by norm_num) (by norm_num)))
        -- the A2 leaf: frobSq A2 = ∑_{k2 j} (A2 k2 j)² is a 4-dim sum of squares; finite for c' < 2
        exact frobSq22_box_lt_top 1 one_pos c' hc'

/-- **The `(4,4,2,2)` hfin upper bound (S2-FREE).** For `c' < ½·minAdm M4422 = 2`,
`∫⁻_{routeMBaseNbhd M4422} |routeMCore M4422 x|^{−c'} < ⊤`. The companion of the banked box-divergence
atom `routeM4422_box_diverges`; together they discharge the two analytic atoms of
`routeMLayerCover_of_atoms` for `M = (4,4,2,2)` (this side via the iterated matrix-product fibre engine
`fibre_lintegral_mul_le`, S2-free).

The residual `sorry` is the `Params`-reshape identification of `routeMCore M4422` over the 28-coord
box with `triple_fibre_lt_top` (the iterated-fibre core, banked sorry-free + S2-free). The full
analytic content — the two fibre bounds (`fibre_lintegral_mul_le`), the `c' < 2` threshold, and the
A2 Morse leaf (`frobSq22_box_lt_top`) — is banked sorry-free in `MatMulFibre`/`S1RadialMorse`. -/
theorem routeMCore_M4422_threshold_lt_top (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm M4422 : ℝ) / 2) :
    ∫⁻ x in routeMBaseNbhd M4422, ENNReal.ofReal (|routeMCore M4422 x| ^ (-(c' : ℝ))) < ⊤ := by
  sorry

end DLNFibre.DLN.RLCT
