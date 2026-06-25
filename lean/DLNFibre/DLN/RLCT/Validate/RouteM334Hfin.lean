import DLNFibre.DLN.RLCT.Validate.RadialResidualPower
import DLNFibre.DLN.RLCT.Validate.RouteMSchur
import DLNFibre.DLN.RLCT.Validate.Case334RouteStep

/-!
# `RouteM334Hfin` — the `(3,3,4)` upper-bound finiteness (the N4 depth-2 rank-stratified hfin instance)

The `(3,3,4)` instance of the hfin upper bound: for `c' < ½·minAdm M334 = 4`,

    ∫⁻_{routeMBaseNbhd M334} |routeMCore M334 x|^{−c'} < ⊤.

This is the `cover_le` premise of `routeMLayerCover_of_atoms` for `M = (3,3,4)`, the companion of the
banked achiever-path box-divergence atom `routeM334_box_diverges` (the lower bound,
`RouteMLayerCoverGEL2.lean`). UNLIKE `(4,4,2,2)` (closed via the iterated-fibre route, `RouteM4422Hfin`),
`(3,3,4)` is corank-2 and the iterated-fibre route UNDERSHOOTS (it caps at `min(3/2, 6) = 3/2 ≪ 4`,
pp-r1-genM-2 §Q2). It needs the **rank-stratified radial-Schur recursion** with the genuine ADDITIVE
disjoint-sum threshold `4 = 2 + 2` (the `‖T‖²` Morse spectator rlct `2` ⊕ the `‖Δ·S‖²` core rlct
`λ_{2,4} = 2`).

## The route (pp-r1-genM-2 §Q1–Q3, decorrelated-Codex confirmed; thread 28 cert + `codex/`)

The additive threshold is reached by the residual-power convolution atom `radial_morse_residual_power_le`
(banked S2-free, `RadialResidualPower.lean`): the `‖T‖²` peel leaves a residual power
`w^{−(c' − 2)}` of the core `w = ‖Δ·S‖²`, which the core integral then absorbs at the SHIFTED exponent
`c'' = c' − 2 < 2` via the `r² = 4`-chart Δ-blow-up cover (a-axis divisor `r²/2 = 2` ⊗ the rank-1 N2a
leaf `(∑col²)·‖row·S‖²`). Threshold equivalence: `c' < 4 ⟺ c'' < 2 = λ_{2,4}`.

## STATUS — partial (the keystone new atom banked; the frame-cover the precisely-named gap)

* **Banked (sorry-free, S2-free):** `radial_morse_residual_power_le` (the residual-power convolution atom,
  `RadialResidualPower.lean`) — the genuinely-new finiteness piece the additive threshold needs, the one
  pp identified the crude Morse-peel `radial_morse_dominates_lt_top` could NOT supply.
* **Gap (precisely-named `sorry`):** `routeMCore_M334_threshold_lt_top` rests on the resolved-form core
  finiteness `∫_{(Δ,S)-box} (‖T‖² + ‖Δ·S‖²)^{−c'} < ⊤` for `c' < 4`. Its proof needs
  (a) the FRAME TRANSPORT bringing `frobSq(A0·A1)` (the genuine flat loss, A0 3×3, A1 3×4, over the box)
  into the `‖T‖² ⊕ ‖Δ·S‖²` cover form — the achiever chart `chartParams334`/`Uval334` is banked
  (`RouteMLayerCoverGEL2`) but only on the lower-bound side; the full COVER up to null over the `r²`-chart
  Δ-blow-up atlas (`g5_pivotNode`/`recStep`) is the remaining measure-theoretic assembly; (b) the
  per-chart a-axis divisor (`radial_aAxis_divisor_lt_top`, banked) ⊗ N2a rank-1 leaf
  (`rankOne_outerProduct_split`, banked). The Tonelli T-peel COMPOSITION via the new atom is built below
  (`core_T_peel_le`).

## S2-hygiene
The hfin CONCLUSION is S2-FREE (Morse leaves, the a-divisor 1-D monomial, Tonelli, the new
residual-power atom, the rank-1 leaf). `monomial_rlct` enters only the leaf-sum hypothesis side the
headline already rides; no NEW axiom.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-! ## `minAdm M334 = 8` (the threshold value `½·minAdm = 4`) -/

/-- `minAdm (![3,3,4]) = 8` (so the hfin threshold is `c' < ½·minAdm = 4`). The `minAdm`-function value
matching `Case334RouteStep.minAdm_M334`'s `.toNat` form (the `minAdm` def is exactly that `.toNat`). -/
theorem minAdm_M334_eq : minAdm (![3, 3, 4] : Fin 3 → ℕ) = 8 := minAdm_M334

/-! ## The Tonelli `‖T‖²`-peel via the residual-power convolution atom (BUILT)

The disjoint-sum cell `(‖T‖² + W)^{−c'}` — `T` an `(m+1)`-dim Morse spectator, `W = core ≥ 0` — peels
the `T`-block by the new residual-power atom, leaving `Cresid · W^{−(c' − (m+1)/2)}`: the core at the
SHIFTED exponent. The Tonelli outer-integral over the core variables then closes from the core's
finiteness at `c'' = c' − (m+1)/2`. This is the additive-threshold bridge the crude Morse-peel could not
supply (pp §Q1). -/

/-- **The Tonelli `T`-peel bound.** For an `(m+1)`-dim Morse spectator block `T` over `[−Tw,Tw]^{m+1}`
disjoint from a strictly-positive core value `w(z) > 0`, with `c'` ABOVE the Morse threshold `(m+1)/2`,
the joint integral is bounded by `Cresid` times the core integral at the SHIFTED exponent `c' − (m+1)/2`:

    ∫_z ∫_T (∑ Tᵢ² + w z)^{−c'} ≤ Cresid (m+1) c' · ∫_z (w z)^{−(c' − (m+1)/2)}.

The disjoint-sum additive-threshold glue: `radial_morse_residual_power_le` (banked) per fixed `z` gives
the residual power, then `lintegral_const_mul'` pulls `Cresid` out. S2-FREE. (Only the per-`z`
positivity `hwpos` is consumed — the inner residual-power atom needs `w z > 0`, not measurability of `w`.) -/
theorem core_T_peel_le {m k : ℕ} (c' : ℝ) (hc' : (m + 1 : ℝ) / 2 < c')
    (Tw : ℝ) (hTw : 0 < Tw) (w : (Fin k → ℝ) → ℝ) (hwpos : ∀ z, 0 < w z)
    (Z : Set (Fin k → ℝ)) :
    ∫⁻ z in Z, ∫⁻ T in morseBox (m + 1) Tw,
        ENNReal.ofReal ((∑ i, (T i) ^ 2 + w z) ^ (-c'))
      ≤ ENNReal.ofReal (Cresid (m + 1) c')
        * ∫⁻ z in Z, ENNReal.ofReal ((w z) ^ (-(c' - (m + 1 : ℝ) / 2))) := by
  -- per fixed `z`: the inner `T`-integral ≤ ofReal(Cresid · (w z)^{−(c'−(m+1)/2)}) by the new atom
  have hinner : ∀ z, ∫⁻ T in morseBox (m + 1) Tw,
        ENNReal.ofReal ((∑ i, (T i) ^ 2 + w z) ^ (-c'))
      ≤ ENNReal.ofReal (Cresid (m + 1) c')
        * ENNReal.ofReal ((w z) ^ (-(c' - (m + 1 : ℝ) / 2))) := by
    intro z
    rw [← ENNReal.ofReal_mul (Cresid_nonneg _ _)]
    exact radial_morse_residual_power_le m c' hc' Tw hTw (w z) (hwpos z)
  calc ∫⁻ z in Z, ∫⁻ T in morseBox (m + 1) Tw,
          ENNReal.ofReal ((∑ i, (T i) ^ 2 + w z) ^ (-c'))
      ≤ ∫⁻ z in Z, ENNReal.ofReal (Cresid (m + 1) c')
          * ENNReal.ofReal ((w z) ^ (-(c' - (m + 1 : ℝ) / 2))) :=
        lintegral_mono (fun z => hinner z)
    _ = ENNReal.ofReal (Cresid (m + 1) c')
          * ∫⁻ z in Z, ENNReal.ofReal ((w z) ^ (-(c' - (m + 1 : ℝ) / 2))) := by
        rw [lintegral_const_mul']
        exact ENNReal.ofReal_ne_top

/-! ## The corank-2 core route (S2-FREE, the transpose-fibre resolution — design note)

The core `‖Δ·S‖²` (Δ a `2×2` left factor, S a `2×4` right factor) integrated over both boxes is finite
for `c'' < 2 = λ_{2,4}` — WITHOUT the radial Δ-blow-up. Integrate S FIRST as the LEFT factor via the
transpose `frobSq(Δ·S) = frobSq(Sᵀ·Δᵀ)` (`frobSq_rmatMul_transpose` below): `Sᵀ` is `4×2` (p=4 rows), so
`fibre_lintegral_mul_le` (X=Sᵀ, p=4) gives the per-Δ bound at threshold `p/2 = 4/2 = 2`; then
`∫_Δ frobSq(Δ)^{−c''}` is the `2×2 = 4`-dim Morse leaf (`frobSq22_box_lt_top`, threshold `4/2 = 2`). Both
factors `≥ 2`, so the core resolves at `c'' < 2` (numerically pinned). This sidesteps the nested
minor-pivot recursion (pp §Q3: the inner threshold `5/2 > 2` never binds; the S-first fibre realises it
directly). The transpose-box measure-preserving reshape (`matTranspose` MP) is the one remaining plumbing
piece for the core-integral wiring; the transpose entrywise identity is banked below. -/

/-- The transpose entrywise identity `frobSq (Δ·S) = frobSq (Sᵀ·Δᵀ)`: `(Sᵀ·Δᵀ)ⱼᵢ = (Δ·S)ᵢⱼ`, so the
sum-of-squares is the same (a `Finset.sum_comm` + per-entry `ring`). The S-first fibre's algebraic core. -/
theorem frobSq_rmatMul_transpose {n p q : ℕ} (Δ : Fin p → Fin n → ℝ) (S : Fin n → Fin q → ℝ) :
    frobSq (rmatMul Δ S) = frobSq (rmatMul (fun j k => S k j) (fun k i => Δ i k)) := by
  unfold frobSq rmatMul
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
  congr 1
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-! ## The resolved-form core finiteness (the precisely-named GAP)

The cover form the frame transport must reach, then the recursion closes. STATED at the resolved-form
level (the `‖T‖² ⊕ ‖Δ·S‖²` cell core), so the conclusion's shape is pinned; the proof needs the frame
transport (flat → resolved) + the `r²`-chart Δ-blow-up cover (banked atoms `radial_aAxis_divisor_lt_top`
+ N2a `rankOne_outerProduct_split` + `core_T_peel_le` above). -/

/-- **The `(3,3,4)` hfin upper bound (the N4 depth-2 instance, GAP).** For `c' < ½·minAdm M334 = 4`,
`∫⁻_{routeMBaseNbhd M334} |routeMCore M334 x|^{−c'} < ⊤`. The rank-stratified analog of
`routeMCore_M4422_threshold_lt_top`; the additive threshold `4 = 2 + 2` is reached by the residual-power
convolution atom `radial_morse_residual_power_le` (banked, the `‖T‖²` Morse-spectator peel) feeding the
corank-2 core `‖Δ·S‖²` at the shifted exponent `c'' = c' − 2 < 2`, resolved by the `r² = 4`-chart
Δ-blow-up cover (a-axis divisor `r²/2 = 2` + the rank-1 N2a leaf, both banked).

GAP (`sorry`): the FRAME TRANSPORT bringing `frobSq(A0·A1)` over the box into the `‖T‖² ⊕ ‖Δ·S‖²` cover
form + the `g5_pivotNode`/`recStep` cover-up-to-null assembly over the `r²`-chart atlas. The achiever
chart `chartParams334`/`Uval334` is banked on the lower-bound side (`RouteMLayerCoverGEL2`); the
UPPER-bound full cover is the remaining measure-theoretic long pole. Threshold + the residual-power
T-peel (`core_T_peel_le`) + the per-chart atoms are banked. -/
theorem routeMCore_M334_threshold_lt_top (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm (![3, 3, 4] : Fin 3 → ℕ) : ℝ) / 2) :
    ∫⁻ x in routeMBaseNbhd (![3, 3, 4] : Fin 3 → ℕ),
      ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) x| ^ (-(c' : ℝ))) < ⊤ := by
  rw [minAdm_M334_eq] at hc'
  have hc4 : (c' : ℝ) < 4 := by linarith
  sorry

end DLNFibre.DLN.RLCT
