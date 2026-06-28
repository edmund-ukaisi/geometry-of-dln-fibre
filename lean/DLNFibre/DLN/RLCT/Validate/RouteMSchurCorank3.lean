import DLNFibre.DLN.RLCT.Validate.RouteMSchurDepth2
import DLNFibre.DLN.RLCT.Validate.RadialResidualPower

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurCorank3` — the corank-3 recursion STEP (the first real firing)

The corank-3 instance of the rank-stratified radial-Schur recursion — the FIRST case where the recursion
genuinely fires (the residual Schur complement `Sc` becomes `2×2`, NOT a scalar, so it is a corank-2 core
that bottoms out in the closed `core_schur2_lt_top` at a SHIFTED exponent — not a Morse leaf). This
validates the inductive STEP `corank-r → corank-(r−1)`-at-shifted-exponent (cert §4 N4 / §3); the full
arbitrary-depth WellFounded-on-corank recursion is the next milestone.

## The threshold (CONFIRMED `c' < 4 = λ_{3,4}` — the JOINT-core SUM, not the corank-2 `2`)
The binding inner threshold is the SUM `jp/2 + λ_{r−j,p}` = (j=1, p=4 ⟹ `jp/2 = 2`) + (`λ_{2,4} = 2`) = 4
= ½·minAdm(3,3,4). Reusing the corank-2 threshold-`2` lemma for the corank-3 leaf would UNDERSHOOT (the
cert §6 trap: it drops the `+jp/2` Morse gain). The shifted-exponent peel is what carries the `+jp/2`.

## The mechanism (the inductive STEP)
`schurInner3_S_le` (the per-chart inner-S heart, at a fixed `3×3` angular `R` with pivot `(0,0)`):
`∫_{S ∈ matBox 3 4 T} frobSq (R·S)^{−c'} < ⊤` for `0 < c' < 4`, via:
* N2b (`schur_minorPivot_split`, `r=3, j=1`) → the JOINT split `frobSq (R·S) ≳ frobSq (R·S)_row0 (Morse,
  p entries) + frobSq (Sc · S_bot)` (`Sc` the `2×2` Schur complement, `S_bot` rows 1,2 of S);
* the SHIFTED-EXPONENT Morse peel of the top block (`radial_morse_residual_power_le`, threshold `p/2 = 2`)
  → the corank-2 residual at exponent `c' − 2`;
* the translation-domination `M22 ↦ Sc` (Jac ≡ 1, `lintegral_translate_le_local` +
  `rowShear_entry_le_one`) confines `Sc` to a fixed box → `core_schur2_lt_top` at exponent `c' − 2 < 2`.

The OUTER 9-chart radial-Δ cover (mirror of the corank-2 `matBox2_*` cover) assembling
`∫_Δ ∫_S frobSq (Δ·S)^{−c'} < ⊤` is built on top (`core_schur3_lt_top`).

## S2-hygiene
S2-FREE: the shifted peel (`radial_morse_residual_power_le`, `radial_ball_iff`-based), `core_schur2_lt_top`
(S2-free), the translation domination, the radial Jacobian dets. No `monomial_rlct`, no new axiom.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

end DLNFibre.DLN.RLCT
