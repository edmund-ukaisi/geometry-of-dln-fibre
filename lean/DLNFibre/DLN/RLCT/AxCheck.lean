import DLNFibre.DLN.RLCT.Validate.Case111
import DLNFibre.DLN.RLCT.Validate.Case212
import DLNFibre.DLN.RLCT.Foundations.S1ProductMin
import DLNFibre.DLN.RLCT.Validate.Case222Algebra
import DLNFibre.DLN.RLCT.Validate.Case222Rlct
import DLNFibre.DLN.RLCT.Validate.RouteMFrontBottleneck
import DLNFibre.DLN.RLCT.Validate.RouteMSchurCorank3
import DLNFibre.DLN.RLCT.Validate.RouteMBoxThresholdRRP
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedSquareL2
import DLNFibre.DLN.RLCT.Validate.DeepestL2Wiring
import DLNFibre.DLN.RLCT.Foundations.S1QuasiSplit
import DLNFibre.DLN.RLCT.Validate.D1ChartProducer

/-!
# Axiom-hygiene check

Emits `#print axioms` for the load-bearing results on every build (imported by the `DLNFibre`
aggregator), so axiom regressions are caught by the standard green-gate rather than only by an
ad-hoc check.

Reading the output:
* **clean** = `[propext, Classical.choice, Quot.sound]` — fully proven, no citation, no `sorry`.
* `+ monomial_rlct` — the single permitted S2 citation (the bare weighted-monomial-integral fact).
* `sorryAx` — an unproven rung underneath. **Expected** on `aoyagi_learning_coefficient` until the
  5 Skeleton rungs (L2 `product_reduction`, D1 `deepest_point_reduction`-≥, R1 `resolution_charts`,
  A1 ×2) are proven; it must **not** appear on any result below that claims to be proven.

This file is `#print`-only — it adds no definitions and no axioms of its own.
-/

open DLNFibre.DLN.RLCT

-- (1,1,1) + (2,1,2) validate showcases — must stay axiom-free.
#print axioms case111_rlct
#print axioms resolution_charts_case111
#print axioms case212_rlct

-- S1 substrate (the heaviest analytic rung) + product-MIN engine — must stay clean.
#print axioms rlct_additive_smooth_block
#print axioms product_min_rlct
#print axioms product_min_rlct_of_ne

-- (2,2,2) loss-identity seam (#83) — pure matrix algebra (`prod_two_layer` + flat coords + `ring`).
-- Must stay clean: NO `monomial_rlct` (the seam's S2-dependence is downstream in the cover), NO `sorryAx`.
#print axioms dlnLoss222_eq_myF222

-- (2,2,2) ≤-direction cover headline (#80, the hard half) — carries `monomial_rlct`, the PERMITTED S2
-- citation (the threshold value rests on S2 via the box-divergence atom). Must be
-- [propext, Classical.choice, Quot.sound, monomial_rlct] — NO `sorryAx`. (Contrast dlnLoss222 above,
-- which must stay monomial_rlct-FREE: the S2-dependence enters here, in the singular cover.)
#print axioms rlctAtOn_myF222_le

-- (2,2,2) ≥-direction cover headline (#86) — the GEOMETRIC content. Must be CLEAN-THREE
-- [propext, Classical.choice, Quot.sound] — S2-FREE (no `monomial_rlct`), no `sorryAx`: the ≥-cover
-- (recStep 24-leaf g5_pivotNode + δ-branch smooth-block + conjugation A-pivots) carries no cited bound.
#print axioms rlctAtOn_myF222_ge'

-- (2,2,2) `=` value (#80) — `le_antisymm` of the ≥ (clean) + the ≤ (monomial_rlct). Must be
-- [propext, Classical.choice, Quot.sound, monomial_rlct] — NO `sorryAx` (the only citation enters via
-- the ≤-half; the ≥-content is citation-free).
#print axioms rlctAtOn_myF222_eq

-- (2,2,2) network headline (#107, ladder 3/3) — `rlctAt (dlnLoss H222) deepest222 = 3/2`, via the
-- m.p. transport ∘ the loss-identity seam ∘ the `=` value. Same axiom profile as `_eq`:
-- [propext, Classical.choice, Quot.sound, monomial_rlct], NO `sorryAx`.
#print axioms case222_rlct

-- R1-LOWER ∀M-(1,1)-smeared front fact (`prodAux_frontScalarShear_cancel`, the cert's biggest-risk piece) —
-- must be CLEAN-THREE [propext, Classical.choice, Quot.sound]: S2-FREE (literal outer-product cancellation,
-- no analysis axiom), no `sorryAx`.
#print axioms prodAux_frontScalarShear_cancel

-- R1-LOWER ∀M smeared-square achiever (`routeMCore_smearedL2_square_uncond`, the box-divergence for the
-- smeared L=2 square stratum `M0<M1 & r=M0`, ARBITRARY M) — must be CLEAN-THREE
-- [propext, Classical.choice, Quot.sound]: S2-FREE (the divergence rests on the diag-dominance Varah
-- field-A bound + the 1D `abs_rpow` first principle, NOT on `monomial_rlct`), no `sorryAx`. Its compile
-- cone is sorry-free; the three analytic per-family facts (hcancel/hUpos/hSpre) are discharged.
#print axioms routeMCore_smearedL2_square_uncond

-- R1-UPPER corank-3 (the rank-stratified recursion's first real firing) — `core_schur3_lt_top`
-- (general-`T`, `∫_{matBox 3 3 T}∫_{matBox 3 4 T} frobSq(Δ·S)^{−c'} < ⊤` for `0 < c' < 4 = λ_{3,4}`)
-- + the reusable matrix-box scaling primitive `lintegral_matBox_smul`. Must be CLEAN-THREE
-- [propext, Classical.choice, Quot.sound]: S2-FREE, no `sorryAx` (despite the imported (3,3,4)-lineage
-- closure carrying unrelated sorries in RouteMRecursion/RouteMSchur — they do not leak here).
#print axioms core_schur3_lt_top
#print axioms lintegral_matBox_smul

-- R1-UPPER ∀p leg (the rank-stratified radial-Schur recursion at every corank) — `routeMBoxThresholdFinite_rrp`
-- (`∫_{matBox r (r+p) T} frobSq(R·S)^{−c'} < ⊤` for `0 < c' < ½·minAdm r (r+p)`, all `r, p`), via the
-- clean-three chain `schurCoreP_two → schurCoreP_capA → schurRecStep_p → routeMBoxThresholdFinite_rrp`.
-- Must be CLEAN-THREE [propext, Classical.choice, Quot.sound]: S2-FREE, no `monomial_rlct`, no `sorryAx`.
#print axioms routeMBoxThresholdFinite_rrp

-- L2 Skeleton rung 1/5 (`product_reduction`) at L=2 — `deepest_gauge_construction_L2`, the standalone
-- clean-three L=2 witness for the deepest-point gauge-slice diffeo construction (the geometric obligation
-- of L2). Must be CLEAN-THREE [propext, Classical.choice, Quot.sound]: the L=2 arm is sorry-free
-- (geometric, S2-FREE, no `monomial_rlct`), no `sorryAx`.
#print axioms deepest_gauge_construction_L2

-- L2 gauge-construction at general L — `deepest_gauge_construction` dispatches L<3 to the clean-three
-- `_L2` witness and carries the #120-tracked L≥3-arm sorries (the grouped recursive diffeo, RESEARCH-RISK
-- roadmapped). Expected `sorryAx` until #120 closes; tracked here so the day it goes clean is visible.
#print axioms deepest_gauge_construction

-- D1 (rung 2/5) (★)-deliverer engine — the analytic quasi-split RLCT lower bound (network-free,
-- reusable; sidesteps the full Gromoll–Meyer Morse lemma via quasi-split-by-constant-comparison). Must be
-- CLEAN-THREE [propext, Classical.choice, Quot.sound], no `sorryAx`: rlct_quasiSplit_ge (the abstract
-- post-chart (★)-deliverer) + rlct_smooth_block_ge (m-fold step_rlct_ge, general residual) +
-- coupled_controls_slice (the pure Lipschitz-comparison inequality). The D1 use-site (the IFT-chart
-- producer for the DLN loss at a general v) consumes these; reviewer-PASS, non-vacuity tight.
#print axioms rlct_quasiSplit_ge
#print axioms rlct_smooth_block_ge
#print axioms coupled_controls_slice

-- D1 (rung 2/5) (★) chart-producer reductions — both must be CLEAN-THREE
-- [propext, Classical.choice, Quot.sound], no `sorryAx`: they are CONDITIONAL reductions (carry the
-- producer obligations as hypotheses), NOT a D1 closure. `rlctAt_ge_nReg_add_slice` delivers the
-- (★) `hAtV` side from the IFT-chart producer's outputs via the banked engine `rlct_quasiSplit_ge`;
-- `deepest_le_of_optimal_chart` wires it through `deepest_le_of_optimal_via_L2_ge` to the exact
-- `rlctAt_deepest_le_of_optimal` per-point conclusion, reduced to (i) the IFT chart + (ii) `hDeepest`
-- (=#44) + (iii) `hCore` (the network-free leading-form RLCT lower bound). They BANK the D1 reduction;
-- the day (i)/(ii)/(iii) discharge, D1 (Skeleton rung 2/5) closes.
#print axioms rlctAt_ge_nReg_add_slice
#print axioms deepest_le_of_optimal_chart
-- D1 PART (b) interface (the `hCore` discharge): `hCore_slice_residual_eq` — the slice residual `R`
-- equals the reduced core pulled back along a bounded-unit local diffeo `Φ` (the G1 `I+G` inner
-- factor) ⟹ `rlctAtOn R = rlctAtOn core₀` (diffeo transfer + spectator peel). Conditional on the
-- producer's diffeo data; must be CLEAN-THREE [propext, Classical.choice, Quot.sound], no `sorryAx`.
#print axioms hCore_slice_residual_eq

-- Headline — sorryAx expected (5 rungs pending); tracked here so the day it goes clean is visible.
#print axioms aoyagi_learning_coefficient
