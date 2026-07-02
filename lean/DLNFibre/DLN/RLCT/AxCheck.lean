import DLNFibre.DLN.RLCT.Validate.Case111
import DLNFibre.DLN.RLCT.Validate.Case212
import DLNFibre.DLN.RLCT.Foundations.S1ProductMin
import DLNFibre.DLN.RLCT.Validate.Case222Algebra
import DLNFibre.DLN.RLCT.Validate.Case222Rlct
import DLNFibre.DLN.RLCT.Validate.RouteMFrontBottleneck
import DLNFibre.DLN.RLCT.Validate.RouteMSchurCorank3
import DLNFibre.DLN.RLCT.Validate.RouteMBoxThresholdRRP
import DLNFibre.DLN.RLCT.Validate.RouteMSchurRectCapB
import DLNFibre.DLN.RLCT.Validate.RouteMHDtotEihd
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedSquareL2
import DLNFibre.DLN.RLCT.Validate.DeepestL2Wiring
import DLNFibre.DLN.RLCT.Validate.DeepestLastBlock
import DLNFibre.DLN.RLCT.Validate.DeepestFrontGauge
import DLNFibre.DLN.RLCT.Validate.DeepestNormalFormFrontPivotL2
import DLNFibre.DLN.RLCT.Foundations.S1QuasiSplit
import DLNFibre.DLN.RLCT.Foundations.S1IFTProducer
import DLNFibre.DLN.RLCT.Foundations.S1ChartTransfer
import DLNFibre.DLN.RLCT.Foundations.S1IFTChart
import DLNFibre.DLN.RLCT.Validate.D1IFTResidualProducer
import DLNFibre.DLN.RLCT.Validate.D1HChartResidual
import DLNFibre.DLN.RLCT.Validate.D1SecondPeelAssembly
import DLNFibre.DLN.RLCT.Validate.D1SecondPeelMinor
import DLNFibre.DLN.RLCT.Validate.D1SecondPeelGlueL2
import DLNFibre.DLN.RLCT.Validate.D1ChartProducer
import DLNFibre.DLN.RLCT.Validate.D1ChartProducerL2
import DLNFibre.DLN.RLCT.Validate.D1ChartProducerL2Build
import DLNFibre.DLN.RLCT.Validate.RouteMBData222
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedAchieverGeneral
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedSquareReduce
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedHSmearedL2
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorDeepRank0Atom
import DLNFibre.DLN.RLCT.Validate.HeadlineL2Assembly
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenAtom
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenWire

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

-- R1-UPPER general-(M0,M1,M2) L=2 leg (the rectangular-Schur extension): the real `min(m,n)` recursion
-- `rectSchurRecStep_mnp` + the box-finiteness `routeMBoxThresholdFinite_mnp` must be CLEAN-THREE [propext,
-- Classical.choice, Quot.sound] (S2-FREE, no sorryAx); `routeMLayerCover_coverLe_mnp` adds only the
-- permitted `monomial_rlct` (hfin leaf side, NO new axiom — same S2 the headline rides). Item-97 regime (ii).
#print axioms rectSchurRecStep_mnp
#print axioms routeMBoxThresholdFinite_mnp
#print axioms routeMLayerCover_coverLe_mnp

-- L2 Skeleton rung 1/5 (`product_reduction`) at L=2 — `deepest_gauge_construction_L2`, the standalone
-- clean-three L=2 witness for the deepest-point gauge-slice diffeo construction (the geometric obligation
-- of L2). Must be CLEAN-THREE [propext, Classical.choice, Quot.sound]: the L=2 arm is sorry-free
-- (geometric, S2-FREE, no `monomial_rlct`), no `sorryAx`.
#print axioms deepest_gauge_construction_L2

-- hJfront re-arch (genm-44l2, reviewer genm-rev-hjfront SURVIVED) — the #44-L2 value side made
-- HEADLINE-CLOSEABLE by replacing the unprovable hJfront with the provable precursor `hcolfront`. All
-- must be CLEAN-THREE [propext, Classical.choice, Quot.sound], no `sorryAx`:
-- `deepest_regular_core_normal_form_L2_front` = Skeleton #44 conclusion at L=2, conditional ONLY on
-- htop[#154] + hcolfront[#100] + hRValue[R1] (no hJfront); `exists_frontPivotFrame_lastBlock_isUnit`
-- (front-preferring chooser, J=frontEmbed) + `deepestPoint_lastBlock_front_rank` (column-dual) are the
-- hard atoms; `deepest_gauge_construction_L2_ofBundle` is the Route-X parameterized gauge body.
#print axioms deepest_regular_core_normal_form_L2_front
#print axioms exists_frontPivotFrame_lastBlock_isUnit
#print axioms deepestPoint_lastBlock_front_rank
#print axioms deepest_gauge_construction_L2_ofBundle

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

-- R1-LOWER generic achiever, BOUNDARY-SMEARED branch ASSEMBLY — must be CLEAN-THREE
-- [propext, Classical.choice, Quot.sound], S2-FREE, no `sorryAx`: `routeMCore_box_diverges_of_smearedChart`
-- (box divergence from a `SmearedAchieverChart M` bundle) + `hSmeared_of_smearedChart` (the spine's
-- `hSmeared` slot from a chart-builder — a CONDITIONAL reduction, NOT a closure). They REDUCE the smeared
-- branch ∀M to "construct one chart-builder `BoundarySmeared M → SmearedAchieverChart M`"; the (2,3,1)
-- witness `routeM231sm_box_diverges_via_smearedChart` confirms the structure is non-vacuous.
#print axioms routeMCore_box_diverges_of_smearedChart
#print axioms hSmeared_of_smearedChart
#print axioms routeM231sm_box_diverges_via_smearedChart

-- D1 obligation (i) at L=2 — the IFT-chart producer REDUCTION. Must be CLEAN-THREE
-- [propext, Classical.choice, Quot.sound], no `sorryAx`: `deepest_le_of_optimal_of_chart_certificate`
-- proves `rlctAt deepest ≤ rlctAt v` from a `GeneralVChartL2` certificate + #44 (the producer route).
-- It REDUCES D1 to {a GeneralVChartL2 instance at the real DLN loss (the general-v Morse-Bott chart,
-- a major multi-tide build Mathlib lacks) + #44}; it does NOT close D1. `GeneralVChartL2.ofExactGerm`
-- is the (degenerate) non-vacuity witness (the real nReg>0 instance is the unbuilt analytic existence).
#print axioms deepest_le_of_optimal_of_chart_certificate
#print axioms GeneralVChartL2.ofExactGerm

-- R1-LOWER BOUNDARY-SMEARED branch CLOSED ∀M at L=2 — must be CLEAN-THREE
-- [propext, Classical.choice, Quot.sound], S2-FREE, no `sorryAx`: `hSmeared_squareSmeared_L2` is the
-- spine-feeding closer (box-divergence ∀M for `1≤minAdm ∧ BoundarySmeared`), `smeared_deepRank_eq_M0`
-- the Lean-proved square reduction (the scope collapse — the smeared regime at L=2 is ALWAYS square),
-- `smearedChart_of_square` the chart assembly. These CLOSE the smeared atom OUTRIGHT (not reduced); the
-- R1-LOWER generic achiever then needs only `hInterior` (the interior-det atom) + the spine wiring.
#print axioms hSmeared_squareSmeared_L2
#print axioms smeared_deepRank_eq_M0
#print axioms smearedChart_of_square

-- R1-LOWER BOUNDARY-SMEARED branch, the spine's `hSmeared` SLOT at L=2 (the named atom genm-r1lower's
-- spine wiring consumes) — must be CLEAN-THREE [propext, Classical.choice, Quot.sound], S2-FREE, no
-- `sorryAx`: `hSmeared_L2` is the closer `hSmeared_squareSmeared_L2` CURRIED into the exact slot shape
-- `(2 ≤ L) → BoundarySmeared M → BoxDiverges M c' ε`; `hSmeared_L2_apply` is the uncurried reading.
#print axioms hSmeared_L2
#print axioms hSmeared_L2_apply

-- ★ R1-LOWER VALUE LEG CLOSED ∀M at L=2 (the interior TRICHOTOMY assembled) — `routeMCore_box_diverges_
-- achiever_L2` (M : Fin 3 → ℕ) must be CLEAN modulo the single cited S2 axiom, i.e.
-- [propext, Classical.choice, Quot.sound, monomial_rlct], no `sorryAx`. It combines the interior
-- `0 < deepRank` atom (`routeMCore_box_diverges_interiorLive`) + the deepRank=0 handler
-- (`routeMCore_box_diverges_eDeepRank0`, E-fixed-pivot chart, det EXACTLY single-axis |u_p|^{minAdm−1},
-- cov PURE monomial) + the smeared branch + the clean-branch hNo (derived IN-BRANCH from the clean
-- equality, NOT a false flat hNo forced through the spine). The general-L `routeMCore_box_diverges_
-- achiever` stays OPEN (#120-gated). `eDeepRank0Unit_ae_pos` is S2-FREE clean-three (nonzero-poly witness).
#print axioms routeMCore_box_diverges_achiever_L2
#print axioms routeMCore_box_diverges_eDeepRank0
#print axioms routeMCore_box_diverges_interiorLive
#print axioms eDeepRank0Unit_ae_pos

-- ★ GENERAL-`L` INTERIOR box-divergence atom (the general-`L` lift of `routeMCore_box_diverges_interiorLive`
-- above) — `routeMCore_box_diverges_interiorLiveGen` must be CLEAN modulo the single cited S2 axiom, i.e.
-- [propext, Classical.choice, Quot.sound, monomial_rlct], no `sorryAx` (identical to the L=2 analog). Its
-- `NodeAchieverChart` bundle `interiorLiveNodeChartGen` must be CLEAN-THREE [propext, Classical.choice,
-- Quot.sound]: the staggered staircase-conjugated leaf Jacobian (`DtotGen_abs_det`, det `∏|det K_s|^{r_s+c_s}`)
-- + the general-`L` injOn/analytic legs carry no cited bound (the S2 dependence enters only in the
-- box-divergence atom's threshold, via `monomial_rlct`).
#print axioms routeMCore_box_diverges_interiorLiveGen
#print axioms interiorLiveNodeChartGen

-- ★ GENERAL-`L` INTERIOR `hInterior` DISCHARGE on the `0 < deepRank` sub-stratum — the thin wire of the
-- atom above into the achiever-dispatch spine's `hInterior` slot. `interiorLiveGen_hInterior_of_deepRank_pos`
-- (the `∀ _ : 2 ≤ L`-shaped consumer form) + `routeMCore_box_diverges_interiorLiveGen_of_deepRank_pos`
-- (the uncurried atom application) must inherit the atom's footprint exactly:
-- [propext, Classical.choice, Quot.sound, monomial_rlct], no `sorryAx`. The `deepRank M = 0` sub-stratum
-- (L ≥ 3) is the remaining general-`L` interior gap (banked at L = 2 only via `eDeepRank0`).
#print axioms interiorLiveGen_hInterior_of_deepRank_pos
#print axioms routeMCore_box_diverges_interiorLiveGen_of_deepRank_pos

-- ★ R1 RESOLUTION INTERFACE at L=2 — the LEAF-1 wiring discharging the L2 headline's `hR1_L2`.
-- Must be CLEAN modulo the cited S2 axiom: [propext, Classical.choice, Quot.sound, monomial_rlct],
-- no `sorryAx`. `r1_resolution_interface_L2` = `rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)`
-- ∀ nondeg M:Fin3, assembled from `achiever_L2` (R1-LOWER) + `routeMBoxThresholdFinite_mnp` (R1-UPPER)
-- as the two `routeMLayerCover_of_atoms` atoms + the value lane. On wiring,
-- `aoyagi_learning_coefficient_L2`'s ONLY remaining `sorryAx` is the D1 wall (hD1ge_L2, Item-109).
#print axioms r1_resolution_interface_L2

-- D1 obligation (i) middle-stratum producer (square-deepest scope) — must be CLEAN-THREE
-- [propext, Classical.choice, Quot.sound], no `sorryAx`: `extra_half_add_lambdaCore_Mprime_ge_square` is
-- the UNCONDITIONAL §6 arithmetic (lambdaCore(square m) ≤ extra/2 + lambdaCore(M')); `hCore_middle_stratum_
-- of_interface` + `deepest_le_of_optimal_middle_stratum` are CONDITIONAL clean-three reductions (chart DATA
-- + the §5 R1-resolution interface + #44 as named hypotheses — the chart instance is unbuilt, the genuine
-- residual). They bank the case-B (middle-stratum) reduction-chain; the chart construction is the open piece.
#print axioms extra_half_add_lambdaCore_Mprime_ge_square
#print axioms hCore_middle_stratum_of_interface
#print axioms deepest_le_of_optimal_middle_stratum

-- D1 §SEL producer (Altitude A, network-free) — must be CLEAN-THREE [propext, Classical.choice,
-- Quot.sound], no `sorryAx`: `rlctAtOn_quasiSplit_ge_of_contDiff_residual` CONSTRUCTS the engine's hcmp
-- from ANY C¹ residual `q` (the §SEL collapse to `rlct_quasiSplit_ge`, D-INDEPENDENT — no new Mathlib
-- lemma / Morse-Bott / operator-√); `deepest_le_of_optimal_of_iftResidual` wires it through the banked
-- two-peel to the per-point `rlctAt deepest ≤ rlctAt v`. CONDITIONAL reductions: carry hchart/hchart₂
-- (the Altitude-B DLN IFT chart-transfer — where D-nonvanishing lives), hDeepest (#44), hDegraded
-- (R1-at-M') as NAMED hyps; they do NOT close the D1 rung. Double-decorrelated PASS (genm-d1prod
-- reviewer + lean-formaliser §QA). The §SEL win: chart-DATA (hF/hQ0/hcmp) removed from the hyp list.
#print axioms rlctAtOn_quasiSplit_ge_of_contDiff_residual
#print axioms deepest_le_of_optimal_of_iftResidual

-- D1 ≥-leg L=2 de-risk (genm-d1asm @70cb36ba; reviewer genm-rev-d1 SURVIVED 6/6) — must be CLEAN-THREE
-- [propext, Classical.choice, Quot.sound], no `sorryAx`: `exists_secondPeel_minor` produces hminor₂ (the
-- extra×extra Jacobian-minor non-degeneracy) from a rank bound; `rlctAt_deepest_le_of_optimal_L2` is the
-- L=2 Skeleton reduction (via Route A `deepest_le_of_optimal_secondPeel_discharged`), CONDITIONAL on the
-- two named-open gates #44/hDeepest + hInterface/R1 — NOT wired into Skeleton:1172 (stays a conditional component).
#print axioms exists_secondPeel_minor
#print axioms rlctAt_deepest_le_of_optimal_L2

-- D1 Altitude-B abstract hchart (network-free) — must be CLEAN-THREE [propext, Classical.choice,
-- Quot.sound], no `sorryAx`: `exists_boundedUnit_chart_of_contDiffAt` is THE hard piece (det DΨ≠0
-- PROVEN not posited at GENERAL wstar — via LinearEquiv.isUnit_det' + continuity, NO rank-exact-pivot),
-- `rlctAtOn_eq_of_contDiff_chart` chains it with the chart-transfer atom = the general chart-transfer.
-- Complete reusable lemmas (no carried obligations); lean-formaliser §QA-B PASS (gates 1+4). The DLN
-- use-site instantiates with the §SEL selected-minor Φ + the H_indep block-invertible f'.
#print axioms exists_boundedUnit_chart_of_contDiffAt
#print axioms rlctAtOn_eq_of_contDiff_chart

-- D1 hchart slot (#225/#231) — `dln_hchart_residual`: the assembled §SEL `hchart` (selected-minor IFT
-- chart + germ-decompose + bump-globalize), the chart-transfer obligation `deepest_le_of_optimal_of_
-- iftResidual` consumes (m = nRegL2 H r). Must be CLEAN-THREE [propext, Classical.choice, Quot.sound],
-- no `sorryAx` (the whole D1HChart* ladder is sorry-free + S2-free; reviewer + Codex fidelity-PASS,
-- gate-4 existential-Wᶜ + residual-form non-vacuity confirmed).
#print axioms dln_hchart_residual

-- D1 SECOND-peel `extraCount` chart producer + the assembled L=2 ≥-leg (D1SecondPeelChart/Assembly).
-- Must be CLEAN-THREE [propext, Classical.choice, Quot.sound], no `sorryAx`: `secondPeel_hchart_residual`
-- (the §5 extraCount selected-minor IFT chart on the first residual VECTOR — the minor is Jacobian-rank
-- on `h`, NOT the scalar Hessian, exactly like the first peel) + `deepest_le_of_optimal_secondPeel_discharged`
-- (the L=2 D1 per-point ≥, second peel discharged from data; modulo the 4 named-open hyps first-peel
-- hchart / #44 hDeepest / hInterface [R1 at M'] / hminor₂). NO #120/gauge-slice in the proof terms — the
-- verify-first gate verdict (reviewer + Codex): the second peel is BOUNDED, off the L≥3 wall.
#print axioms secondPeel_hchart_residual
#print axioms deepest_le_of_optimal_secondPeel_discharged

-- R1 interior-det headline at the (2,2,2) node — must be CLEAN-THREE [propext, Classical.choice,
-- Quot.sound], no `sorryAx`: `interiorDet_headline_222` is the FIRST end-to-end faithful-route
-- interior-det Jacobian (|det Dφ| = |u_pRad|^{minAdm−1}·|aRead(pbo u)|²) on a concrete node,
-- UNCONDITIONAL (PivotNotReader via route-D, pRad ∉ readerSet by membership). The (2,2,2)
-- VALIDATION milestone; the ∀M-L2 generalization reuses its pivot-generic lemmas.
#print axioms interiorDet_headline_222

-- R1-LOWER ∀M-L2 interior-det `|det Dφ|` headline (the general-M generalization of the (2,2,2) anchor) —
-- must be CLEAN-THREE [propext, Classical.choice, Quot.sound], no `sorryAx`: `interiorDet_leaf_headline_eihd`
-- (the staircase-conjugated leaf Jacobian, via eIn faithfulness + the eihdc coupling + the 3 fderiv-BparamsLeaf
-- J-blocks J00/J01/J11) + the coupling identity `eihd_hD`. The cov-field input to cover_ge_div / NodeAchieverChart.
#print axioms eihd_hD
#print axioms interiorDet_leaf_headline_eihd

-- Headline — sorryAx expected (5 rungs pending); tracked here so the day it goes clean is visible.
#print axioms aoyagi_learning_coefficient

-- L=2 headline ENDGAME scaffold (genm-l2asm) — the `L = 2` instance of the headline, assembled from
-- the banked L=2 rungs (front-gauge #44 `_L2_front`, the WLOG transport, D1 `deepest_point_reduction`,
-- the PROVEN arithmetic recombination) + exactly TWO named-open leaves. Expected axiom profile:
-- [propext, Classical.choice, Quot.sound, sorryAx] — the `sorryAx` ONLY from the two named leaves
-- (the route-independent R1 resolution interface `hR1_L2` + the D1 ∀-v ≥-leg producer `hD1ge_L2`),
-- and NO `monomial_rlct` (S2 enters only DOWNSTREAM of the R1 leaf, once that sorry is discharged).
-- STEP-0 finding: the dependency graph has TWO open leaves, not one — the D1 ≥-leg is a genuine
-- second obligation beyond R1 (per-v middle-stratum producer), corroborated by Codex xhigh.
#print axioms aoyagi_learning_coefficient_L2
