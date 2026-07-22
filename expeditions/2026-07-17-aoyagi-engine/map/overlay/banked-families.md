# Overlay — banked-family cards (cartographer, curated layer) — the A–E frame

*RE-ROOTED 2026-07-21 (cartographer re-root #1, tip 70a8ec6cf). The chart-Engine-era cards
(R1–R6 consumption maps, D-arc/carrier/endgame/final-arc indexes) are ARCHIVED VERBATIM at
[[archive/banked-families-chart-era]] — still the reference for any SALVAGE re-import out of the
retired `Engine/` parts-bin (RETIRED.md governs). This file cards what the A–E frame consumes.
Every pin grep-verified against the live tree at 70a8ec6cf. Paths `lean/DLNFibre/…`.*

**Standing posture (carried over from the operator fidelity-steer):** the PAPER's structure
outranks the module DAG's convenience; an unanchorable banked family is a stray to flag, not
launder. The live paper-fidelity ledger is now **compass.md § Paper-fidelity ledger** (elder-owned;
incl. the two NEW thread-31 defects). The chart-era anchor table is [[archive/paper-anchors-chart-era]].

---

## OBJECT A — ideal-RLCT invariance (`Core/Aoyagi/IdealInvariance.lean` + `Waypoint.lean`; 0-sorry)

*The category-NEW workhorse (Mathlib-absent). Landed seat-A, wave 1. All batch-gated clean-three.*

- Headlines: `rlctAt_sumSqFam_eq_of_germ_eq` (`IdealInvariance.lean:289`), weighted twin
  `wrlctAt_sumSqFam_eq_of_germ_eq` (`:449`).
- Leaves: `eventually_sumSqFam_le_of_germRepresents` (`:174`, Cauchy–Schwarz domination),
  `rlctAt_mono_of_eventually_le` (`:213`, junk-guarded germ-monotonicity — **renamed from
  `rlctAt_mono_of_ae_le`**, see [[naming]]), `rlctAt_const_mul` (`:250`),
  `rlctAt_sumSqFam_le_of_germRepresents` (`:262`); weighted: `wrlctAt_one` (`:315`),
  `wrlctAt_const_mul` (`:348`), `wLocalAdmissibleExponents_subset_of_eventually_le` (`:358`),
  `wrlctAt_mono_of_eventually_le` (`:401`), `wrlctAt_sumSqFam_le_of_germRepresents` (`:422`).
- Carriers: `GermRepresents` (`:72`), `RegionRepresents` (`:84` — the record's ideal-identity
  clause consumes this), `LocallyNullZeros` (`:97`, the junk-0 guard), `wLocalAdmissibleExponents`
  (`:305`).
- Waypoint helper: `locallyNullZeros_sumSqFam_of_polynomial` (`Waypoint.lean:68`) — WRAPS the
  existing `MvPolynomial.volume_zeroSet_eq_zero` (survey-first held).
- **Trap (D3/C-delta class):** admissibility needs MEASURABILITY hypotheses (`hWmeas`,
  `Measurable unit`) — ContinuousAt-only admits junk-0 collapse. Twice caught at statement-lock.

## OBJECT C — monomial-ideal RLCT (`Core/Aoyagi/MonomialRLCT.lean`; 0-sorry)

*The guarded S2 boxed rule. Landed seat-C. Batch-gated clean-three, S2-FREE (no `monomial_rlct`).*

- `exists_unit_sumSqFam_monomial` — chain collapse `∑bₖ² = b_{k₀}²·U` under `DivChain` (`:54`).
- `monomialSumSq_wrlctAt_eq` — THE S2 BOXED RULE: `wrlctAt = min_d (h_d+1)/(2k_d)`.
- `monomialSumSq_two_mul_wrlctAt_eq_min` — DLN unit-multiplicity form `2·wrlctAt = min (h_d+1)`.
- Honest boundary: `not_divChain_coupled_example` (`:77`) — the coupled counterexample the guard
  excludes. `Measurable unit` on leaves 2/3 is the controller-BLESSED delta.
- Carriers consumed everywhere in B: `monomialFam` (`:43`), `jacWeight` (`:48`), `bindingAxes`
  (`:60`), `monomialThreshold` (`:66`).
- Wave-2 hygiene owed: MonomialBox Core-lift + DLN dedup (`RouteMSJMonomialLower`/`Case222Cover`
  duplication, forced by Core↛DLN today).

## OBJECT B record + value (`Core/Aoyagi/ProductResolution.lean` + `Engine.lean` + `AreaFormula.lean`)

*The v4.2 record (verified to equilibrium: v3 structural kills → v4 hypothesis kills → v4.1 one
quantifier → v4.2 clean; 093475db3) + monument 1. Value chain batch-gated clean-three.*

- Record: `Chart` (`ProductResolution.lean:62`), `Resolution` (`:126`), `jacDet` (`:55`),
  `Chart.jacWeightFn` (`:142`), `Chart.chartMin` (`:148`), `Resolution.divisorMin` (`:154`).
  FROZEN; the shear pin (thread 33) confirmed NO field change needed (unit/hjac already right).
- Per-chart value: `Chart.two_mul_wrlctAt_eq_chartMin` (`:219`) — A∘C, the wiring the blueprint
  was built for. Negative guard: `no_unit_forces_axis_jac_coupled` (`:621`).
- **Monument 1 (atlas CoV):** `rlctAt_sumSqFam_eq_iInf_charts` (`:540`) — ≤ via the NEW
  InjOn-off-null area formula; ≥ via off-origin C + compact subcover + a.e.-cover subadditivity.
  Fidelity strength (rev-cov-fidelity): the weight is the ACTUAL `|det Dg|` (`jacWeightFn`) — a
  false `jac` declaration cannot game the value.
- Value chain: `Resolution.two_mul_rlctAt_eq_divisorMin` (`:590`) → `Resolution.divisorMin_eq_cCodim`
  (`Engine.lean:45`) → `Resolution.two_mul_rlctAt_eq_cCodim` (`Engine.lean:84`) — `res` + QIP
  min-attainment are HYPOTHESES; the chain never touches `exists_coreResolution`.
- Reusable infra: `lintegral_image_eq_lintegral_abs_det_fderiv_mul_of_injOn_off_null`
  (`AreaFormula.lean:39`) — the Waypoint-owed general InjOn-off-null lintegral CoV.
- Inhabitation (record-shape tests, kernel-checked): `idResolution`/`allOnesResolution`
  (`ResolutionInhabited.lean:92,138+`) rank-1; `blowupResolution2` (`BlowupResolution.lean:237`) D=2.

## LEAF-2 — the universal origin blow-up (`Core/Aoyagi/OriginBlowup.lean`; 0-sorry)

*The shared atom for rung (B) AND the monument's per-step blow-up geometry. Universal-in-D ⟹
instantiates at `flatDim d` with NO cast transport (the opaque-width wall dissolved BY DESIGN).*

- `blowupResolution (hD : 2 ≤ D) : Resolution (coordFam D) 0` (`:290`) — max-pivot atlas, every
  Chart field discharged.
- `jacDet_blowupMap` (`:55`) — the universal Jacobian det `(w i)^(D−1)` via `BlockTriangular.det`.
- `ball_subset_iUnion_blowup_image` (`:259`) — the EXACT argmax sector cover (residual-(I) content
  for the pure origin case, spectator-free).
- D=2 cousins live under `…2` names in `BlowupResolution.lean` (4 renamed at integration — [[naming]]).

## CORE LEAVES — L1 + terminal_bezout (`Core/Aoyagi/PrincipalInv.lean`; 0-sorry, REVIEWED)

*The monument's leaves 1–2, PROVEN + rev-core SURVIVED (2026-07-21). Nodes `b-leaf1-regionrepresents`
+ `b-principalinv`. With these down, 2 of the monument's 8 leaves are closed (cone 8→6). Cards:
[../../threads/42-core-leaves/statement-cards.md]; reviewer artifacts `threads/40-rev-core/codex/`.*

- `terminal_bezout : TerminalBezout` (`PrincipalInv.lean:318`) — principality is BORN terminally: a
  cleared pivot `(F i₀∘g)=b·unit`, `unit 0 ≠ 0`, inverts on the shrunk open `V' = V ∩ {unit≠0}` to
  upgrade `StepInv` (divisibility) to terminal `PrincipalInv` (divisibility + Bézout). Unconditional;
  `unit⁻¹`-continuity via `ContinuousOn.inv₀` (named, NOT assumed). Kill `km_terminal_bezout`: the
  genuinely-vanishing `b=u₀` + proper shrink dropping `u₀=−1`.
- `principalInv_regionRepresents` (L1, `PrincipalInv.lean:123`) — a terminal `PrincipalInv` yields BOTH
  `RegionRepresents` inclusions the Object-B charts need (`⟨F∘g⟩=⟨b⟩` on the region, the `M'=1`
  compression), region-quantified — no germ. Genuine interface conversion (not an rfl-alias). Consumer
  wiring elaborates at the driver `exists_atlasRealizesExponents` :809–813 (hfwd/hbwd).
- **Trap (consumer, recorded at review):** the leaf residual must be LITERALLY `Fin 1` with value `≡1`
  (defeq-only blocks the wiring); the cleared pivot must be a SINGLE generator (not a germ/combination)
  — supplying `i₀`/`unit` is L5's "born terminally" obligation via `terminal_edge_stepInv`.
- Carrier: `b-principalinv` also homes the M17 predicates `IgnoresCoords`/`Deg1SupportedOn` (the
  size-axis guard — see [[severance-witnesses]]).

## SALVAGE ADAPTER — the monument's combinatorial half (`DLN/Aoyagi/RecursionAdapter.lean`; 0-sorry)

*mon-rec; elder-ratified salvage (C1/C2/C3); rev-monument-adapter SURVIVED (seam weakened to
only-the-minimizer; `AtlasRealizesExponents` rename). Batch-gated: `hlb_hattain_of_atlasRealizesExponents`.*

- `AtlasRealizesExponents` (`:55`) — the seam predicate (charts realize the salvaged tree's
  terminal exponents; STRICTLY weaker post-escalation).
- `qipMin_eq_minAdm` (`:69`) — the D bridge; `hlb_hattain_of_atlasRealizesExponents` (`:78`);
  `exists_hlb_hattain_of_exists_atlasRealizesExponents` (`:109`) — the leaf-shaped reduction
  `exists_coreResolution ⟸ ∃ res, AtlasRealizesExponents d res`.
- Salvage roots (retired-`Engine` combinatorics, C1 import boundary re-audited clean at merge):
  `minAdm_le_terminalExponents`, `o5_core_realized`, `isFullMonomialization_buildTree_conRoot`,
  `minAdm_eq_cCodim` bridge. Import ONLY the audited-green closure — never ChartBridge*/Geo*/
  CanonicalResolution ([[dead-routes]] § retired chart-Engine).
- C2 anchors (decide-checks vs the decorrelated battery): (2,2,3,2)→3 running-min, (2,2,1,1)→1,
  (3,3,4)→8, (4,4,4)→12 (`theory/aoyagi-2023-reproduction/g-monument-mval-instances.py`).
- ⚠ drift flag (owner): docstring `:77` still says `AtlasRealizes` (pre-rename).

## COROLLARY REDUCTION (`DLN/Aoyagi/LearningCoefficient.lean` + `Foundations/GlobalHomog.lean`; summit file)

*Seat-bridge, wave 1. Batch-gated: `exists_flatten`, `lossDLN_zero_eq_coreLoss`, `coreReduction`.*

- `exists_flatten` — the LINEAR m.p. origin-fixing homeomorphic flatten (built directly for
  `Tuple` via piCurry reindex); `lossDLN_zero_eq_coreLoss` — the Frobenius identity;
  `coreReduction` — `rlctGlobal (lossDLN d 0) = rlctAt (∑coreGenᵢ²) 0` (deepest-point ∘ flatten
  ∘ m.p.-homeo transport; no `he_lin` needed internally).
- NEW REUSABLE, network-generic: `GlobalHomog.lean` — `rlctGlobal_comp_homeomorph` +
  `rlctGlobal_eq_rlctAt_zero_of_homogeneous` (rides banked `deepest_le_of_homogeneous_core`).
- The summit `aoyagi_learning_coefficient_via_engine` (`LearningCoefficient.lean:299`) and the
  frontier `exists_coreResolution` (`:268`, sorry `:287`) live here.

## OBJECT D / E slices

- D: `Resolution.divisorMin_eq_cCodim` + the banked `minAdm = cCodim` chain (pre-phase Core +
  dev's cite-free determinantal geometry) + `qipMin_eq_minAdm` (adapter). Guards:
  `battery/g-minadm-groundtruth.py`, `battery/g-def3-broken.py`.
- E (charter §1-E **OPENED-SCOPED**, operator 2026-07-21 — no longer DEFERRED): interface
  `one_le_boxedOrder` (`Core/Aoyagi/Order.lean:62`) + the θ≠ρ distinction
  `numTop_d22222_ne_aoyagiPoleOrder` (`DLN/Aoyagi/ThetaOrderDistinction.lean:195`; `aoyagiPoleOrder`
  def `:53`). **P6.1 LANDED** (`Core/Aoyagi/OrderCount.lean`, sorry-free: `bandCount_eq`,
  `perJCard_eq_paper`, `envHi_sub_envLo`, `bandWidth_sum` — band arithmetic `a(ℓ−a)+1`; node
  `e-p61-band-arithmetic`, card [../../threads/41-order-count/statement-card-tier1.md]). **P6.2
  ADJUDICATED** (pnp, node `e-p62-count-identification`): ρ = deepest-stratum MAX-CROSSING of terminal
  (t̃=0) global-minAdm divisors = **max CHAIN of binding minimisers under componentwise ≤** (chainHeight)
  = `a(ℓ−a)+1` — NOT the naive minimiser count ([2,2,2,2,2]: six tight minimisers, ρ=5). ⚠ the
  certificate's *antichain* speculation was CORRECTED to a max-CHAIN (elder register `ab106f1a4`; seat-E
  battery 1018 cores) — read the card [../../threads/41-rho-count-object/certificate.md] through that
  correction. Guard:
  `battery/rho_battery.py` (guards BOTH E nodes; `_edgespec_traversal_334.py` is its runner-skipped
  helper). The analytic zeta-pole seam stays the named monument-class deferral.

## In-flight (NOT banked — do not consume as substrate)

- `DLN/Aoyagi/GeometricAtlasD12.lean` (rung B, node `b-rung-d12`): **now LANDED** — gate-orphan
  RESOLVED, wired + batch-banked (341); `exists_atlasRealizesExponents_d12` + `two_mul_rlctAt_coreGen_d12`
  (the first cite-free LC instance) both clean-three. No longer an in-flight caveat.
- `DLN/Aoyagi/MonumentAtlas.lean` (rung C, nodes `b-leaf34..b-leaf8` + `b-terminal-edge-stepinv`): the
  monument skeleton — TYPED, wired, SORRIED (gate = elaboration + battery, NOT sorry-free). Leaf set now
  **9** (8-leaf skeleton + the NEW `terminal_edge_stepInv`, `:736`). Proven: L1 + `terminal_bezout`.
  Open PROOF QUEUE: `terminal_edge_stepInv` (`b-terminal-edge-stepinv`, elder rider — expected easy,
  unit-residual strictly weaker) + L3 + **L4 = THE WALL** (`case1_preserves_stepInv`, `b-leaf34`,
  seat-L4, wall assembly in flight, rebase signal fired) + L5 fold hinge + L6/L8 + L7 tail. Leaves
  re-stated per [[severance-witnesses]]. Do NOT read a sorried leaf as banked.
- **canonCenter round — LANDED** (integrated `605497e2a`, no longer uncommitted). What it bought: L7
  (`leafPath_compactCover`, `b-leaf7`) is now **BRIDGE-FREE** — the coordinate story is canonCenter's
  own slot bookkeeping `(S,J,mergeIdx,d)` decoded through `tupIdxEquiv` (`LearningCoefficient.lean:138`)
  / the engine's `divBirthCoord` (`EngineConstruction.lean:62`), NOT the retired card↔sum bridge; the
  coordinate-axis severance witness dies ([[severance-witnesses]], `d174f1f41`).
- **leafOf coupling — PENDING-ADJUDICATION** (navigator: dead-scope OR owed; NOT assumed either way):
  L5's `FoldRealizes` carries its own `leafOf`, distinct from `FoldProduced`'s; whether the two must be
  coupled (or the gap is dead-scope) is the nav call. Do not consume the coupling as resolved.
