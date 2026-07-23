# Regrounding + Close-Out Plan — 2026-07-23

Controller regrounding after the operator flagged a treadmill/local-min. Built from carto-fresh's
fresh-eyes verdict + my own cross-check + my own reading of the foundation/structures. This is the
plan artifact, not a tick-log. Edit-in-place as the fork resolves.

## 1. Verdict (cross-checked against the kernel + the paper + my own read)

**TREADMILL — confirmed.** Integration-branch census flat (~489→495 over 260 commits, ~15h;
78% journal-only). No MonumentAtlas leaf closed on the trunk in that window. Seat work is banked
OFF the integration branch (CapDescent/SourceClearedResid/LeafCoverTiling/DivBirthReach absent from
trunk); ~30 seat branches; every active seat has a HIGHER census than the trunk (relocates sorries,
doesn't close them). #73 (wire-swaps + aggregator) is BOOKKEEPING, not the keystone — it moves one
opaque sorry (`exists_coreResolution`:311) to ~11 named leaves + pulls in ~16 seat-module sorries.

**Raw census overstates the live frontier ~1.5×.** Of 42 raw sorries: via_engine as-wired = 1;
the monument to fill it = ~11 MonumentAtlas leaves + ~5 Aoyagi wiring (trunk) + ~16 relocated on
seats; **~20 are the literal-name/hbox Skeleton+RouteM route (aoyagi-full's, OFF this objective);
~5 pure fossils** (retired chart Engine). ~25 of 42 are off-this-expedition.

**LOCAL-MIN — suspected at the ENCODING level (not the objective).** The geometric resolution IS
necessary (the monomialisation lives in exceptional coords; the Jacobian enters the RLCT; pure-ideal
cannot dodge the chart CoV). The `Chart`/`Resolution` structs faithfully encode Aoyagi. BUT the
*construction* is a provenance-heavy geometric fold where the paper uses a lighter ideal-identity
argument — see §2.

## 2. The grounded model (the fork, precisely located)

The value/target framework is ALREADY ideal-level and mostly done:
- `Chart` (ProductResolution.lean:62) carries the ideal identity as its exponent-realization
  certificate: `hideal_fwd`/`hideal_bwd` = `⟨(∏C)∘g⟩ = ⟨diag b⟩` on `nbhd` (RegionRepresents, coeffs
  continuous on nbhd), + `hjac` (|det Dg| = monomial·unit, unit nonvanishing on nbhd), + the cover.
- Value engine: `two_mul_rlctAt_eq_divisorMin` (Object B, the CoV summing per-chart monomial
  contributions with Jacobians) ∘ `divisorMin_eq_cCodim` (Object D, **PROVED**). Object B is
  route-independent — it consumes any `Resolution`.
- The Jacobian genuinely enters the RLCT, so NO route bypasses the chart framework via pure
  ideal-invariance. (I briefly overreached on this; corrected.)

Where the heavy machinery lives — the CONSTRUCTION only:
- `exists_atlasRealizesExponents` (MonumentAtlas:1896) builds the atlas from `buildTree` and proves
  each chart's certificate via: **L5** `leaf_stepInv_of_path` (atlas + FoldProduced/FoldRealizes
  provenance + per-chart `PrincipalInv`), fed by **L4** `case1_preserves_stepInv` (THE WALL, corank≥2)
  + **L3** `case2_preserves_stepInv`, all carrying `FoldStepInvAt` (the support/degree-1 invariant).
  **L1** `principalInv_regionRepresents` turns PrincipalInv into the two RegionRepresents.
- ALL the fidelity pain (the ~29 catches, the WALL, the KILL `sourceClearedResid_ignoresEscapedBelow`,
  `couplingClear`, degree-1 exactness, #95 row-phantom, #98 growth arm) is in L3/L4/L5's
  `FoldStepInvAt`, and it descends from encoding each blow-up step as a coordinate SUBSTITUTION
  (`blockBlowupCoordQuot`, divide-by-pivot) that is exact only at degree 1 — so you must track which
  coordinates survive.

**The fork.** Prove the same `hideal_fwd`/`hideal_bwd` (equivalently PrincipalInv) via the paper's
per-step **unimodular Schur-clearing** (worked.tex:443–458): in each blow-up chart a pivot = unit·b
(unit nonvanishing there), left/right-multiply by unimodular Q,P built from unit⁻¹ (⟨QAP⟩=⟨A⟩
exactly), and the cross-term F₃F₂ is a *product of generators* ∈ ⟨F₂,F₃⟩ so it drops (:466). The
exceptional monomials accumulate into diag(b). NO substitution, NO degree-1 tracking.

- SHARED (kept): `buildTree` + FoldProduced/FoldRealizes provenance, L6 chart geometry, L7 cover
  (engine DONE), L8 exponent-ledger, L1, Object B, Object D, the whole `Chart`/`Resolution` framework.
- SWAPPED (retires): L3/L4/L5's `FoldStepInvAt` proof → ideal-identity proof. **The WALL, the KILL,
  #95, #98, couplingClear, degree-1 all retire** if the swap holds.
- Corank≥2 plausibly DISSOLVES: clearing J pivots one at a time, each an identical ideal-preserving
  step; the coupling `diag(b)` accumulates automatically; no special corank≥2 object, no shear-rescue
  (the `2u₀u₂` rescue is a symptom of divide-by-pivot, absent when you Schur-clear instead).

**Foundation gap (the crux of "lighter IN LEAN"):** the unimodular cofactors (unit⁻¹) must be
continuous + nonvanishing on the chart `nbhd` — which is EXACTLY what the framework already requires
(`hunit_ne`, RegionRepresents coeffs continuous on nbhd). So possibly NO new foundation, just a
cleaner proof of the same fields; at most a small reusable "comparable-within-a-chart" lemma.

**Key risk (exact-algebra, for pnp-ideal):** does the Schur-clearing give clean RegionRepresents
(cofactors continuous, unit nonvanishing) on the chart `nbhd` — including at the RLCT-relevant points,
not just the block-elimination basepoint — corank≥2 included, on d=![1,2,1] and a corank-2 case
(e.g. (3,3,4))? If yes → re-architect retires the hard parts. If the unit degenerates on the nbhd →
the support-tracking may be intrinsic and confirm-and-grind is right.

The rejected `SupportedOn` history (MonumentAtlas:1518-1526) does NOT refute this — it refuted
ideal-membership AFTER the substitution, not the paper's matrix-level identity. It sharpens the
suspicion (the substitution encoding is the source of the pain).

## 3. Decision framework (re-architect vs grind) — cross-check elder + pnp-ideal against §2

- **RE-ARCHITECT** if: pnp-ideal confirms clean RegionRepresents via Schur-clearing on d=![1,2,1] +
  corank-2 (cofactors continuous, unit nonvanishing on nbhd), AND elder surfaces no concrete prior
  rejection of the matrix-level route. → The escape from the local min; the WALL/KILL/#95/#98 retire.
- **CONFIRM-AND-GRIND** if: pnp-ideal finds the cofactors degenerate on the nbhd / the ideal identity
  needs support-tracking anyway. → The support-tracking is intrinsic; finish the geometric route.
- **MIDDLE** (lighter but needs a real foundation lemma): weigh the reusable foundation-build vs the
  remaining geometric grind (the WALL + #98 which seat-killfin estimates ≫150 LoC hard/uncertain).

I hold my own model (§2) and judge their reports against it, not as oracles.

## 4. Contingency plan

**Branch A — RE-ARCHITECT (if §3 says so).** A targeted swap, not a rebuild:
1. Foundation (if needed): the "comparable-within-a-chart" / cofactor-regularity lemma. Small,
   reusable, Mathlib-grade. Build first, in Core.
2. The ideal-route L3/L4/L5: per-step unimodular Schur-clearing over `buildTree` producing PrincipalInv
   (or hideal_fwd/hideal_bwd directly). One clean per-step lemma reused for case1/case2/corank≥2.
3. Keep L1/L6/L7/L8/ObjB/ObjD + the atlas/provenance scaffolding. Re-point exists_atlasRealizesExponents.
4. HOLD then RETIRE the geometric fold (CapDescent/SourceClearedResid/the KILL seats, #92/#95/#98) —
   quarantine, don't delete, until the ideal route is green.
5. This is a big LADDER change (not a destination/def-of-done change) → surface to operator as a knowing
   decision with recommendation; proceed-on-silence.

**Branch B — CONFIRM-AND-GRIND (if §3 says so).** Finish the geometric route, census-gated:
1. Close L4 (the WALL) + L3 + #98 growth arm (the genuinely hard pieces) — dedicated, gated on
   census-DROP not commit-count.
2. Then L6/L7 wires (L7 engine done), L8, then #73 (billed as bookkeeping).
3. Same cleaning (§5) + process fixes (§6).

## 5. Cleaning (either branch) — carto-fresh owns; report banked

- Quarantine the ~20 literal-name/hbox Skeleton+RouteM sorries out of the census signal.
  **Operator-gated** (the literal-name Skeleton root is a registered root; removing it from the signal
  touches the definition-of-done question #94 — wait-for-explicit-go).
- Prune/mark the ~5 fossil chart-Engine sorries (retired nodes).
- Triage the ~30 seat branches: which are dead/merged/superseded vs live. Delete the dead.
- Make `scripts/sorries` (or a cone-aware wrapper) report the true LIVE via_engine frontier, so the
  census signal reflects reality.

## 6. Process fixes (stop the treadmill) — binding on the controller

- Gate every seat + every "done" on census-DROP on the integration branch, not commit-count/journal.
- No journal-tick-as-progress; the journal is history, the kernel is truth.
- No new render-seat spawning without a census-drop target; integrate to trunk on a cadence rather
  than accumulating banked off-branch work behind a deferred keystone.
- Stop calling #73 the keystone; the keystone is the L3/L4/L5 content (or its ideal-route replacement).

## 7. Decision points + operator surface

- IN FLIGHT: elder-standing (history/why + ruling) + pnp-ideal (exact-algebra + foundation cost),
  decorrelated, on the §2 fork. I cross-check both against §2, then decide §3.
- SURFACE TO OPERATOR (knowing decision, recommendation, proceed-on-silence): the fork decision
  (re-architect vs grind) once adjudicated — it redirects the whole team.
- WAIT-FOR-EXPLICIT-GO (unchanged): the literal-name-root quarantine (§5, touches def-of-done #94);
  any #73 PR merge; dev→main. The objective (objects A–E, via_engine sorry-free) is UNCHANGED either
  way — the fork is a ladder choice, not a setpoint change.
