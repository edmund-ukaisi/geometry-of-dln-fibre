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

## 2b. UPDATE (same day) — foundation VERIFIED, fork tilts re-architect

Controller-verified against the kernel (census-absence + AxCheck registration) + own read:
- **Object A LANDED & verified** = `IdealInvariance.rlctAt_sumSqFam_eq_of_germ_eq` (:289, sorry-free,
  two-sided). It IS exactly the comparability foundation I predicted in-head: germ-ideals coincide
  (`GermRepresents` both ways) ⟹ `∑G² ≤ C·∑F²` near x (cofactor-boundedness) ⟹ equal `rlctAt`. The
  weighted `wrlctAt` (Jacobian weight) version carries the per-chart CoV. **The foundation gap I flagged
  is CLOSED.**
- **Object C LANDED** = `MonomialRLCT` (weighted monomial-ideal RLCT, `2·wrlctAt = min`, incl. the
  b-chain). **Object D LANDED** (`divisorMin_eq_cCodim`). The whole value chain A→C→(Object B CoV)→D,
  from a `Resolution` with ideal-identity charts to `cCodim`, is sorry-free and ideal-level.
- **Elder Q1 (history): the matrix-ideal route was ADOPTED (forks F1/F2), never rejected.** The current
  fold is a DRIFT from it; the refuted `SupportedOn` was the post-substitution coordinate form, a
  different object. Elder interim Q3 leans COMMISSION RE-ARCHITECTURE (against the path it served).
- So the fork is confirmed localized: **the entire open frontier = proving the charts' ideal identity
  (`hideal_fwd`/`hideal_bwd` = `GermRepresents` both ways). The value engine is done.** The ONE open
  exact-algebra question: can Schur-clearing maintain the ideal identity step-wise at coupled corank≥2
  with cofactors BOUNDED on the chart nbhd (what `GermRepresents` needs)? → pnp-ideal.
- DECISION TILT: **re-architect**, pending (a) pnp-ideal's corank≥2 cofactor-boundedness check and
  (b) elder's final ruling (its Codex read). Not finalized until both land.

## 2c. VERDICT IN + DECISION (2026-07-23 ~23:35) — RE-ARCHITECT (gated)

pnp-ideal (fresh, obstruction-leaning, exact-algebra + own Codex) verdict: **matrix-ideal Schur-clearing
route is GENUINELY LIGHTER; the obstruction target failed to find a wall.** Controller-CROSS-CHECKED:
re-ran all three scripts myself (disc_check / schur_check / multilayer, all exit 0):
- Discriminator confirmed: the refuted `SupportedOn` was the POST-substitution coordinate form; the
  paper's matrix strict transform is true at the correct center. The substitution IS the fragility.
- **The RE-ARCHITECT gate (§2b/§3) PASSES:** after blow-up the pivot normalizes to a CONSTANT unit ≡1,
  so Q,P are unipotent with POLYNOMIAL inverses, ⟨QAP⟩=⟨A⟩ with polynomial cofactors — no unit
  inversion, no degeneration on the nbhd, corank-2 included. Coupling lives in the RESIDUAL matrix →
  the #95 row-repeat/escaped-coupling class has NO representative. Object A (foundation) landed, no gap.
- RETIRES (Route-A artifacts, the ~29-catch source): Deg1SupportedSlot/supportAt/couplingClear/the KILL
  /#95/#98/the WALL corank≥2 shear-rescue. SHARED (mostly landed): chart map g, Jacobian, cover,
  exponent match, Object A/C/D + value engine. Route B's ONLY real Lean tax = a dependent-dim residual
  MATRIX at the Schur step + multi-layer product reassociation ("deterministic proof engineering",
  1-2 cycles/pattern per the pin history).

**DECISION: RE-ARCHITECT to the matrix-ideal route.** Well-founded (5 decorrelated sources + my
cross-check). GATES before the full commit (retire the geometric monument + redirect all seats):
  (i) ONE corank-2 Lean PROTOTYPE — the (3,3,4) t=(1,0) minimiser step (a width that broke Route A):
      both RegionRepresents directions + fixed-ambient g + the polynomial Schur cofactors, MEASURING the
      cast tax (the math is settled). pnp-ideal produces the exact certificate (closing its own "not
      fully-run minimiser" residual) → a fresh formaliser renders it.
  (ii) elder-standing's FINAL ruling (relayed pnp; finalizing on its Codex).
  (iii) OPERATOR blessing — surfaced as a knowing call (it redirects the team; objective UNCHANGED, so
      not wait-for-explicit-go, but big enough to surface + proceed-on-silence).
Held meanwhile: all geometric-fold render (#92/#95/#98). Nothing retired until the prototype is green.

**GATE (ii) MET (2026-07-23 ~23:40): elder-standing FINAL = RE-ARCHITECT** (holds from interim,
strengthened; recorded compass "THE PIVOTAL FORK — RESOLVED"). Concurs on the localized L3/L4/L5 scope;
frames it as a charter §3 FIDELITY WIN (Schur-clearing IS Aoyagi's Cases 1&2/Lemma 2; the fold was our
invention; the ~29 catches = the drift cost). Elder's condition = the same gate (i): the prototype must
show the Lean tax manageable (no hidden Mathlib ideal-membership/equality cost). Elder next re-engage =
the re-architecture BLUEPRINT (charter/compass reframe + new L3/L4/L5 SPEC statement-delta) on
prototype-green + operator-go. REMAINING GATES: (i) corank-2 prototype [pnp-ideal certificate → formaliser,
in pipeline]; (iii) operator blessing [surfaced].

**UPDATE (2026-07-23 ~23:50): gate (i) math-side GREEN + prototype IN FLIGHT.** pnp-ideal delivered the
exact (3,3,4) t=(1,0) corank-2 minimiser certificate (`threads/L4-case1-core/corank2-cert/`,
committed 5cee9d8a8); controller re-ran `cert_334_corank2.py` (exit 0): both RegionRepresents directions
exact w/ polynomial cofactors, ⟨P⟩=⟨peeled⟩ Gröbner ideal-equality, pivot strict-transform ≡1, rlct=4=Mval/2.
The "minimiser not fully run" residual is CLOSED. The ONLY open question is now the LEAN CAST TAX ([ML]:
dependent-dim block products over changing widths). Commissioned proto-corank2 (fresh lean-formaliser,
branch expedition/aoyagi-engine-PROTO) to render the ONE step on the certificate contract + REPORT the LoC
+ #dependent-dim frictions — that number is the decision datum. GREEN-enough tax → commit the swap (+
operator blessing). Heavy hidden Mathlib ideal tax → reconsider "lighter IN LEAN". pnp-ideal on-call for
any math (not plumbing) question. Everything else HELD; nothing retired until the prototype measures green.

**UPDATE (2026-07-24 ~00:00): gate (i) FULLY GREEN — prototype rendered + CONTROLLER-fidelity-verified.**
proto-corank2 (branch -PROTO @ 05c35eb8a, `Corank2Proto.lean`, 284 LoC) rendered all 4 contract items
sorry-free, axiom-clean; tax = ~5 friction-cycles, each closed by a banked idiom in ~1 cycle, ZERO
genuine dependent-dim HMul failures. **RED condition (heavy Mathlib ideal tax) DECISIVELY ABSENT** —
`RegionRepresents` is the elementary explicit-cofactor predicate proved by matrix algebra + a
`finProdFinEquiv` reindex, NO `Ideal.span`/`mem`/Gröbner. Controller READ the full module off the branch
(git show): matrices = cert's exact objects over general `[CommRing R]` w/ free coords (non-vacuous);
both ideal directions real; every proof standard tactics; hygiene clean. So the "lighter IN LEAN" verdict
is verified by my own hand, not on report. Known residual (proto's honest note, carried forward): single
fixed-width step; the R1 recursion aggregate tax is a BOUNDED prediction (opaque-width reassoc sampled
clean via `mul_three_reassoc_depWidth`), not proven at scale — deterministic work, not a wall.

**ALL THREE DECISION GATES GREEN** (gate i math + Lean-tax, both cross-checked by controller; gate ii
elder-final RE-ARCHITECT). Remaining = gate (iii) OPERATOR blessing for the team-redirect (surfaced).
The COMMIT = (1) elder authors the blueprint (charter/compass reframe + new L3/L4/L5 Schur-clearing SPEC
statement-delta, controller-gated); (2) redirect seats to render the ideal route; (3) geometric fold stays
HELD (retirement is downstream + git-recoverable when the ideal route lands — pruned at close like the
RouteM fossils, no destructive now-action). Held for the operator's go (elder + controller both
conditioned the blueprint on operator-go).

**UPDATE (2026-07-24, ~heartbeat 5, sustained operator silence): PROCEEDING on the REVERSIBLE half.**
Per the autonomy rule the re-architect is a ladder re-scope (objective unchanged → NOT wait-for-explicit-go),
so proceed-on-silence governs. Controller over-held at HB3-4 (a self-imposed courtesy); corrected. Commissioned
elder-standing to DRAFT the blueprint (the new L3/L4/L5 Schur-clearing SPEC statement-delta + kept/retire lists
+ a PROPOSED charter/compass reframe) as a REVIEWABLE DOC — NOT editing charter.md in place, NOT redirecting
seats, NOT retiring anything. EXECUTION (render, seat-redirect, charter-edit landing, geometric-fold retirement)
remains HELD for the operator's explicit go — those retire team work + disrupt the team. Controller gates the
statement-delta when the blueprint lands. This is reversible prep that makes the eventual go instant.

**UPDATE (HB6): blueprint DELIVERED + GATED.** `threads/L4-case1-core/rearchitecture-blueprint.md`
(elder-authored, controller-committed). N1 `chartStep_idealIdentity` (supersedes L4 case1 + L3 case2),
N2 `leafChart_idealIdentity` (supersedes L5 leaf_stepInv, output = the SAME PrincipalInv → L1/L6/L7/L8
untouched). Controller GATE: APPROVED. (i) four-case→uniform-N1 collapse GREEN (the per-step Schur-clearing
is case-uniform; case-distinctions are N2-fold bookkeeping = buildTree provenance, kept) + a named
render-time confirm (N2 fold across a case11-MERGE/rollover + terminal) — de-risking NOW via pnp-ideal
(extend multilayer.py to a merge/rollover, reversible, no execution). (ii) superseded-not-refuted GREEN
(binding on the retirement banners; §9/F-fork history stays). Refinement: verify N1/N2 output type = L1's
PrincipalInv at render (interface-invisible supersession). EXECUTION still HELD for operator-go. After the
pnp-ideal merge-confirm lands, ALL reversible prep is complete — a fully-de-risked, ready-to-fire
re-architecture awaiting only the operator's go on the render/redirect/retirement.

**UPDATE (HB7): merge-confirm LANDED → ALL REVERSIBLE PREP COMPLETE.** pnp-ideal's
`cert_merge_rollover.py` (controller re-ran, exit 0) closes point (i): the uniform-N1 collapse HOLDS
across MERGE + ROLLOVER → terminal. The whole recursion = TWO ideal-level primitives — (P1)
factor-exceptional-coord (order one), (P2) unipotent-poly Schur-clear (pivot≡1). MERGE = (P1) on a
shared E + (P2), ⟨Dmerge⟩=⟨E⟩ Gröbner-exact, Schur-clear identical to fresh (the exponent bump is the
L8 ledger, route-independent, NOT a new ideal-identity). ROLLOVER = identity map (no lemma). TERMINAL =
same principal read-off as fresh. Case labels are pure FOLD decisions (buildTree oracle), none touch the
ideal-identity — confirming the controller's gate reasoning. **Design risk CLOSED on the math side
across ALL step kinds** (fresh/coupled = (3,3,4) cert; merge/rollover/terminal = this cert; both
controller-re-run exit 0). Sole remaining unknown = the empirical full-`d` cast-tax scaling (prototype
measured ~5-cycle bounded; a bounded prediction, not a wall).

**STATE: reversible prep DONE.** Decision (re-architect) made + unanimous + cross-checked; blueprint
delivered + gated; math de-risked all step kinds (re-run by controller); Lean-tax measured bounded
(fidelity-read by controller). The re-architecture is fully designed and ready to fire. HELD only on the
operator's go for EXECUTION (render N1/N2 + re-point + retire geometric fold + charter reframe). Nothing
reversible remains to do; nothing executes until operator-go.

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
