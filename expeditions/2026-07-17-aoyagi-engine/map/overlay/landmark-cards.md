# Overlay — landmark cards (cartographer, curated layer)

*Sole writer: cartographer office. Created pass #1 (2026-07-17). REFRESHED pass #2 (2026-07-18): the
restructure LANDED, so cards 3/4 (engine-route, resolution-tree) + the standing-context header were
de-staled, and drifted line-pins in cards 5/6 corrected (the "stale pin costs tides" class). One card
per carried landmark (8). "True state" is verified against the live Lean tree + certs, not the log.
Paths are repo-relative to the expedition root.*

**Standing context (read once) — REFRESHED pass #2 (2026-07-18): the restructure has LANDED.** The
EDGE-labelled carrier (fork 7) is in root and r2-VALIDATED (tick 37); the six obligation predicates
flipped `adjudicated → stated`; `ChartBridge` (the ex-`ChartsCover`) is strengthened + interface-FROZEN
(tick 46/51). The per-leaf read is now the Mathlib AREA FORMULA (fork-8 revision, tick 43) — the
banked local-homeomorph RLCT transport stays BANKED-but-UNUSED on the leaf path (P6 one live spine;
see [[dead-routes]]). Live shape since: the fork-10 full-mechanism reframe + council #3 fork 11 (Path A
the SOLE critical path; R1 lands the faithful full-`T` + `genDivExp` carrier NOW; R6 regular-peel OWED
first-class; "kills the cite for free" STRUCK). **[REFRESH 2026-07-19 tick 265+, cartographer-6: the
"two live engine holes = `monomialization_terminates` + `region_glue`" framing is STALE. Post-assembly
the engine has ONE analytic hole: `chartBridge_buildTree` (`EngineObligations.lean:53`).
`monomialization_terminates` is assembled (`:91`); `region_glue` is a proven composition (`:154`);
`o5_realization` went clean-three (`:72`). See [[wiring-endgame]] pass #5 + [[STATUS]] for the current
hole ladder.]** — see [[banked-families]] for the R1–R6 consumption map.

---

## 1. `mint-repoint` — the destination (root, `stated`)

**What it is.** The unconditional mint: `(⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) =
ENNReal.ofReal (aoyagiLambda H r)` for `B.rank = r`, `1 ≤ L`, `r < H s ∀ s` — no Aoyagi hypothesis,
clean-three. The learning-coefficient headline the whole engine exists to unconditionalise.

**True status.** `stated`, parked "until hbox-root lands (consumer stack proven; wiring only)". The
consumer stack IS proven: `aoyagi_learning_coefficient_gen` (`HeadlineGenAssembly.lean:55`) is
0-sorry / clean-three, conditional SOLELY on `hbox` (reuse-map cert). The `≤`-half is unconditional
upstream. So mint is a pure wiring step once `hbox-root` is discharged.

**Anchor drift (flag).** `claims.yaml` gives `lean: aoyagi_learning_coefficient` with `evidence:
HeadlineGenAssembly.lean`. The bare `aoyagi_learning_coefficient` actually lives at
`Skeleton.lean:1685` (a legacy stub that re-points at mint); the evidence file holds the `_gen`
(hbox-conditional) form. Anchor and evidence file are split across two modules — intended per the
node note ("legacy Skeleton stubs re-point at mint"), but a reader following `lean:` into the evidence
file finds `_gen`, not the bare name.

**Witnesses / whys.** No battery (a wiring claim). Why a landmark: it is the root of the map — the
question's answer.

**Pointers.** `HeadlineGenAssembly.lean`; `threads/00-genesis/reuse-map-cert.md` §one-Prop interface.

---

## 2. `hbox-root` — the one owed Prop (`stated`)

**What it is.** `∀ M, RouteMBoxThresholdFinite M`: for every width vector, `∀ c' < minAdm(M)/2`,
`routeMLayerBoxIntegral M c' 1 < ⊤`. No carried/cited Aoyagi Prop — this is the engine's SOLE
upstream obligation.

**True status.** `stated`. The predicate `RouteMBoxThresholdFinite` is a 0-sorry def at
`Validate/RouteMBoxReduction.lean:165` (confirmed live). Its discharger is
`engine_box_threshold_finite` (`Engine/EngineDriver.lean:44`), whose composition is sorry-free
itself — the sorries are pushed into the two named holes below `engine-route`.

**Witnesses / whys.** Interface confirmed by the reuse audit (exactly one Prop owed, nothing else).
Why a landmark: the single seam between the banked consumer stack and the new engine.

**Pointers.** `RouteMBoxReduction.lean:165`; `reuse-map-cert.md`.

---

## 3. `engine-route` — the founding route (`adopted`)

**What it is.** The transform-only Aoyagi engine: reduce → tree → coverage → thresholds. Driver
`engine_box_threshold_finite` (`EngineDriver.lean:44`); a `@[blueprint]` composition, sorry-free
itself, with a fit `example` (`EngineDriver.lean:59`) plugging its output into
`aoyagi_learning_coefficient_gen`'s `hbox` slot (kernel-checked `engine-route → hbox-root →
mint-repoint`).

**True status.** ADOPTED (tick 7): council 2×ADOPT + skeleton fit-example elaboration + battery
12-green + fork-6 TOMBSTONE (decorated-descent superseded). Gate build controller-verified GREEN from
source (ticks 9, 14). **The six `needs` nodes FLIPPED `adjudicated → stated` at the r2 six-obligation
flip (tick 37)** — the restructure landed and the predicates are correctly stated (validator warnings
15 → 9). `engine_box_threshold_finite` now carries only the two live holes
(`monomialization_terminates`, `region_glue`); its flip to clean-three IS the hbox event the mint
re-point waits on. [REFRESH 2026-07-19, tick 170: STALE after the E assembly —
`monomialization_terminates` is ASSEMBLED (no longer bare) and `region_glue` is a PROVEN
composition through `region_glue_of_chartBridge`; the two live analytic holes are now
`chartBridge_buildTree` (EngineObligations:52) + `o5_realization` (:63); R2 and R3 CONVERGE at
`chartBridge_buildTree`. The hbox event = those two flipping clean-three.]

**Witnesses / whys.** Battery 15 scripts: 13 guards SURVIVE, 2 naked-weight kills FIRE
(`w-naked-weight-111`, `w-naked-weight-4444`) — the zero-slack lesson's anchor. Why a landmark:
founding route; its adoption gate was the first live test of the uplifted harness.

**Pointers.** `threads/00-genesis/architecture-cert.md`; council-1 counsels; the tick-7 journal entry.

---

## 4. `resolution-tree` — the key definition (`validated`; edge carrier LANDED)

**What it is.** The pp.14–22 chart-tree datatype: per-node monomial vector + divisibility chain +
the TYPED divisor-support (sharing) map. Flattening the sharing to per-generator multiplicities is a
TYPE error, not merely a battery failure (fork 3).

**True status — LANDED + r2-VALIDATED (tick 37).** ROOT (`Engine/ResolutionTree.lean`) is now the
EDGE carrier: `Edge {case, subst, child}`, `branch (n) (edges : List (Edge M))`; `StepData` carries
no `case`; `chartDom` REMOVED (downstairs-open defect); leaf `chartMap` = DERIVED path-composite fold;
ChartBridge predicates at leaf level; the faithful `StepRel := rootLedger e.child = stepUpdate n
e.case e.subst` (reads `e.child`; discharge rfl-class, tick 44). The pass-#1 NODE carrier
(`support : Fin numGen → Finset`, `LeafData.chartDom`, unary `StepInvariant`) is SUPERSEDED — GONE
from root. bChain stays a TYPED field (fork 3). **OPEN under council #3 fork 11:** the faithful carrier
lands full-`T` (non-derivable, chooser-required) + the `genDivExp` multiplicity field at R1 — the
current binary `support` is a nonzero-locus approximation ([[banked-families]] R1/R4).

**Witnesses / whys.** `g-coupled-binding-334` (minAdm(3,3,4)=8 reached only on a corank-2 first cut —
the coupled path), `g-delta-flatten` (`lct(δ²(x²+y²))=½` vs `lct(δ₁²x²+δ₂²y²)=1`, identical
multiplicities, different value). Why a landmark: typed sharing fields are the design crux.

**Pointers.** `threads/00-genesis/paper-read-cert.md`; `threads/01-skeleton/necessity-and-encodings.md`
(the council-2 edge-vs-node driver + the mixed-case Case-1 necessity witness).

---

## 5. `coverage-theorem` — THE HARD PART (`adjudicated`)

**What it is.** The tree's chart images cover a box-NEIGHBOURHOOD of the zero locus, and the candidate
divisor set is exhaustive: no untracked exceptional divisor has a ratio below the tracked minimum. A
UNIVERSAL claim — WITHOUT invoking `rlct = c*` (circularity guard). The one genuine new proof.

**True status.** `adjudicated` (cert-d3). The HUNT SURVIVED (tick 12): 5 decorrelated legs (exhaustive
monomial, two independent codim methods, sheared-incidence exact LP over the continuous weight space,
tracked-leaf Newton-LP census, MC guide), 0 undershoots on 7 instances incl. corank-2 (3,3,4). Scope
is cited BY POINTER (`hunt-cert.md §5`), never blanket "established". In Lean, `coverage_theorem`
(`EngineObligations.lean:219`) is a PROVED PROJECTION of `resolutionOf_spec` — the covering CONTENT
lives inside the sorried construction hole `monomialization_terminates` (`:184`), NOT its own tide
(the bundle collapsed the fan-out). **Caveat (load-bearing, RESOLVED-in-shape):** the ex-`ChartsCover`
was a WEAK conjunct the univ atlas satisfied (`g-chartscover-vacuity`); it is now the per-leaf
`ChartBridge` (strengthened MeasurableSet + bounded srcBox, interface-FROZEN + abstract-field-gate
cleared, tick 51). Making the monomial assertions TRUE over the constructed atlas is still R2's
burden — council #3 gate: the ChartBridge PROOF + a DECORRELATED atlas-closure probe (pen-and-paper,
never the builder).

**Residual scope (honest, parked).** angular/non-coordinate centers for instances other than
(2,2,2,2); 3rd+ nested blow-ups for instances other than (2,2,2); the (2,3,2,2)/(4,4,4,4)
minimizing-branch weighted searches; the (4,4,4,4) full exact chart; optional D-module lct check.

**Witnesses / whys.** kill = `g-coverage-sharing-killcond` (mis-tracked sharing invents a spurious
low-ratio divisor). Guards: `g-case2-exponent` (Case-2 divisors CAN bind — keep them in the candidate
set), `g-chart-bridge-pullback`, `g-leaf-chain-separation`. Why a landmark: the named hard part; the
expedition-level kill-condition lives here.

**Pointers.** `threads/02-covdesign/cert-d3-coverage-design.md`; `threads/03-hunt/hunt-cert.md §5`.

---

## 6. `exponent-ledger-bridge` — the analysis↔combinatorics seam (`adjudicated`)

**What it is.** The chart exponents `M_{s,k}` land on the banked minAdm forms:
`½·min{M_{s,k} : t̃=0} = ½·minAdm(M)`, i.e. `minAdm M` is a terminal divisor exponent AND lower-bounds
them all. Consumes `minAdm`/`Mval` verbatim; never re-derives the arithmetic.

**True status.** `adjudicated`. A PROVED PROJECTION of the bundle (`exponent_ledger_bridge`,
`EngineObligations.lean:226`). The arithmetic conjunct is made GENUINE at (2,2,4):
`canonicalResolution224_arithmetic` (the split bank piece; `CanonicalWitness224.lean`) rides precisely
on this (the carrier-independent conjuncts, with `Mval((0,0)) = minAdm = 4` by kernel `decide`). The
form-A-vs-slack trap (`g-tightness-formA`: truth scans cannot separate a tight bound from a slack
one) earns the landmark slot — the bridge must be the exact minimisation, not a scan.

**Witnesses / whys.** `g-minadm-groundtruth` (paper worked minAdm values + λ=minAdm/2),
`g-tightness-formA`, `g-def3-broken` (Def 3 as printed forces an empty selection — use the geometric
`½·min_t Mval(t)`). Why a landmark: the seam where the analytic chart read meets the banked QIP
combinatorics.

**Pointers.** `RouteMLayerSplit.lean` (minAdm/minAdmRec), `RouteMSJCorankRec.lean` (QIP family);
the minAdm-as-minimum property `minAdm_le_Mval_toNat` at `RouteMState.lean:259` (MOVED from
RouteMLayerSplit — pass #1's pin was stale; see [[naming]]); `paper-read-cert.md`.

---

## 7. `theorem4-localization` — the non-deepest EXACT reduction (`adjudicated`)

**What it is.** A non-deepest neighbourhood reduces, by an EXACT RLCT-preserving CoV (NEVER a
reweighted-residual bound), to a strictly-smaller arity-IH instance. Threshold preservation:
`nReg + minAdm(M') ≥ minAdm(M)` via the minAdm-as-minimum property (`inf'_le` / `minAdm_le_Mval`
class) — **NOT `MinAdmMono`** (opposite direction; a name-similarity formaliser trap, caught at
covdesign D2).

**True status.** `adjudicated` DISSOLVE (cert-d2) + SHAPE-CHECK CONFIRMED at (2,2,4) (lane 1, tick
17): pure homogeneity domination via `deepest_le_of_homogeneous_core` (`DeepestMinRlct.lean:157`,
banked hypothesis-free), degree 2L; nothing wanted a chain-IH. **Delta vs calibration.md:** navigator
pass #1 flagged "shape-check has no live owner (architect reaped tick 8)" — that gap is now CLOSED by
lane 1's tick-17 confirmation. OPEN LEG: L≥3 coupled non-origin points discharge via the banked
domination, not a chain-IH. Acyclicity verified (domination calls nothing; CoV strictly drops;
disjoint owners).

**Witnesses / whys.** kill = `g-glue-lossy-vs-exact` ((2,2,2) rank-1 non-deepest: exact CoV rlct=3/2
vs lossy naked-weight rlct=1/2). Why a landmark: promoted at council #1 — owns the seam where the
naked-weight disease re-enters.

**Pointers.** `threads/02-covdesign/cert-d2-theorem4-localization.md`; `DeepestMinRlct.lean:157`.

---

## 8. `rr4-precedent` — the (r,r,4) guard (`adjudicated`)

**What it is.** The (r,r,4) family run end-to-end and banked 0-sorry: the whole engine's OUTER
plumbing (sub → det-Jacobian → gammaAtom → cover → threshold), as a precedent/guard the generic
engine must reproduce.

**True status.** `adjudicated`. OUTER-plumbing precedent ONLY — the inner SchurCore walls at depth ≥ 3
(`RouteMBoxThresholdRR4.lean:12–21`, the "Why only (r,r,4)" scope note; NOTE the compass/map shorthand
"RR4.lean" = `RouteMBoxThresholdRR4.lean`, there is no bare `RR4.lean`). Honest form: the composition
is 0-sorry.

**Declaration names pinned (charter task for this guard node).**
- `routeMBoxThresholdFinite_rr4_of_schurRecStep` (`RouteMBoxThresholdRR4.lean:219`) — the assembly:
  GIVEN the carve `hstep : SchurRecStep 4 …`, delivers `RouteMBoxThresholdFinite` for (r,r,4);
  generalises the anchor `routeMBoxThresholdFinite_M334` to all r.
- `minAdm_rr4_eq` (:88) — `minAdm(r,r,4)/2 = schurLambda r`.
- `routeMLayerBoxIntegral_rr4_eq` (:177) — the box-integral CoV; `frobSq_prod_eq_eParamsRR4` (:157),
  `measurePreserving_eParamsRR4` (:121), `eParamsRR4_preimage_box` (:133) the CoV supports.

**Witnesses / whys.** The composition's 0-sorry status is its own guard. Why a landmark: the outer
precedent + threshold-reachability at (r,r,4); it is NOT an inner precedent (SchurCore/front-peel core
documented non-generalising at depth ≥ 3).

**Pointers.** `RouteMBoxThresholdRR4.lean`; `reuse-map-cert.md` (WORKED PRECEDENT line).
