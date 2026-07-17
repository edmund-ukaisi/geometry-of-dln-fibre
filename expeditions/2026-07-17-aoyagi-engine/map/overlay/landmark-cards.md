# Overlay — landmark cards (cartographer, curated layer)

*Sole writer: cartographer office. Created pass #1 (2026-07-17, cadence-triggered at 63 commits, no
prior pass). One card per carried landmark (8). "True state" is verified against the live Lean tree +
certs, not the log. Paths are repo-relative to the expedition root.*

**Standing context (read once):** the expedition is mid-RESTRUCTURE. Council #2 (journal ticks 23–25)
adopted an EDGE-labelled carrier (fork 7) + the ChartBridge revision + Q5 route (b) (banked
local-homeomorph RLCT transport). The root Lean (`Engine/*.lean`) is still the r2-VALIDATED
NODE-carrier shape; the edge restructure is IN FLIGHT on the architect's branch (task #42
`in_progress`), NOT merged to root. Every landmark card below distinguishes the root state from the
adopted-but-unlanded shape.

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
source (ticks 9, 14). **But the six `needs` nodes are back at `adjudicated`** — the validator's 6 C9
warnings correctly track this: the restructure (council #2) changes their statements, so the adopted
route cannot elaborate against verbatim statements yet. This is honest mid-flight state, not rot.

**Witnesses / whys.** Battery 15 scripts: 13 guards SURVIVE, 2 naked-weight kills FIRE
(`w-naked-weight-111`, `w-naked-weight-4444`) — the zero-slack lesson's anchor. Why a landmark:
founding route; its adoption gate was the first live test of the uplifted harness.

**Pointers.** `threads/00-genesis/architecture-cert.md`; council-1 counsels; the tick-7 journal entry.

---

## 4. `resolution-tree` — the key definition (`drafted`; RESTRUCTURE IN FLIGHT)

**What it is.** The pp.14–22 chart-tree datatype: per-node monomial vector + divisibility chain +
the TYPED divisor-support (sharing) map. Flattening the sharing to per-generator multiplicities is a
TYPE error, not merely a battery failure (fork 3).

**True status — root vs adopted.** ROOT (`Engine/ResolutionTree.lean`) is the NODE carrier:
`StepData` with `case : StepCase` as a field, `support : Fin numGen → Finset (Fin numDiv)`,
`LeafData` with `chartDom : Set (Params M)`; `inductive ResolutionTree | leaf | branch (n) (charts :
List …)`. This is the r2-VALIDATED shape. The ADOPTED shape (council #2, NOT yet in root) is
EDGE-labelled: `Edge {case, localSub/subst : ChartSubst M, child}`, `branch (n) (edges : List (Edge
M))`; `chartDom` REMOVED (downstairs-open defect); leaf `chartMap` = DERIVED path-composite fold;
ChartBridge predicates at leaf level; `StepInvariant` becomes relational (`StepRel` on edges). Node
status was `validated` at r2 then reopened to `drafted` when the restructure landed as the plan —
r2 VALIDATE is marked superseded+incomplete (it missed the univ-atlas vacuity).

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
(`EngineObligations.lean:144`) is a PROVED PROJECTION of `resolutionOf_spec` — the covering CONTENT
lives inside the sorried construction hole `monomialization_terminates`, NOT its own tide (the bundle
collapsed the fan-out). **Caveat (load-bearing):** `ChartsCover` as-stated is a WEAK conjunct — the
univ atlas satisfies it (`g-chartscover-vacuity`, lane 2 exact counterexample); the real geometric
atlas is the construction's + ChartBridge's burden.

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

**True status.** `adjudicated`. A PROVED PROJECTION of the bundle (`EngineObligations.lean:152`). The
arithmetic conjunct is made GENUINE at (2,2,4): `canonicalResolution_224` rides precisely on this
(the four carrier-independent conjuncts, with `Mval((0,0)) = minAdm = 4` by kernel `decide`). The
form-A-vs-slack trap (`g-tightness-formA`: truth scans cannot separate a tight bound from a slack
one) earns the landmark slot — the bridge must be the exact minimisation, not a scan.

**Witnesses / whys.** `g-minadm-groundtruth` (paper worked minAdm values + λ=minAdm/2),
`g-tightness-formA`, `g-def3-broken` (Def 3 as printed forces an empty selection — use the geometric
`½·min_t Mval(t)`). Why a landmark: the seam where the analytic chart read meets the banked QIP
combinatorics.

**Pointers.** `RouteMLayerSplit.lean` (minAdm/minAdmRec), `RouteMSJCorankRec.lean` (QIP family);
`paper-read-cert.md`.

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
