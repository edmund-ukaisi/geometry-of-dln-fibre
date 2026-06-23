# Consolidation checkpoint — Aoyagi general-M RLCT (2026-06-23)

Controller step-back after the structure sprawled (many parallel worktrees/branches/teammates →
duplicate work + branch divergence + deferred consolidation). This is the single source of truth
for the result-state and the consolidation plan. `VM-ROTATION-RESUME.md` holds the logistics
(worktree recreation + per-teammate briefings); this holds the *state*.

## 1. The result, honestly (Proved / Open)

Target: general-M `aoyagi_learning_coefficient` = RLCT(dlnLoss, deepest) = ½·minAdm M.

**PROVED + independently audited (rv-ga + decorrelated Codex):**
- `MinAdmMono` — hMono (#149): minAdm(schurStateRed M) ≤ minAdm M, + the componentwise general
  theorem + degenChild corollary. Double-audited FAITHFUL. (branch fm3/routem @c8c9d5a)
- `binding_recursion_of_step` (#153): the abstract recursion, conclusion-not-smuggled.
- `binding_rlct_eq_lambdaCore_of_hstep'` (#154, BindingSpine): instantiation; **reduces the
  binding R1 to EXACTLY hstep + hbase** (hMono discharged). (branch fm3/routem-ga @a94fcd8)
- `hbase` = #70 Morse base — proved (needs wiring only).
- Core measure brick: nonzero MvPolynomial zero-set is Lebesgue-null (orphan @
  backup branch worktree-agent-a990da42…; HARVEST into Core).

So: **the binding R1 = ½·minAdm is PROVED conditional on (hstep + hbase); hbase is proved.**
The whole non-geometric spine (arithmetic + recursion + instantiation) is verified bedrock.

**OPEN — the genuine remaining math (this is the honest gap):**
| # | what | owner | status |
|---|---|---|---|
| #104 | **hstep** — the per-node geometric squeeze (general blow-up cert: dlnLoss in Schur form, the y₀^? *exceptional-divisor* Jacobian — the SOUND weighted-cover, not the vacuous #148 MP-chart) | fm3 | deriving (paper/sympy → transcribe). **THE long pole + the gate to "complete".** |
| #80 | L2 PIN2 — chain around the `framedParams_split_eq_frame_raw` frame-bridge cert | cobuild | leaf cores banked; 1 cert sorry |
| #82 | L2 PIN1 — the regSlice fderiv sandwich (#156/#157) | deriv-fm | skeleton done; analytic fill |
| #158/#159 | frame-bridge boundary frames + 2 Core rank-normal-form proofs | crux2 + formaliser | wrappers green; 2 sorries |
| #151 | cross-branch wiring: merge routem+routem-ga, supply hMono → binding R1 headline | controller | gated on hstep+hbase |
| #42/#105 | D1 top assembly (≥-leg + L2-at-v) | — | waiting on R1/L2 |
| #146 | geometric-codim bridge Mval=codimForm (ENRICHMENT, not on critical path) | rs-grind | foundation green; collapse |

**Naming honesty:** the RLCT comes from a two-sided squeeze (c₁ < c₂); the value ½·minAdm is
exact, the loss↔Φ relation is a comparability (g156 leakage), correctly named. S2
(monomial_rlct) is the ONLY citable axiom; everything else must be proved.

## 2. The structure, honestly (the sprawl)

~28 worktrees, ~30+ branches, 159 tasks. The result-bearing work lives on **5 branches**:
- `fm3/routem` — arithmetic spine (hMono, recursion arithmetic, #146).
- `fm3/routem-ga` — recursion + BindingSpine + (2,2,2) anchor.
- `fm2/deepest-gauge-chart-sub34` — L2: #120 consolidated + FOLD3 + #80 leaf cores.
- `fm/deriv-spec` — #82 #120 def-change + regSlice skeleton.
- `fm2/split-reindex` — #158 frame-lane.
Everything else is stale/duplicate/scratch (agent-* worktrees, superseded feature branches,
backup branches). Duplicate work happened: #120 (cobuild+deriv-fm), FOLD3 (cobuild+crux2).

## 3. Consolidation plan (= #28, elevated to NEXT priority post-rotation)

1. **One integration branch** off `dev` (e.g. `aoyagi/integration`). Merge the spine: pull
   fm3/routem (MinAdmMono) + fm3/routem-ga (recursion+BindingSpine) → do the #151 wiring there.
   Then add the L2 branches as their pieces land.
2. **Harvest orphans**: MvPolynomial-zero-set-null → DLNFibre.Core; review the backup branches
   (backup/fm2-d1-deepest-min-crux2-59, backup/stash0, backup/stash1) — cherry-pick or discard.
3. **Prune**: the agent-* worktrees + branches, the superseded feature branches (atlas-value,
   l2-product, rm-atlas, fold3-close dup, etc.), the duplicate-#120 leftovers.
4. **Reconcile the task board**: close the stale in_progress (#27/#39/#85/#86/#99/#117 — the
   atlas/routeStep route was SUPERSEDED by the recursion route; #44/#135 largely subsumed).
   Keep the genuine-open set: #104, #80, #82(#156/#157), #158/#159, #150, #151, #42/#105, #146.
5. **Synthesis flush**: update the expedition synthesis.md with this true state.

## 4. Leaner go-forward (the lesson)

The sprawl came from over-parallelization without periodic consolidation. Post-rotation: run
**fewer concurrent lanes**, **consolidate to the integration branch as pieces land** (don't let
branches diverge), and **don't defer #28** — fold completed work back continuously. The critical
path is narrow now: it's **#104 (fm3)**, then the L2 finish + #151 wiring + D1. Drive that line,
not breadth.
