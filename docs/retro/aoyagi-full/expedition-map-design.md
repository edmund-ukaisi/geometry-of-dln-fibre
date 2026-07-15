# The expedition-map — design note (harness proposal, 2026-07-14)

**The map is not the territory.** The kernel is the territory; the expedition-map is the top-down
record of claimed land and charted routes, and every contract below exists to keep the map honest
against the territory. Write this slogan wherever the map is taught; it is the design discipline
in one line.

**What the map is for: gestalt, not citation.** The map's value is the *gestalt* — the perceived
shape of the whole (what exists, what is dead, what is owned, what sits next to what, where the
frontier bulges) — which is exactly what the territory cannot give you: the kernel returns
point-truths, one expensive query at a time, and no amount of grepping composes them into a
situation. Use the map to decide **what matters**; use the territory to decide **what is true**.
Concretely, the controller's usage discipline:
- Read the map freely for orientation, prioritisation, delegation — the gestalt layer needs no
  verification, because being approximately-and-holistically right is its whole job.
- The moment a *specific cell* becomes decision-load-bearing — "this lemma is mechanical", "X
  discharges Y", "that route is dead", "this is orphaned" — it stops being gestalt and becomes a
  claim, and a claim from the map is **prose with a freshness stamp, never a crisp truth**. Verify
  it against the territory before acting (the map makes this cheap: it tells you exactly *where*
  to look — verification degrades from search to lookup).
- Verify the **ripples** too: acting on a cell changes its neighbours (retire a lemma → who
  consumes it? adopt a route → which hypotheses does it *now* need? rename → what dangles?). The
  map's edges tell you the blast radius to check; they do not certify it.
The five-fork night (2026-07-14/15) is the demonstration from the usage side: five different
readers took a map-layer cell (a docstring, a cert paraphrase, a ledger DONE, a "zero consumers"
grep) as crisp, and each was wrong in the direction the reader needed it to be; every catch came
from someone re-deriving the cell against the territory at decision time. The contracts below
harden the cells; this principle governs the *reading* — no contract can make prose true, only
fresher.

## Why (one paragraph of origin)

The bottom-up motion (the rising sea: bricks, banked lemmas) has the kernel as its consistency
mechanism and never rotted. The top-down motion (what remains, what discharges what, what is dead)
lived in prose — ledger headlines, tracker verbs — and every endgame failure of aoyagi-full was a
consistency failure there: scope inflation ("crux discharges (a)/(b)" — shell-0 only), orphaned
residuals (the balanced-sector question), found-already-banked (mnp, 319h), rename chains
(hbox→(□)→atom→…→DecoratedDescent), a definition consumed before validated (adm, false-as-stated).
The expedition-map gives the plan a kernel: weaker than the real one — it checks coherence, not
truth — but the same architectural role. Lineage: leanblueprint validates the concept at scale
(LTE, PFR); we do not adopt it (LaTeX substrate, hand-marked status, authored edges — the rot
vectors); we build the thin structured version with computed status and gate-time contracts.

## Shape — a heavy lake, many role-views (revised 2026-07-14, second pass)

The object is NOT the curated file; it is a rich data lake whose small human-written heart is the
claims file, and **everything anyone reads is a generated projection**. (The aoyagi-full retro
substrate — commits/events/threads/decls/cone tables — IS this lake, built read-side post-hoc;
the proposal runs it live.) Layout: `expeditions/<e>/map/` containing `claims.yaml` (curated
heart, sole hand-edited file), `survey/` (computed, heavy, regenerated: decls/deps/status/cone, near-match index,
estimate-outcome history, evidence store — "the map is drawn from the survey"; named to avoid
Lean's `lake`), views via CLI (below), `MapAnchors.lean`, and `STATUS.md` (the ONE materialized
view — the tick-view, auto-written by every validator run, never hand-edited: the post-compaction
breadcrumb and operator glance).

**Views by role and decision cadence** — controller tick-view (~40 lines ambient: frontier,
owners, alarms, gates-opened); controller **decision-view** (on-demand, RICH, 5–20k tokens:
subtree + evidence excerpts + refuted siblings with reasons + near-matches + blast radius +
calibration stats — invoked before every knowing-decision); tide-brief view (the recon-map as a
GENERATED artifact — self-recon upgrades from assembling to verifying); lookahead view (DAG with
build-time vs sorry-propagation edges, unwitnessed edges, owner gaps, coverage-claims-without-
hunts); reviewer view (the landing artifact's consumers + their hypothesis needs); librarian view
(corroboration diffs, near-match queue); operator dashboard; retro = the lake's git history.

Curated-heart schema:

1. **`map/claims.yaml`** — curated, controller-single-writer, ~40–80 entries. One file: the
   single writer removes merge pressure, and one `git log -p` is the plan's full evolution — the
   retrospective resource for free. Entry schema (all fields short):

       id:            crux-pivot-peel          # stable slug, never reused
       kind:          claim | notion | route
       title:         one line
       prop:          prose (pre-formal) — or superseded by the Lean anchor once stated
       lean:          DLNFibre.DLN.RLCT.pivotPeel_domination   # fully-qualified name = join key
       status:        conjectured | cert | stated | skeleton-linked | proven
                      # exits: refuted | superseded | retired  (forwarding pointer mandatory)
       edges:         discharges: [...]  needs: [...]  conjectured-toward: [goal]
                      refutes: [...]     superseded_by: ...
       owner:         lane/seat, or parked: <reason>
       kill:          kill-conditions (claims.md discipline, structured home)
       evidence:      [threads/…/cert.md, …]

2. **`map/survey/`** — computed companion tables (package-lock analogy; never hand-edited). The
   env-walker + extractors derive: lean name exists?, sorried?, axiom closure, referenced-by (edge
   witnesses), fossil/live cone membership, near-match index, estimate-vs-outcome history (one
   convention: a claim's closing delta records predicted-vs-actual — size class, wall/labour call
   — and calibration stats fall out). Regenerated at gate time and librarian cadence.

3. **`MapAnchors.lean`** — the kernel-checked marriage. Every `stated`+ claim gets an
   `example : <statement verbatim> := <lean name>` pin (the harness's existing example-block
   contract pattern, systematized; same family as `AxCheck.lean`). A statement edit breaks the
   build — drift detection at kernel grade. Notions at `frozen` get their defs pinned likewise.

## Maturity ladders

**Claims**: `conjectured → cert → stated → skeleton-linked → proven`. Statuses from `stated` up
are **computed** (walker + anchors), never asserted. Contracts bind progressively by rung —
nothing below `stated` is checked beyond well-formedness.

**Notions (definitions/hypothesis-bundles)**: `proposed → drafted → validated → frozen`.
`validated` requires the bedrock obligations as attached sub-claims: in-file non-vacuity witness,
intended-instance satisfiability, consumer statements typecheck. `frozen` = anchor-pinned; edits
become map events with computed blast-radius (who consumes this notion?). The adm episode is the
motivating trace: a `drafted` notion consumed by a skeleton before `validated`. Statements that
quote a notion carry a `needs` edge — the DAG sequences definitional work ahead of its consumers.

## The freedom principle (the map is not a permission system)

- **Granularity**: research-level claims only. The bottom-up layer — API, atoms, bricks — rises
  with no map presence. A map with thousands of entries has failed.
- **The cheap bottom rung**: an exploration arc costs one `conjectured` node with a one-line prose
  `conjectured-toward(goal)` edge and zero obligations. Let the sea rise; ask only for a sentence
  of story.
- Drift detection flags only work with *no* story: open effort reachable from no root by any edge
  (including conjectured ones). That is the hard-part-avoidance/math-drift query, at the right bar.

## Contracts (enforced by script at the sorries-gate + librarian cadence)

1. Well-formed DAG; stable ids; forwarding pointers on every exit-status node.
2. `stated`+ ⟹ lean name exists AND its MapAnchors pin elaborates.
3. Computed statuses match the kernel (proven ⟺ sorry-free closure, expected axioms).
4. `discharges` edges witnessed (consumer's proof/skeleton references provider) once consumer ≥
   skeleton-linked; unwitnessed edges surfaced as UNWITNESSED, not assumed.
5. Live sorries ⊆ mapped claims (no unregistered frontier); fossil sorries ⊆ artifacts of
   superseded/retired nodes.
6. Open claims have `owner` or explicit `parked` (the orphaned-residual detector).
7. Notions consumed by any `stated` claim must be ≥ `validated` (the adm rule).
8. Every open claim reachable from a root via some edge chain (conjectured edges count).
9. **Route-adoption gate** (2026-07-15, the five-fork night): a `route` node moves to adopted (a tide
   may be spawned on it) only with two machine checks green: **(a)** its composition skeleton
   elaborates against the consumed claims' *verbatim* statements (via their MapAnchors pins — a route
   spec may not re-type a signature from a docstring or cert paraphrase; the consumption edge is
   exactly where paraphrase drifts toward consumer need), sorries only at nodes the route declares
   new; **(b)** every hypothesis the route carries is evaluated at the **corner battery** (below) —
   satisfiable-at-the-visited-instances is not implied by well-typed. Provenance: five consecutive
   route documents in ~12 h each paraphrased a formal statement more generously than it reads, by
   five different authors — structural, not disciplinary; both sub-modes (edge type error; false
   hypothesis at the binding corner) appeared, and each check catches one of them.

**The corner battery** (curated, lives beside `claims.yaml`): the standing family of small
kill-configurations that refuters keep coming from — seeded at genesis from the paper's worked
examples, grown by appending every refuting witness a hunt certifies (aoyagi-full's would be
(2,2,3), (3,3,3), (3,3,4), (3,3,7)@u2j2, (1,1,2,2), (6,6,6)@u4 — 5/5 of the five-fork night's
kill-witnesses were in or adjacent to it). The survey evaluates every open route's hypotheses
against the battery at the green-gate ride-along; a new battery member re-tests all open routes for
free. Property-based testing for plans.

## Flows (the life of the map)

- **Genesis**: one node — the goal, `conjectured`, charter constraints as properties. No scale
  gate; a small expedition's map is five nodes.
- **Decomposition**: controller adds children + edges as routes are designed; competing routes are
  sibling `route` nodes with a chosen-flag. Refuted routes stay in place (`refuted` + evidence) —
  negative knowledge is a query, and fresh-tide briefs cite the refuted-sibling list mechanically.
- **Rising-sea events** (all computed): statement lands → `stated`; skeleton references → edge
  witnessed; sorry closes → `proven`; librarian near-match → `conjectured → proven` directly
  (the found-already-banked fix, and its converse: new claims are checked against the index first).
- **Plan-change events**: refutation flips a node and the contract flags all downstream broken
  edges (blast-radius as computation); scope-split (the T2 case) is caught by the witness check
  failing mechanically, node splits with lineage; supersession leaves a forwarding pointer and
  explains fossils; a frozen-notion edit demands a blast-radius review first.
- **Recovery**: a compacted/restarted controller re-grounds from the map — the
  burden-of-knowledge generational-turnover cost drops to one directory.

## Roles

Controller: sole curated-writer; applies teammate `MAP_DELTA` proposal blocks (REQUEST_SPAWN
pattern). Librarian: regenerates the computed companion; near-match service. Lookahead: audits
map-vs-territory; its pathology checks are map queries. Reviewer AUDIT: consumer-check = edge
audit at landing. Operator: reads the map as the dashboard; `priorities.md` ranks node-ids.

## Scaffold consolidation (what the map retires)

The pre-map scaffold accreted one file per coping mechanism — each a sedimentary layer marking the
moment the previous one rotted (BUILT-INDEX created day 21, endgame-lanes day 23, FRONTIER headers,
NOW markers). Post-map:

- **`brief.md`** — unchanged; the SINGLE durable home of standing directives (heartbeat/loop
  prompts reference it; no more four-way directive copies).
- **`expedition-map/`** — absorbs ALL state (status, edges, ownership, liveness, banked catalog,
  lane assignment). Retires `BUILT-INDEX.md`, `endgame-lanes.md`, FRONTIER headers, NOW markers.
- **`journal.md`** (renamed from `synthesis.md` — name = content): append-only journal of
  decisions and reasoning, entries cite map ids, never restates state. Append-only is
  machine-checked (each commit's journal diff must be pure tail-addition).
- **`priorities.md`** — thinned to a ranked list of map node-ids + one-line taste notes. Owner
  corrected to the CONTROLLER (empirical: the operator channel is conversation + the discuss
  queue; no operator file-edit occurred in 24 days on aoyagi-full).
- **`discuss.md`** — namespaced ids (`D-###`), open items only; resolved auto-archived.
- **`heartbeat-prompt.md`** (renamed from loop-prompt): fixed harness section + a controller
  memo-to-self section. **Pointer form recommended**: the armed cron message is a constant
  "read heartbeat-prompt.md and act" — the file is the source of truth and cannot go stale;
  rearm only on cadence change. (Payload form — memo baked into the cron message — requires an
  edit⟹rearm discipline that is a fresh rot vector; avoid.)
- `threads/`, `lessons.md` unchanged (process lessons there; Lean technique in `lean/CLAUDE.md`;
  thread paths contract-validated). Statement cards become generated views of map nodes.

## Context spend: value-density, not frugality

The principle is **spend proportional to decision value** — the expensive events are never reads;
they are mis-commissioned tides (50–100k tokens + hours), rendezvous-discovered mis-classifications
(T2: half a day), re-derived banked theorems (mnp: 319h), and grep archaeology (re-deriving state
from a 200k-line ledger costs more than any view and misses things). So: AMBIENT recurring reads
stay thin (they are mostly redundant with held context); DECISION moments get deliberately rich
generated views — a 10–20k-token decision-view that prevents one mis-commissioning pays for itself
many times over. Budgets below apply to the ambient tier only:

| artifact | pattern | budget |
|---|---|---|
| heartbeat memo | every cron fire (the multiplier ⟹ costliest real estate) | ≤ 10 lines, entries expire |
| priorities.md | every tick | ≤ 30 lines |
| map-summary (generated view: roots, open frontier + owners, unwitnessed edges, risks) | every tick | ≤ 40 lines |
| expedition-map.yaml (full) | re-ground only | 5–10k tokens; ≤ 12 lines/entry (contract) |
| journal.md | write-mostly; read = tail (~10 entries) post-compaction | tail 2–3k tokens |
| open discuss | per-tick surface | ≤ 20 lines |
| brief.md | re-anchor | 1–2k tokens |

The open-claim count is the over-decomposition alarm (sawtooth; trending past ~30 ⟹ validator
surfaces it). Compaction re-ground = brief → tick-view → priorities → journal tail → open discuss
(~12–15k tokens, CONSTANT in expedition age — the burden-of-knowledge fix as a context budget).
Hold decisions, query facts — and when a decision is at hand, invoke the rich view rather than
re-deriving.

## High-value surfaces (each traceable to a paid cost on aoyagi-full)

1. Per-edge WITNESS status badges (T2 overclaim: half a day).
2. Near-matches at claim creation, from statement-text + fan-in similarity (mnp: 319h, twice).
3. Owner/parked alarms on open claims (the orphaned balanced-sector residual).
4. Refuted-sibling context attached to every route node (the shortcut cycle; covasm).
5. Notion-validation status wherever consumed (adm, false-as-stated).
6. Blast radius on demand — who consumes this notion/lemma (the adm ripple, computed ad-hoc).
7. Evidence freshness: cert dates, statement hashes, last-verified stamps (stale trackers).
8. **Calibration stats**: estimate-vs-outcome base rates surfaced at classification time — "of
   your last 7 'pure wiring' calls, 3 were re-scoped analytic; of 5 'small brick' verdicts, 1 was
   crux-shaped." The lake holds the history; no discipline substitutes for seeing one's own curve.
9. Capacity-vs-rank mismatch (lanes × claims vs priorities — the hard-part-avoidance query).

## Expedition-time operation (vs retro archaeology)

The retro machinery reconstructed state from exhaust (regex over 200k ledger lines, pickaxe
recovery). Expedition-time, state is **born structured** — journal entries cite map ids (no ledger
parsing ever), claims written at the source — so the live survey is SMALLER than the retro lake.
Operating rules:
- **Views are a CLI, not a directory** (a `views/` dir is another rot surface): `map view tick |
  decision <node> | brief <node> | lookahead | reviewer <name>` — computed fresh at invocation,
  each printing its survey anchor. Only STATUS.md is materialized (auto-written).
- **Survey refresh rides the green-gate**: every integration gate = build + AxCheck + walker
  (incremental — re-walk only modules whose oleans changed) + validator + STATUS.md. No new build
  cadence; ~2–3 marginal minutes.
- **Staleness is stated, never hidden**: between gates views render from the last survey with an
  anchor banner; on a broken build the validator reports "territory unreachable since <sha>".
  Views never block on a build.
- **Loud change-classes**: a statement edit breaks its MapAnchor pin (pins compile in the
  aggregator — drift cannot reach a gate silently); a rename breaks the pin too, forcing rename +
  anchor + forwarding pointer into one atomic commit — naming discipline as a build failure, not
  a rule to remember.

## Someday

- **expedition-cli hardening**: `map validate | query | delta` beyond the view subcommands
  (delta = applying teammate MAP_DELTA blocks; render = the blueprint-style dependency view; the
  retro dashboard is the prototype).
- Migration note: statement cards and BUILT-INDEX entries are prose renderings of map nodes;
  on adoption they become generated views, not sources.
