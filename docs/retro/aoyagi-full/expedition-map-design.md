# The expedition-map — design note (harness proposal, 2026-07-14)

**The map is not the territory.** The kernel is the territory; the expedition-map is the top-down
record of claimed land and charted routes, and every contract below exists to keep the map honest
against the territory. Write this slogan wherever the map is taught; it is the design discipline
in one line.

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

## Shape

Three artifacts in `expeditions/<e>/`:

1. **`expedition-map.yaml`** — curated, controller-single-writer, ~40–80 entries. One file: the
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

2. **`expedition-map.status.json`** — computed companion (package-lock analogy; never hand-edited).
   The env-walker derives per-entry: lean name exists?, sorried?, axiom closure, referenced-by
   (edge witnesses), fossil/live cone membership. Regenerated at gate time and librarian cadence.

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

## Context budgets (controller context management)

Every recurring read carries a hard size budget with a contract check — files without budgets grow
(synthesis.md's 200k lines are the proof). Access patterns:

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
surfaces it). Compaction re-ground = brief → map-summary → priorities → journal tail → open
discuss (~12–15k tokens, CONSTANT in expedition age — the burden-of-knowledge fix as a context
budget). Hold decisions, query facts: anything queryable (banked details, dependency facts,
history) stays out of context.

## Someday

- **expedition-cli**: `map validate | query | delta | render` (render = the blueprint-style
  dependency view; the retro dashboard is the prototype).
- Migration note: statement cards and BUILT-INDEX entries are prose renderings of map nodes;
  on adoption they become generated views, not sources.
