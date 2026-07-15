# The expedition-map

The top-down layer of an expedition — the plan — given the same architecture the bottom-up layer
(the Lean tree) already has: checked artifacts, computed status, executable refutations, a typed
frontier. **The map is not the territory** (the kernel is the territory; every contract below keeps
the map honest against it), and **the map is for gestalt, not citation** — read it to decide what
matters, read the territory to decide what is true; any cell that becomes decision-load-bearing is
re-verified against the territory, with its ripples ([`principles.md`](principles.md) P7).

The map is one object in two parts: the **ledger** (the `expeditions/<slug>/map/` directory below —
nodes, status, witnesses) and the **engine** (the skeleton — settled decisions reified as typed,
sorried Lean holes wired to the headline, so the brick-closing gradient pulls along the adjudicated
route; P6). A map built as ledger alone is bookkeeping with no pull; the anchor pins and hole↔node
links below are what tie the two parts together.

## Layout — one authored file, everything else computed or curated

```
expeditions/<slug>/map/
├── claims.yaml   AUTHORED  the heart: the plan of record (single curated writer: controller)
├── battery/      CURATED   executable witnesses (kill-conditions as scripts, not sentences)
├── overlay/      CURATED   cartographer: banked-family cards, dead-route registry, naming pointers
├── survey/       COMPUTED  regenerated from the Lean walker + git; gitignored; cannot rot
└── STATUS.md     MATERIALIZED  the sole committed view (tick-view; the post-compaction breadcrumb)
```

`claims.yaml` is never generated; it is the one thing a person (the controller) writes. Everything
voluminous is computed against it, joined by node `id` and `lean` anchor. Views are joins of
heart × survey × overlay — rendered by the CLI, never edited.

## The heart — `claims.yaml` schema

```yaml
meta:
  expedition: <slug>
  roots: [<node-id>, …]        # the goal statement(s); liveness = reachability from here
  updated: <date>              # bumped by any edit; validator warns on staleness vs git

nodes:
  - id: box-threshold          # stable kebab-case id; rename ONLY via `expedition rename`
    kind: claim                # claim | notion | route
    title: "(□) box-integral finiteness below T1"     # ≤ 80 chars, names what is PROVEN-or-claimed
    prop: |                    # the statement, verbatim math or Lean-adjacent; for `stated`+ nodes
      ∀ c' < minAdm(M)/2, ∫_box frobSq(prod M ·)^(−c') < ⊤
    lean: RouteMBoxThresholdFinite    # decl name once stated; anchor pin ties prose to kernel
    status: skeleton-linked    # see ladders below
    tier: new                  # new | established  (established = cited source carries burden)
    owner: capstone            # thread/seat name, or `parked: <one-line reason>` — never blank
    kill: battery/box-diverges-at-threshold.py   # executable kill-condition (battery ref)
    edges:
      - {type: needs, to: deeper-flag-shell-le}
      - {type: discharges, to: mint-108}
    evidence: [threads/genm-incidencepp/incidence-cert.md]   # pointers, never restated content
    notes: "one-line hooks only; content lives at the pointers"
```

**Kinds.** `claim` — a mathematical statement with a truth-value. `notion` — a definition/carrier
whose *shape* is the design question (a recurring failure: a notion consumed by builds before it
was validated, and false-as-stated). `route` — a proof strategy: a decomposition claim ("these nodes compose to that
one") subject to the adoption gate.

**Edges.** `needs` (dependency), `discharges` (this node closes that obligation — must become
witnessed, contract 4), `conjectured-toward` (free-form prose edge; the cheap bottom rung),
`refutes` (node → node, with battery witness), `superseded-by` / `forwarded-to` (exit pointers —
tombstones, never silence).

## Maturity ladders (one per kind)

- **claim**: `conjectured` → `adjudicated` (a cert with witnesses exists; for `tier: established`,
  verified against the source — the former claims-policy `verified`) → `stated` (Lean statement exists +
  anchor pin) → `skeleton-linked` (a consumer in the skeleton elaborates against it) →
  `proven` (sorry-free closure, expected axioms — computed, not asserted).
  Exits: `refuted` (battery witness attached) / `superseded` / `retired` (+ `forwarded-to`).
- **notion**: `proposed` → `drafted` → `validated` (stress-tested; adversarially probed) → `frozen`.
  Contract 7: a notion consumed by any `stated`+ claim must be ≥ `validated`.
- **route**: `proposed` → `adopted` (the **route-adoption gate**, below) → `building` → `landed` /
  `refuted`.

Tide-eligibility (the old maturity gradient): a `new` claim needs `adjudicated`; an `established`
claim's adjudication is the light verify-against-source. The AUDIT gate is unchanged and universal.

## The engine face — skeleton linkage

- A settled fork becomes skeleton **immediately** (promotion lag ≈ 0; P6): the adjudicated
  decomposition lands as a driver + obligation-record in Lean (statement-locked-ish, sorried, on
  canonical, wired to the headline). Each skeleton hole carries a map node id in its docstring
  (`-- map: <node-id>`); each `stated`+ node carries its `lean` name.
- **Anchor pins**: `expedition anchors emit` writes `MapAnchors.lean` — one
  `example : <prop-as-stated> := <lean-name>` per pinned node — compiled at the green-gate, so a
  statement edit that breaks fidelity is a build failure, and a rename without a forwarding pointer
  cannot land quietly.
- A `refuted`/`superseded` node **retires its skeleton hole** in the same commit (contract 5's
  fossil rule) — a stale hole is worse than none: pull is strong and neutral.

## The battery — refutations as tests

`battery/<name>.py`: a small, exact, self-contained script (stdlib/sympy-class; exit 0 = claim
survives, exit 1 = killed, other = error) with a frontmatter docstring: which node(s) it kills or
guards, the config (e.g. `M=(3,3,3), t=1, c'=4`), provenance (the cert that produced it). Seeded at
genesis from the source's worked examples; **every hunt-certified refuting witness is appended** —
a settled fork's deliverable includes its witnesses (P1). `expedition battery run` executes them;
the survey refresh re-runs the battery against all open routes' hypotheses, so a new witness
retro-tests every live plan for free.

**The route-adoption gate** (a `route` node moves `proposed → adopted` only with both green):
(a) its composition skeleton elaborates against the consumed nodes' *verbatim* statements (via
anchor pins — a route spec may not re-type a signature from a docstring or cert paraphrase);
(b) every hypothesis the route carries is evaluated at the battery. Skeleton *revisions* re-run the
same gate — loud, priced events, never quiet edits.

## The overlay — the cartographer's layer

`overlay/` holds what judgment curates over the computed layer: **banked-family cards** (per lemma
family: what exists, what each assumes, the near-misses one hypothesis away),
the **dead-route registry** (refuted approaches + one-line reasons + battery pointers), **naming
forwarding-pointers** (every rename leaves one; `expedition rename` maintains them), and
**tombstones** for decayed detail. Promote/decay judgment reads the elder's `compass.md` first —
what is low-level enough to sink depends on what the expedition cares about.

## The survey — computed, riding the green-gate

Regenerated (never edited) from: the Lean declaration walker (names, statements, deps, axioms,
sorries), git state (branches, tips, freshness), battery results. Provides the computed joins:
per-node kernel status (`proven` ⟺ sorry-free closure with expected axioms), discharge-edge
witnessing (does the consumer's proof term reference the provider), the live-sorry cone from
`meta.roots` (goal-relative zero-sorry: LIVE frontier vs fossils), orphan detection (open effort
reachable from no root). Refresh rides the existing green-gate (build + AxCheck + incremental walk,
~2–3 marginal minutes); on a broken build the survey **states** its staleness ("territory
unreachable since <sha>") rather than hiding it. Merge conflicts in computed files are resolved by
regeneration, by definition.

## Views — generated, per audience, at graded resolution

| view | audience | budget | content |
|---|---|---|---|
| `view tick` → STATUS.md | controller (every tick; post-compaction) | ≤ 40 lines | roots' distance, live frontier, open gates, owners, staleness |
| `view decision <id>` | controller at a decision | rich (5–20k tokens) | the node's full context: cone, siblings, refuted-sibling history, battery, evidence |
| `brief <id> --resolution 1–4` | worker teammates at spawn / mid-thread descent | printed token estimate | ancestors→root, siblings, attached battery, banked/near-miss cards, dead routes with reasons, traps |
| `view lookahead` | navigator office | ≤ 7 items feed | open-node DAG (build-time vs sorry-propagation deps), idle-lanes-vs-open-gates, gates-ran ledger |
| `view dag` | any | — | the edge graph, filtered by kind/status |

Don't economize on the decision and brief views — ambient context stays thin so that
decision-relevant context can be rich (the value-density principle). `STATUS.md` is the *only*
materialized view; a views/ directory of stale renders is the rot surface this design removes.

## Contracts (the validator; every CLI command runs it, pre-commit runs `--fast`)

1. Well-formed DAG; stable ids; every exit-status node carries a forwarding pointer.
2. `stated`+ ⟹ `lean` exists AND its anchor pin elaborates (pin compile at green-gate; `--fast`
   checks existence against the survey).
3. Computed statuses match the kernel (`proven` ⟺ sorry-free closure, expected axioms).
4. `discharges` edges witnessed once the consumer is ≥ `skeleton-linked`; unwitnessed edges are
   surfaced as UNWITNESSED, never assumed.
5. Live sorries ⊆ mapped nodes (no unregistered frontier); fossils ⊆ retired/superseded nodes'
   artifacts (and flagged for pruning).
6. Every open node has `owner` or explicit `parked` (the orphaned-residual detector).
7. Notions consumed by any `stated`+ claim are ≥ `validated`.
8. Every open node reachable from a root via some edge chain (`conjectured-toward` counts — the
   freedom principle's cheap rung; unreachable effort is the drift flag, at the right bar).
9. **Route-adoption gate** (above) for `route` nodes at `adopted`+; skeleton revisions re-gated.
10. **Lints**: view/file budgets (STATUS ≤ 40 lines; `notes` one line; priorities ≤ 30); the
    **selling-register lint** — `mechanical`, `just wiring`, `bypasses`, `trivially`, `suffices`
    in a route/claim `notes`/`title` without a witness or evidence pointer is a warning (P5:
    the record is the reward model).

## Ownership and operations

- **claims.yaml**: controller, single curated writer. Everyone else proposes `MAP_DELTA` (a patch
  block in a report); the controller applies. Operator edits `priorities.md` (ranked node ids) as
  the taste channel, and may edit the map directly (highest authority).
- **overlay/**: cartographer, single writer, within its own authority (nothing destructive —
  everything is pointers and git-recoverable). Plan-layer changes it wants are MAP_DELTAs.
- **battery/**: append-mostly; any seat's certified witness is added by the controller/cartographer
  with provenance.
- **Guarded ops** (where hand-editing is error-prone, the CLI is authoritative):
  `expedition rename <old> <new>` (atomic: id rename + reference rewrite + forwarding pointer +
  anchor regeneration), `expedition tombstone <id>`, `expedition new <kind>` (scaffold a node).
  All other edits are by hand; the validator catches what hands break.
- **Hooks**: pre-commit runs `expedition validate --fast` (structural contracts, lints); the
  green-gate runs the full validator + survey refresh + anchor compile + battery.

## Granularity and freedom

Research-level nodes only — the bottom-up layer (API lemmas, atoms, bricks) rises with no map
presence; a map with thousands of entries has failed. An exploration arc costs one `conjectured`
node with a one-line `conjectured-toward` edge and zero obligations: the map is not a permission
system; let the sea rise, ask only for a sentence of story.

## Genesis

At expedition setup: `meta.roots` + the goal node(s); the battery seeded from the source's worked
examples; the skeleton seeded the moment the first fork is adjudicated (the digestion/adjudication
phase's deliverable contract — [`expedition.md`](expedition.md) § Phases). For open problems the
adjudication never ends: forks settle progressively and the skeleton ratchets, one fork at a time.
