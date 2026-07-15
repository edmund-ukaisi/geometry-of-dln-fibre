# expedition CLI — implementation notes (v0)

The v0 prototype of the expedition-map CLI. Contract of record is
[`expedition-map.md`](expedition-map.md); this file records the decisions taken
where that spec is silent, the survey adapter's assumptions, and known v0 limits.

## Layout

```
scripts/expedition                 executable launcher (stdlib only; adds scripts/ to path)
scripts/expedition_map/
  model.py        load + index claims.yaml; vocabulary; dependency graph + reachability
  survey.py       walker-dump adapter; per-node join; git freshness
  validate.py     contracts 1-10 -> Findings (error | warning)
  views.py        tick/STATUS, decision, lookahead, dag, brief
  battery.py      header parsing + script execution + verdicts
  ops.py          rename, tombstone, new, calibration, anchors
  cli.py          argparse dispatch
scripts/hooks/pre-commit           runs `validate --fast` on every expeditions/*/map
tests/                             pytest (74 tests); real fixture under tests/fixtures/
```

Dependencies: Python 3.12, `pyyaml` (6.0.3), stdlib. No framework, no classes
where a dict does. Run: `python3 -m pytest tests/ -q` (pytest 9.0.3 present).

## Install the hook

```
git config core.hooksPath scripts/hooks
```

The hook is a no-op unless the working tree has `expeditions/*/map/claims.yaml`;
on those it runs `expedition validate --fast` (structural contracts + lints, no
survey/battery), quiet on success, blocking on contract errors. It never blocks
for infrastructure reasons (missing python3 / launcher => silent exit 0).

## The survey adapter — two modes (the central decision)

The spec assumes the walker dump carries per-decl deps + axioms. The real dumps
in `docs/retro/aoyagi-full/substrate/` come in **two shapes**, so the adapter
auto-detects a *mode* and records it in the survey's freshness stamp:

- **full** — a `{decls: [...]}` (or bare list) dump where each record has
  `deps_type`/`deps_proof`/`axioms` (the `decls.json` shape, 8428 decls).
  Existence, sorry-taint (closure contains `sorryAx`), discharge-edge witnessing
  (consumer's transitive deps contain the provider), and the root live-sorry cone
  are all **definitive**.
- **cone** — a `{headlines: [...], cone: [<name>...]}` dump: the transitive
  dependency cone of already-proven roots, names only (the
  `cone_before_mint.json` shape, 2897 names). This can **confirm** a decl is
  present (in-cone ⟹ exists and is sorry-free, since it feeds a proven root) but
  cannot **refute** existence — a decl outside the roots' cone may simply be live
  frontier not yet wired to a proven headline. It carries no deps/axioms.

Node↔decl keying: exact Lean name, else unique last-dotted-component ("short
name") match, since `claims.yaml` anchors are usually unqualified
(`deeperFlag_shell_le`, not `DLNFibre.DLN.RLCT.deeperFlag_shell_le`). Ambiguous
short matches resolve to none and are surfaced.

**Why this matters for the contracts.** Against a cone-mode survey the
survey-dependent checks degrade to *warnings*, honestly, rather than firing false
errors:

- C2 (anchor existence): in-cone ⟹ confirmed (pass); not-in-cone ⟹ warning
  ("may be live frontier; run full walker to confirm"); in **full** mode a truly
  absent decl is a hard **error**.
- C3 (proven ⟺ sorry-free): cone mode cannot see axioms ⟹ warning
  "unverifiable"; full mode gives a hard error on a sorry-tainted `proven` node.
- C4 (discharge witnessing): cone mode has no deps ⟹ every gated edge is a
  warning "UNWITNESSED (dep data unavailable)"; full mode gives a hard error when
  the provider is genuinely absent from the consumer's closure.
- C5 (live sorries ⊆ mapped nodes): cone mode ⟹ single warning "not computed".

This is the honest reading of "the map states its staleness rather than hiding
it": the tool reports exactly what the available territory can and cannot decide.

## Decisions where the spec was silent

- **Dependency direction.** `needs`/`conjectured-toward` from n are `n → to`
  ("n depends on to"). `discharges` is **reversed** (`n discharges t` ⟹ `t → n`,
  because the discharger n is the provider that closes t's obligation). This is
  what makes a node carrying both "box needs deeper" and "deeper discharges box"
  a single edge, not a false 2-cycle. `refutes` is orthogonal to dependency and
  excluded from the DAG.
- **Reachability / liveness (C8).** Undirected connectivity to a root over
  dependency edges (needs / discharges / conjectured-toward / refutes). Exit
  edges (`forwarded-to` / `superseded-by`) do **not** carry liveness — a retired
  node pointing at a live successor stays dead. Only **open** nodes trigger the
  C8 orphan error; closed (proven/frozen/landed) or exited orphans are reported
  by the survey but are not errors.
- **Open vs closed.** open = status not in {proven, frozen, landed} ∪ {refuted,
  superseded, retired}. Ownership (C6) and reachability (C8) apply to open nodes
  only.
- **C2 missing anchor.** A `stated`+ claim (or `adopted`+ route) with no `lean`
  field is a **warning**, not an error, so the map can represent a node proven
  inline without a standalone anchor (e.g. the fixture's `j0-sector`). The spec's
  "stated+ ⟹ lean exists" is enforced hard only for the *existence* of a declared
  anchor in full mode.
- **C9 route-adoption gate.** v0 cannot run Lean elaboration, so an `adopted`+
  route emits **warnings** (not errors): (a) it must have ≥1 `needs` edge and each
  needed claim should be `stated`+ (else the skeleton can't elaborate against a
  verbatim statement yet); (b) some battery must evaluate its hypotheses (its own
  `kill` or a needed node's). Full enforcement is the green-gate's job.
- **The validator as a gate on every command.** Read/report commands
  (status, view, brief, battery) run `validate --fast` first and abort (exit 2)
  on contract errors; warnings print a one-line count to stderr and proceed
  (`--strict` makes warnings abort too). Write ops (rename/tombstone) do their own
  re-parse guard instead. `new` needs no map.
- **STATUS unwitnessed count.** The tick view counts discharge edges as
  UNWITNESSED only once the consumer is `skeleton-linked`+ (matching C4's gate),
  so the STATUS number agrees with the validator's.
- **calibration scoring.** Naive: parse a leading number from predicted/actual;
  both numeric ⟹ matched / over- / under-estimated (actual > predicted =
  under-estimate); non-numeric equal strings ⟹ matched; else unscored.

## Landmarks (§ Landmarks)

`landmark: true` (optional bool, default false) marks the carried shortlist.
Contract **11** is structural (runs in `--fast`): a hard **error** when the count
exceeds the cap of 9, and its message names every landmark so demotion is a copy
away; a **warning** when a landmark sits on an exit status (retired / superseded /
refuted — a stale landmark to retire from the shortlist). Landmarks open
`STATUS.md` / `view tick` (a `## landmarks` section before roots); the tick view
is budget-aware, so with a full shortlist it compresses the live-frontier list
(`… +N more`, blocked entries dropped first) to hold the 40-line cap. `brief`
at resolution ≥ 2 and `view decision` add a landmark-orientation section that
phrases the target's relation to each landmark over the dependency graph —
`ancestor (this feeds it)`, `descendant (feeds this)`, `sibling`, `is this node`,
or `no direct edge`. `view dag --landmarks` shows only landmark nodes and the
edges among them. Spec-silent decision: the relation phrasing uses the dependency
direction from `build_dep_graph` (discharges reversed), and "sibling" means a
shared direct consumer.

## Known v0 limits

- **anchors emit is honest, not complete.** It emits `#check @<name>` pins plus a
  `-- TODO statement pin` comment per node — a real `example : <prop> := <name>`
  needs hand-translation of the prose prop into a Lean term. Only nodes with both
  `lean` and `prop` are pinned. It is not wired to a compile step here.
- **No per-node ages.** `claims.yaml` has no per-node timestamps, so the tick view
  shows owner + status but not age; a git-blame pass would recover ages (deferred).
- **rename prose caveat.** The id rewriter only touches structural positions
  (`id:` / `to:` / `roots`), leaving `title`/`notes`/`prop`/`evidence` prose
  untouched — verified by test. Block-style `roots:` lists are handled; a rename
  that must reach into prose is out of scope.
- **tombstone is line-oriented.** It edits the node's block in place (status →
  retired, appends a `forwarded-to` edge after the last field) so comments and
  ordering survive; it recognizes `- id: <id>` block-list form (the authored
  format). It does not retire the Lean skeleton hole — that is a manual step the
  command's output reminds you to do (spec contract 5 fossil rule).
- **survey freshness.** Stored git HEAD vs current HEAD flags staleness; outside a
  git repo (e.g. a tmp copy) the head is `None` and nothing is falsely marked
  stale. `survey/` is gitignored (computed, cannot rot); `STATUS.md` is committed.

## How to run

```
# validate (full uses survey if present; --fast is structural only)
scripts/expedition --map <dir> validate [--fast] [--strict]

# build the computed survey from a walker dump (full or cone shape)
scripts/expedition --map <dir> survey --from <walker.json>

# views
scripts/expedition --map <dir> status                 # writes STATUS.md
scripts/expedition --map <dir> view tick|decision <id>|lookahead|dag [--kind K] [--status S]
scripts/expedition --map <dir> brief <id> --resolution 1..4

# battery / ops
scripts/expedition --map <dir> battery run [--node <id>]
scripts/expedition --map <dir> rename <old> <new>
scripts/expedition --map <dir> tombstone <id> --forward <id> --reason "..."
scripts/expedition new claim|notion|route <id>        # prints a scaffold
scripts/expedition --map <dir> calibration add --node <id> --predicted "x" --actual "y"
scripts/expedition --map <dir> calibration show
scripts/expedition --map <dir> anchors emit [--out MapAnchors.lean]

# tests
python3 -m pytest tests/ -q
```

The real integration fixture is `tests/fixtures/aoyagi-endgame/` (a genuine map
of the aoyagi-full endgame). Survey it from the real walker dump:
`scripts/expedition --map tests/fixtures/aoyagi-endgame/map survey --from
docs/retro/aoyagi-full/substrate/cone_before_mint.json` (cone mode).
