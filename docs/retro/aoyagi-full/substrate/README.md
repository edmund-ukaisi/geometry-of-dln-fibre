# Substrate — the hard-data pool

All generated files are gitignored; regenerate with:

    python3 mine_commits.py && python3 parse_ledger.py && python3 join.py

Read-only against `origin/expedition/aoyagi-full`; safe to rerun as the branch moves.

## Tables & join keys

- `commits.json` — one row per commit in `FORK..BRANCH`. Keys: `sha` (short), `sha_full`,
  `update_refs` (UPDATE-N in subject), `thread_slugs`, `teammate_tag`, `item_refs`,
  `files[].path`, `files[].pillar`. Also `kind`, per-commit lean/docs adds/dels.
- `events.json` — one row per `⚙ UPDATE-N` block in the ledger *as it exists at the branch tip*.
  Keys: `update_n`, `date`, `thread_slugs`, `sha_refs` → `resolved_shas`, `item_refs`,
  `landed_commit`/`landed_iso` (E1 join), `line_start`/`line_end` (1-based into
  `synthesis.md@branch` — drill-in anchor for semantic passes), `flags` (keyword indicators —
  deliberately noisy-but-mechanical; the S-grade classification pass refines them later).
- `threads.json` — one row per thread slug seen in commit subjects/scopes: span, commit counts,
  lean LoC, UPDATE mentions, combed role/pillar where matched (T2, fuzzy — 27/275 matched;
  micro-tides are finer-grained than the combed campaign threads by design).
- `pool_summary.md` — join-quality stats + first readouts.

## `decls.json` — Lean environment walk (`WalkDecls.lean`)

One row per **source declaration** whose defining module starts with `DLNFibre` (Core + DLN,
everything). Auto-generated decls are skipped (recursors, `.casesOn`/`.recOn`/`.brecOn`/`.below`,
`.injEq`/`.inj`, `.noConfusion*`, `.ctorIdx`/`.congr_simp`, `match_*`/`proof_*`/`_eq_*`/`_private.*`
via `Name.isInternalDetail` + a suffix blacklist). Each row:

- `name`, `kind` (`theorem|def|abbrev|structure|inductive|instance|opaque|axiom`), `module`,
  `file` (`lean/DLNFibre/…​.lean`), `line` (declaration start incl. its docstring; `0` if no range).
- `statement` — pretty-printed type, notation delaborated (`≤`, `∑'`, `^`, `ℝ`), truncated at 2000 chars.
- `n_binders` — leading `∀`/`Π` count (hypothesis-count proxy).
- `deps_type` / `deps_proof` — `DLNFibre.*` constants used by the type / by the value (proof term),
  self excluded.
- `axioms` — transitive axioms (matches `Lean.collectAxioms`; the field to read for the `sorryAx`
  footprint and the clean-three `[propext, Classical.choice, Quot.sound]`).

Each row is keyed to its **owning** module (`getModuleIdxFor?`), so names are unique even when a short
lemma name is declared in two closure files. Regenerate from the `lean/` directory **after a green
`scripts/lb DLNFibre`** (the walker imports the compiled environment):

    cd lean && lake env lean --run ../docs/retro/aoyagi-full/substrate/WalkDecls.lean \
      --module DLNFibre --prefix DLNFibre \
      --out ../docs/retro/aoyagi-full/substrate/decls.json \
      --generated "$(date -u +%Y-%m-%dT%H:%M:%SZ)"

`--module`/`--prefix` are configurable (e.g. a `Mathlib.*` namespace prototypes without building
DLNFibre). The walker is `unsafe` and calls `enableInitializersExecution` so `importModules
(loadExts := true)` runs the imported `initialize` code through the interpreter — required for
notation to delaborate. Axiom collection is memoized across decls (a shared reachability cache),
which keeps the walk near-linear; run time ≈ 2.5 min (≈14 s import + init, ≈2 min walk) for ~8.4k
decls.

## Known data notes (honest)

1. Ledger coverage: 991/995 blocks (range 5..999; missing 300, 615-617 = referenced numbers
   that never existed as blocks). Two header formats live at tip (early `**★★ UPDATE-N`,
   later `**⚙ UPDATE-N`); the parser handles both. The initial "compacted ledger" reading was
   a parser artifact — corrected via the A1 metric.
2. Early-era (N ≲ 136) `date` fields are format-migration backfill stamps; use `landed_iso`
   (`date_quality` field: ok / midnight-straddle / early-backfill / no-landing).
3. sha-ref classes: in_canonical / exists_unmerged (banked-on-work-branches volume — itself a
   readout) / agent_id_like (harness tide-ids, a join key to threads) / unknown (2 refs, likely
   never-pushed rebased objects).
4. Flag counts are keyword-grade: `corrected` on a block ≠ one correction event. Event-grade
   classification is the S pass, run over the `anchor_ref`+`line_start/end` drill-in anchors.

## Planned next extractors

- Longitudinal ledger recovery (gap 1) + `--all`-refs sha resolution (gap 2).
- Claimed-vs-kernel auditor: every `clean-three @sha` ledger claim re-checked against the kernel
  at that sha (port of the dev cordon batch collector).
