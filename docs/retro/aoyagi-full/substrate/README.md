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

## Known data gaps (honest)

1. The live ledger holds ~836 of ~995 UPDATE blocks — early blocks were compacted away during
   the run. Recovery path (H⁻, planned): parse `synthesis.md` at *historical* commits and union
   the blocks; the full ledger exists in git history even where the tip file doesn't have it.
2. ~44% of ledger sha-refs don't resolve inside `fork..branch` — mostly banked-but-unmerged
   work-branch artifacts (itself informative: references to work that never reached canonical);
   resolving against `--all` refs is a planned upgrade.
3. Flag counts are keyword-grade: `corrected` on a block ≠ one correction event (a block can
   discuss corrections). Event-grade classification is the S pass, run over `line_start/end`
   anchors.

## Planned next extractors

- `walk_decls` (Lean metaprogram): decls + statements + proof-term dependency edges → the
  structure themes; needs a built tree (kick `lb DLNFibre` first).
- Longitudinal ledger recovery (gap 1) + `--all`-refs sha resolution (gap 2).
- Claimed-vs-kernel auditor: every `clean-three @sha` ledger claim re-checked against the kernel
  at that sha (port of the dev cordon batch collector).
