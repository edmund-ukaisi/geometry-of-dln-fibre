# Semantic Audit Dashboard

This tool builds the first deterministic slice of the semantic audit CI pipeline.

The durable architecture contract is maintained in
`docs/infra/semantic-audit-architecture.md`.

The committed control surface is:

- `audit-config.json`, which assigns audit tiers and declares source/comparison/API-boundary targets;
- `records/*.jsonl`, which stores answered Lean reconstructions, source-intention cards,
  comparison records, and API-boundary records.

It produces:

- a technical attestation record;
- a Lean-native declaration inventory;
- module and dependency graph data;
- resolved config and normalized record artifacts;
- generated work packets;
- coverage summary data;
- deterministic semantic findings;
- a static HTML dashboard.

Run from the repository root:

```bash
python3 tools/semantic-audit/semantic_audit.py run
```

Fresh worktrees need a usable `lean/.lake` before the extractor can load `DLNFibre`. Either run the
usual Lean setup (`lake exe cache get`, then `lake build`) or reuse a local build cache with an
ignored `lean/.lake` symlink.

The generated output lives under:

```text
.semantic-audit/runs/<run-id>/
```

Important generated files include:

```text
audit-config.resolved.json
audit-input-snapshot.json
lean-reconstructions.jsonl
source-intentions.jsonl
comparisons.jsonl
api-boundaries.jsonl
work-packets.jsonl
coverage-summary.json
findings.jsonl
dashboard/index.html
```

Open:

```text
.semantic-audit/latest/dashboard/index.html
```

The tool intentionally does not call agents yet. It creates deterministic JSON/JSONL packets and an
HTML packet browser so humans or subagents can answer records independently and feed them back into
the next run.

## Packet Answering Workflow

List open Lean reconstruction packets:

```bash
python3 tools/semantic-audit/semantic_audit.py packet list \
  --kind lean_reconstruction \
  --status open
```

Create a worker bundle for one packet:

```bash
python3 tools/semantic-audit/semantic_audit.py packet bundle \
  DLNFibre.Core.intervalModule
```

By default, bundles are written under a run-scoped directory:

```text
.semantic-audit/work/<run-id>/<packet-id>/
```

The bundle contains:

```text
manifest.json
context.json
instructions.md
answer.json
```

The worker reads `instructions.md` and `context.json`, then edits only `answer.json`. For
`lean_reconstruction` packets, the context intentionally excludes source-intention and comparison
records. It also excludes docstrings, raw Lean source excerpts, and prior human-written Lean-card
summaries. It includes only formal Lean evidence: declaration metadata, elaborated type, direct
statement dependencies, proof-only dependencies, and users.

Lean reconstruction answers are intentionally a blind first stage. New templates ask for:

```text
reconstructed_statement
mathematical_role
speculative_source_intent
speculation_confidence
```

The speculation fields are not source evidence. They are a labeled Lean-only guess so later
comparison can notice when the paper reveal confirms, sharpens, or falsifies the initial read.
Because docstrings and source comments are not in the blind bundle, this stage should not inherit
paper labels merely because a Lean docstring cited them.

Comparison answers use a reveal discipline. The worker first summarizes the frozen formal Lean card,
then reads the quarantined Lean prose reveal, then summarizes the source-intention card, and only
then writes the match judgment:

```text
blind_lean_summary
lean_prose_summary
source_summary
match_analysis
discrepancies
```

If a comparison bundle is generated with debug overrides while still blocked, `context.json` includes
`prerequisite_status` so the missing Lean/source card is visible before a worker tries to answer it.

Bundle-generated answer templates include three provenance fields:

```text
packet_id
source_run_id
context_fingerprint
```

The controller checks these fields against `manifest.json` and the current packet context before
append. This is what lets a later run distinguish a current answer from a stale answer after Lean
signatures, source excerpts, dependency cards, or packet inputs change.

The bundle manifest also contains `context_file_digest`, an exact-file tamper check for
`context.json`.

After the worker fills `answer.json` and sets `"status": "answered"`, the controller lints and
validates the bundle:

```bash
python3 tools/semantic-audit/semantic_audit.py packet ingest \
  .semantic-audit/work/<run-id>/<packet-id> \
  --dry-run
```

Append the durable record only after the dry run is clean:

```bash
python3 tools/semantic-audit/semantic_audit.py packet ingest \
  .semantic-audit/work/<run-id>/<packet-id> \
  --append
```

`packet ingest` checks the answer schema, packet kind, target identity, bundle run id, exact
`context.json` digest, stable context fingerprint, answer identity, and duplicate/replace policy.
Use `--replace` only when intentionally replacing an existing durable record with the same identity.
Use `--allow-stale` only when intentionally ingesting a bundle generated from an older run; the
controller will mark stale-accepted records with a `stale_accepted` field. `packet ingest --append`
requires a bundle manifest by default; raw JSON records should normally use `packet append`.

Packets can have four lifecycle states:

```text
open      ready for work
blocked   waiting for prerequisite Lean/source cards
stale     backed by a durable record whose context is no longer current
answered  backed by a durable record for the current context
```

`packet bundle` refuses blocked packets unless `--allow-blocked` is passed for debugging. Stale
packets should be rebundled from the current dashboard run and answered as a new versioned record.

The lower-level commands remain available for manual debugging:

```bash
python3 tools/semantic-audit/semantic_audit.py packet context DLNFibre.Core.rankPattern
python3 tools/semantic-audit/semantic_audit.py packet scaffold DLNFibre.Core.rankPattern
python3 tools/semantic-audit/semantic_audit.py packet validate /tmp/rankPattern.record.json --for-append
python3 tools/semantic-audit/semantic_audit.py packet append /tmp/rankPattern.record.json --dry-run
```

Rerun the deterministic pipeline afterward:

```bash
python3 tools/semantic-audit/semantic_audit.py run
```

For fast local iteration, use `--skip-build` only when a fresh Lean build/sorries attestation already
exists for the same commit and worktree state.

The dashboard will then mark the packet answered and show the answer body in the Work Packets
inspector.

## Batch Worker Orchestration

Batch orchestration is the queue-oriented version of the same workflow. It does not introduce a new
durable memory store. It creates generated queue plans and generated bundles, prepares prompts for
Claude Code/Codex/Agent Teams/human workers, then validates returned `answer.json` files through the
same controller boundary.

Preview a deterministic queue:

```bash
python3 tools/semantic-audit/semantic_audit.py packet queue \
  --kind source_intention \
  --status open \
  --limit 3
```

Create a batch of worker bundles:

```bash
python3 tools/semantic-audit/semantic_audit.py packet bundle-batch \
  --kind source_intention \
  --status open \
  --limit 3
```

The command writes:

```text
.semantic-audit/work/<run-id>/batch-<digest>/
  queue-plan.json
  bundles/
    <packet-id>/
      manifest.json
      context.json
      instructions.md
      answer.json
```

Each worker receives one bundle directory, reads `instructions.md` and `context.json`, and edits only
that bundle's `answer.json`.

Prepare agent-native dispatch prompts:

```bash
python3 tools/semantic-audit/semantic_audit.py packet dispatch-batch \
  .semantic-audit/work/<run-id>/batch-<digest>
```

This writes:

```text
.semantic-audit/work/<run-id>/batch-<digest>/
  dispatch-manifest.json
  bundles/
    <packet-id>/
      worker-prompt.md
```

The repo tool does not launch agents. The active controller session assigns each `worker-prompt.md`
to a Claude Code, Codex, Agent Teams, or human worker. V1 assumes shared bundle files: workers edit
the generated `answer.json` in the same checkout. If a substrate uses isolated worktrees, copy the
completed `answer.json` files back before collection.

Collect returned answers and write a generated run report:

```bash
python3 tools/semantic-audit/semantic_audit.py packet collect-batch \
  .semantic-audit/work/<run-id>/batch-<digest>
```

This writes:

```text
.semantic-audit/work/<run-id>/batch-<digest>/worker-run.json
```

`collect-batch` validates the whole batch without writing durable records. The lower-level validator
remains available when no worker-run report is needed:

```bash
python3 tools/semantic-audit/semantic_audit.py packet ingest-batch \
  .semantic-audit/work/<run-id>/batch-<digest>
```

Append only after the batch dry run is clean:

```bash
python3 tools/semantic-audit/semantic_audit.py packet collect-batch \
  .semantic-audit/work/<run-id>/batch-<digest> \
  --append
```

`collect-batch --append` delegates to the same two-phase append logic as `ingest-batch`: it validates
every bundle first, rejects duplicate identities inside the batch, and only then rewrites touched
durable record files. A validation failure leaves durable records unchanged.

Batch commands require a fresh technically attested latest run: `lake build` and the sorry/axiom
check must both be clean, and live config, record, Lean/source, and audit-tool inputs must match the
latest run's `audit-input-snapshot.json`. Rerun the audit after ingesting records before assigning
the next stratum.

The default queue includes only `open` and `stale` packets. Dispatch defaults to `source_intention`
packets. Blocked, answered, internally dependent, non-source, or non-fresh batches require explicit
debug flags. In normal use, keep strata separate:

```text
Lean reconstructions or source-intention cards
  -> rerun audit
  -> comparisons using blind-Lean-then-reference reveal
  -> rerun audit
  -> API-boundary reviews or follow-up strata
```
