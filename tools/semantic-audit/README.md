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
records. It includes the Lean declaration signature, docstring, source excerpt, direct statement
dependencies, proof-only dependencies, users, and any answered Lean cards for dependencies.

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
