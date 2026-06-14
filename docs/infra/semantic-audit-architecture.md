---
title: "Semantic Audit Architecture"
status: draft
source: original
topics: [infrastructure, semantic-audit, ci]
created: "2026-06-14"
updated: "2026-06-14"
---

# Semantic Audit Architecture

This note is the durable contract for the semantic audit pipeline. It should stay short and be
updated when we change artifact responsibilities.

## Purpose

The semantic audit pipeline turns mathematical review into durable CI-style artifacts.

The pipeline is not a theorem prover. Its job is to coordinate independent attention:

```text
Lean reconstruction
  what the current Lean declaration says

Source intention
  what the paper or exposition appears to intend

Comparison
  whether those two independently produced statements match
```

The key rule is decorrelation. A worker answering a Lean reconstruction should not be guided by the
paper-intention card. A worker answering a source-intention card should not treat the current Lean
statement as ground truth. The comparison packet is where those views meet.

## Artifact Model

There are six artifact types.

```text
Run
  an immutable generated snapshot under .semantic-audit/runs/<run-id>/

Packet
  a generated task in work-packets.jsonl

Bundle
  a portable worker assignment created from one packet

Queue plan
  a generated batch assignment listing packet ids and bundle paths

Answer
  the worker-filled answer.json inside a bundle

Record
  durable accepted audit memory under tools/semantic-audit/records/*.jsonl
```

Only records are durable memory. Runs, packets, bundles, and queue plans are generated artifacts.

## Bundle Files

A bundle has four files.

```text
manifest.json
  controller metadata: run id, packet id, record identity, context file digest

context.json
  the evidence the worker is allowed to use

instructions.md
  worker-facing task description and controller commands

answer.json
  the only file the worker edits
```

The separation is intentional. `context.json` is evidence, `answer.json` is output, and
`manifest.json` is controller state.

## Queue Plans

A queue plan is a generated batch assignment. It is stored as `queue-plan.json` in a batch directory
and contains:

```text
run_id
selection filters
selected packet ids
bundle paths
```

Queue plans are not durable memory and should not be edited by workers. They are a reproducible
controller artifact for assigning many independent packets at once.

By default, queue selection includes only assignable packet states:

```text
open
stale
```

Blocked packets require an explicit debugging override. Already answered packets are not assignable
batch work.

Queue plans must be created from a fresh technically attested run. The controller checks that:

- `lake_build.ok` is exactly `true`;
- `sorries.ok` is exactly `true`;
- the current `HEAD` matches the run attestation;
- the live audit config matches the run snapshot;
- the live durable record files match the run snapshot;
- the live Lean/source/tool input files match the run's generated `audit-input-snapshot.json`.

If any of these checks fail, rerun the audit before assigning semantic work. Debug overrides may
print warnings instead, but that should not be the normal workflow.

## Batch Strata

Batches should contain independent packets. This is not just scheduling hygiene; it preserves the
context-fingerprint invariant.

Lean reconstruction contexts include summaries of answered dependency and user declarations.
Comparison contexts include answered Lean and source records. Therefore, appending one answer can
change another packet's current context.

The controller rejects same-batch dependencies by default:

- two selected Lean reconstruction packets may not be connected by a Lean dependency edge;
- a selected comparison packet may not depend on a selected Lean or source-intention packet.

The intended rhythm is:

```text
bundle one stratum
  -> ingest accepted answers
  -> rerun audit
  -> bundle the next stratum
```

This keeps each accepted record current against the run that generated its context.

## Minimal Provenance

The worker-facing answer carries three provenance fields.

```text
packet_id
source_run_id
context_fingerprint
```

`packet_id` says which generated task was answered. `source_run_id` says which run produced the
bundle. `context_fingerprint` says which semantic evidence the answer summarized.

The manifest additionally carries `context_file_digest`. This is not semantic provenance; it is a
tamper check that `context.json` was not edited after bundle creation.

## Staleness Invariant

The central invariant is:

```text
record.context_fingerprint == current_context_fingerprint(packet)
```

If the equality holds, the durable record is current for that packet.

If the record exists but the fingerprint is missing or different, the packet is stale.

If no record exists, the packet is open.

If a comparison is missing prerequisite Lean/source records, the packet is blocked.

This single invariant is the reason we can safely reuse audit memory across refactors without
pretending old answers are still current.

## Controller Boundary

Workers should not edit durable record files directly.

The controller is the only path from `answer.json` to `tools/semantic-audit/records/*.jsonl`. Before
append, it checks:

- the answer schema;
- the packet kind and target;
- the generated record identity;
- the run guard;
- the exact `context.json` file digest;
- the stable context fingerprint;
- duplicate and replacement policy.

The controller may accept stale bundles only with an explicit `--allow-stale`; such records are
marked with `stale_accepted`.

Batch ingest uses the same checks for each bundle, then validates the whole batch before writing any
record file. Duplicate identities inside the batch are rejected. When appending, each touched JSONL
record file is rewritten through a temporary file and replaced only after the batch has passed
validation.

## Human Workflow

The intended workflow is:

```text
run audit
  -> open dashboard
  -> choose packet or queue plan
  -> create bundle or bundle batch
  -> workers fill answer.json files
  -> controller dry-run ingest
  -> controller append ingest
  -> rerun audit
```

The dashboard should expose this as a simple action queue. The manifest and fingerprint machinery
should remain mostly invisible unless something fails validation.
