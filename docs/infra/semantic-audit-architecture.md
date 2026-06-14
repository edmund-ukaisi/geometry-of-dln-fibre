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

There are five artifact types.

```text
Run
  an immutable generated snapshot under .semantic-audit/runs/<run-id>/

Packet
  a generated task in work-packets.jsonl

Bundle
  a portable worker assignment created from one packet

Answer
  the worker-filled answer.json inside a bundle

Record
  durable accepted audit memory under tools/semantic-audit/records/*.jsonl
```

Only records are durable memory. Runs, packets, and bundles are generated artifacts.

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

## Human Workflow

The intended workflow is:

```text
run audit
  -> open dashboard
  -> choose packet
  -> create bundle
  -> worker fills answer.json
  -> controller dry-run
  -> controller append
  -> rerun audit
```

The dashboard should expose this as a simple action queue. The manifest and fingerprint machinery
should remain mostly invisible unless something fails validation.
