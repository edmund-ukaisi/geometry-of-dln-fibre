---
title: "Semantic Audit CI Roadmap"
status: draft
source: original
topics: [infrastructure, semantic-audit, lean, ci, dashboard]
created: "2026-06-13"
updated: "2026-06-14"
---

# Semantic Audit CI Roadmap

This document sketches an infrastructure roadmap for turning semantic auditing into a CI-style
pipeline for the Lean formalisation.

The short artifact contract for the implemented pipeline lives in
[`semantic-audit-architecture.md`](semantic-audit-architecture.md). Keep that note authoritative for
current artifact responsibilities; this roadmap is for longer-term direction.

The goal is not to replace mathematical judgement. The goal is to spend AI attention at scale on
the parts of review that are abundant, parallel, and reusable: reconstructing what Lean declarations
actually say, comparing that reconstruction against paper/source intent, probing boundary cases, and
turning recurring semantic failures into durable regression checks.

## Guiding Separation

Semantic CI starts only after a technical attestation gate has passed.

```text
technical attestation
  -> lake build succeeds
  -> no sorry/admit/#exit/native_decide policy failures
  -> axiom policy is clean
  -> tracked/imported module set is known
  -> immutable snapshot recorded

semantic audit CI
  -> assumes the Lean artifact is technically valid
  -> asks whether it means the intended mathematics
```

The technical gate and the semantic audit gate should be separate pipelines. The semantic audit
should not spend intelligent attention rediscovering whether Lean compiled; it should begin from a
green, named snapshot.

## Canonical Artifacts

Use JSON/JSONL as the canonical data layer and HTML as the human interface.

Markdown summaries are not required as a primary artifact if the dashboard is good. YAML is also not
needed unless we later choose to maintain a small hand-authored config file. Human-facing review,
triage, and visualization should happen in HTML over structured data.

Proposed run layout:

```text
.semantic-audit/
  runs/<run-id>/
    audit-run.json
    technical-attestation.json
    declarations.jsonl
    modules.jsonl
    semantic-graph.json
    audit-config.resolved.json
    lean-reconstructions.jsonl
    source-intentions.jsonl
    comparisons.jsonl
    work-packets.jsonl
    coverage-summary.json
    findings.jsonl
    regression-results.jsonl
    dashboard/
      index.html
      assets/...
```

The run directory should be generated. We can decide later which outputs are committed and which are
ignored. The schema should be stable enough that reports, dashboards, and future CI jobs can consume
old runs.

## Pipeline Shape

The intended pipeline is staged.

```text
0. technical attestation
1. Lean declaration extraction
2. semantic graph construction
3. work-packet generation
4. independent Lean reconstruction
5. independent source/intention reconstruction
6. comparison and skeptic passes
7. finding normalization and triage
8. regression-rule generation
9. HTML dashboard/report
```

Each stage should produce an artifact that can be inspected independently. Later stages may fail or
be incomplete without invalidating earlier extracted facts.

## Extraction Strategy

The extraction layer should be Lean-native where correctness matters.

Use Lean/Lake to load the compiled environment and extract:

- declaration names;
- declaration kind;
- elaborated type/signature;
- theorem proof or definition value dependencies;
- module of origin;
- docstring;
- source declaration range;
- generated auxiliary constants where useful;
- direct type dependencies versus proof/value dependencies.

Useful existing tools and APIs:

- Lean `Environment` and `ConstantInfo`;
- `Expr.getUsedConstants`;
- `findDocString?`;
- `findDeclarationRanges?`;
- `import-graph`, already available through mathlib, for module import graphs and import analysis;
- small Lean executables run through `lake env lean --run` for project-specific extraction.

Source scanning remains useful, but only as an auxiliary layer:

- import-line scanning;
- source mentions;
- docstring mentions;
- stale prose keyword scans;
- file tracking and aggregator coverage.

Source scanning should never be the authority for a Lean declaration's type or proof dependency.

## Independent Semantic Projections

The system should not generate one statement card directly from the intended exposition. Instead it
should generate independent projections and compare them.

```text
Lean reconstruction
  What the Lean declaration actually says, reconstructed bottom-up.

Source/intention reconstruction
  What the paper, exposition, or research programme appears to want.

Alignment comparison
  Whether the Lean reconstruction matches the intended statement.
```

The decorrelation rule is load-bearing: a Lean reconstruction worker should see the Lean signature,
local definitions, dependency cards, and policies, but not the campaign synthesis or intended-source
card. A source/intention worker should read the paper or exposition and describe the mathematical
target without being steered by the current Lean statement. The comparator then aligns the two.

Existing human-authored cards and prose should be audited as a third projection, not treated as
ground truth.

## Work Packets

The pipeline should generate small work packets so many agents can work in parallel.

Packet kinds:

- `lean_reconstruction`: reconstruct the exact mathematical content of one declaration or cluster;
- `source_intention`: reconstruct the intended theorem/definition from paper or exposition;
- `comparison`: compare a Lean reconstruction with a source/intention card;
- `skeptic`: attack a declaration/card for vacuity, overclaim, wrong object, or accidental convention;
- `api_boundary`: compare a Lean API's admitted objects against the paper's mathematical domain;
- `regression_probe`: test whether a known semantic failure mode appears again.

Audit workers should not edit the main codebase. They return structured JSON findings and, where
appropriate, suggested Lean probes. If a probe must be checked, run it in an isolated worktree or
scratch file importing the relevant module.

## Finding Lifecycle

Raw agent notes are not tasks. They become tasks only after normalization and triage.

Suggested lifecycle:

```text
new
  -> accepted
  -> fixed
  -> regression-added

new
  -> rejected

new
  -> waived
```

Each finding should record:

- declaration or source target;
- finding kind;
- severity;
- evidence with file/range or source artifact;
- reconstructed Lean reality;
- intended mathematical claim, when applicable;
- recommended action;
- whether the issue is conservative, misleading, unsound, stale, or only exploratory;
- possible regression rule.

Severity labels should match the semantic-audit policy:

- `blocker`: downstream work may rest on the wrong statement;
- `high`: prose/name/card likely overclaims Lean content;
- `medium`: useful formalisation but meaningful mismatch or missing bridge;
- `low`: stale wording, minor card drift, or local cleanup.

## Dashboard

The dashboard is the human-facing product.

Initial views:

- run attestation and dirty/tracked/untracked state;
- module heatmap by severity and audit coverage;
- declaration table with filters by module, kind, tier, trust surface, and finding severity;
- declaration detail view with source, type, docstring, dependencies, reverse dependencies,
  reconstructions, comparisons, findings, and examples/non-examples;
- dependency graph view, including target-theorem closures;
- paper theorem to Lean declaration alignment table;
- API-boundary warnings;
- non-vacuity witness coverage;
- finding lifecycle board.

The dashboard should make action obvious: what to fix, what to waive, what to probe, and what has
become a regression rule.

## Regression Suite

Every recurring semantic failure mode should become a standing check where possible.

Deterministic checks:

- tracked Lean files versus module imports;
- files that build when targeted but are absent from the public aggregator;
- declaration existence for carded Lean names;
- stale prose keywords such as `deferred`, `remaining`, or `future` near declarations whose successor
  exists;
- public docstrings using strong words such as `complete`, `classification`, `equiv`, or `iff` without
  corresponding nearby declarations or waivers;
- T0 declarations missing a reconstruction/comparison record;
- T0 predicates missing a non-vacuity witness or waiver;
- declarations with high reverse-dependency count but no semantic card.

Agentic checks:

- name-versus-content mismatch;
- too-general or too-specific API boundary;
- paper/source theorem mismatch;
- vacuity and boundary-case pressure;
- source typo propagation;
- definitional packaging presented as mathematical content.

The system should distinguish deterministic failure from agentic suspicion. A deterministic failure
can fail CI directly. An agentic suspicion should create a finding for triage unless it is part of a
human-approved gate.

## Initial DLNFibre Failure Modes

The first regression/query library should include failure modes already seen in this repo:

- a Lean file builds when targeted but is untracked or not imported by `DLNFibre.lean`;
- stale Lean prose says a construction is deferred after a successor file has landed;
- docstrings advertise complete invariants or equivalences before the corresponding theorem exists;
- `Supported` arrays are broader than the paper's triangular rank patterns;
- interval-like APIs admit arbitrary endpoints where the paper object requires `i <= j`;
- prose says irreducible components are indexed by minimal objects when the order convention requires
  maximal objects;
- source-paper typo or convention conflicts are copied without a comparison record;
- a closure/rank inequality is encoded as a set definition but described as a proved closure theorem.

These are not necessarily all bugs. They are semantic audit queries: each should produce either a
finding, a waiver, or a regression test.

## Build Phases

### Current Full-Loop MVP

The current tool has implemented the first closed deterministic loop:

- `tools/semantic-audit/audit-config.json` assigns a seed T0 set and declares paper/source,
  comparison, and API-boundary targets.
- `tools/semantic-audit/records/*.jsonl` stores answered reconstruction, source-intention, and
  comparison records.
- `semantic_audit.py run` emits resolved config, normalized records, generated work packets, coverage
  summary data, findings, and a static dashboard with tier, coverage, packet, and source-target views.
- The runner still does not call agents. Humans or subagents answer packets by adding structured
  JSONL records, then rerunning the deterministic pipeline.

### Phase 0: Bootstrap The Substrate

Create the first project-native audit substrate:

- project prefix `DLNFibre`;
- public aggregator `DLNFibre.lean`;
- output directory `.semantic-audit/`;
- JSON/JSONL artifacts;
- exact Lean dependency extraction;
- module and declaration graph output.

### Phase 1: Technical Attestation And Inventory

Build a first runner that emits:

- `technical-attestation.json`;
- `modules.jsonl`;
- `declarations.jsonl`;
- `semantic-graph.json`;
- basic deterministic findings for untracked/unimported files and missing declaration coverage.

This phase should not require agent calls.

### Phase 2: HTML Dashboard MVP

Build a static dashboard over the JSON artifacts:

- declaration table;
- module table;
- finding table;
- target declaration dependency view;
- source links into local files.

The dashboard can start simple. Its job is to make structured findings readable and actionable.

### Phase 3: Reconstruction Packets

Generate work packets for T0/T1 declarations and accept structured agent responses:

- Lean reconstruction records;
- uncertainty notes;
- suggested examples/non-examples;
- suggested comparison targets.

At this phase, humans or local subagents can execute packets manually. The important part is the
schema and decorrelation discipline.

### Phase 4: Source Alignment

Add paper/exposition source-intention packets and comparison packets:

- paper theorem/definition extraction;
- source-intention records;
- Lean-versus-source alignment records;
- finding generation for mismatches.

This phase is where theorem-numbering, closure-order, and paper-typo issues become first-class.

### Phase 5: Regression Library

Promote repeated findings into checks:

- deterministic rules in code;
- agentic standing queries;
- waiver records;
- dashboard views showing regression coverage.

The goal is compounding memory: once a semantic bug class is found, future runs should keep looking
for it.

### Phase 6: Incremental And Cached Audits

Add cache keys and invalidation:

- declaration hash from normalized type, value/proof dependency set, docstring hash, and source range;
- dependency graph propagation;
- changed-declaration work queues;
- target theorem blast-radius reports.

This is the phase where semantic audit cost should track semantic change, not repository size.

## Open Design Decisions

- Should audit artifacts live in `.semantic-audit/` as ignored generated outputs, or should selected
  run artifacts be committed?
- Should the HTML dashboard be fully static, or should it include a small local server for filtering
  and lifecycle updates?
- Should accepted waivers be edited in JSON through the dashboard, or kept in a small hand-authored
  config file?
- Should semantic audit workers be allowed to add Lean witness/probe files directly, or should they
  only propose probes for a formaliser/controller to commit?
- Should `doc-gen4` be integrated as a source-link/documentation layer, or should we keep a thin
  Lean-native extractor plus custom dashboard?

## First Concrete Tasks

1. Create a minimal `.semantic-audit/` schema and run metadata format.
2. Build a Lean dependency extractor for `DLNFibre`.
3. Add a declaration extractor that emits JSONL from the Lean environment.
4. Add deterministic module/file coverage checks.
5. Generate a simple dashboard from the extracted JSON.
6. Create the first T0 declaration packet format and run a manual reconstruction pass.
7. Add comparison packets for the paper's rank-pattern and orbit-closure statements.
8. Promote the first accepted semantic findings into regression rules.
