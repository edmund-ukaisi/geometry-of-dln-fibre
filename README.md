# geometry-of-dln-fibre

Digesting and formalising in Lean the paper *"Geometry of the fibers of the multiplication map of deep
linear neural networks"* (Simon Pepin Lehalleur & Richárd Rimányi, 2024 — arXiv:2411.19920; local copy
in `paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/`).

Three goals:
1. **Understand** the paper, its method, and its results.
2. **Formalise** almost all of its results in Lean 4 + Mathlib.
3. Do so as a **good, reusable Lean library** with clean API design.

The research *process* is a domain-agnostic harness ported from the `ai-research-assistant` programme —
disposition + discipline in [`CLAUDE.md`](CLAUDE.md), and a repeatable instantiation recipe in
[`TEMPLATE.md`](TEMPLATE.md).

## What the paper says

It studies the algebraic set of tuples of composable matrices $A_\ast=(A_1,\dots,A_N)$ that multiply to a
fixed matrix $B$. Reinterpreting a tuple as a representation of the equioriented **type-A quiver** turns the
geometry into finite orbit combinatorics (Gabriel ⟹ orbits ↔ **Kostant partitions** ↔ **rank patterns**).
From this it determines the codimension $C$ and the number $\theta$ of top-dimensional irreducible components
of the fibre — in three forms (a Poincaré series in equivariant cohomology, a quadratic integer program, an
explicit formula) — proves the surprising **permutation invariance** of $(C,\theta)$ in the dimension vector,
and concludes that the real log-canonical threshold of the square-Frobenius loss is $C/2$, so deep linear
networks are "mildly singular." A full map is in
[`docs/expositions/paper-digest/high-level-overview.md`](docs/expositions/paper-digest/high-level-overview.md).

## Layout

```
CLAUDE.md            disposition + working discipline (auto-loaded by Claude)
AGENTS.md            codex entry point + reader-facing exposition workflow
ROADMAP.md           result-map + the Core/DLN formalisation-target ladder
TEMPLATE.md          how to instantiate this harness for a new paper
docs/policies/       how research is done (expedition · claims · review · precision · bedrock · …) + exposition-format trio
docs/expositions/    curated reader-facing digest (paper-digest/)
.claude/skills/      lean-formalisation, local-codex-consult
.claude/agents/      scout, pen-and-paper, lean-formaliser, reviewer
.agent-team/         roles/ (tracked), logs/ (tracked), comms/ (scratch)
lean/                Lean 4 + Mathlib project — lib DLNFibre: Core (engine) + DLN (application); build from here
theory/              markdown theory workspace; setup.md = the Rep_d / mult / quiver substrate
expeditions/         one dir per expedition (brief, priorities, threads, synthesis, lessons)
paper-sources/       the paper + reference papers (Aoyagi)
```

## What it does

Research runs as **expeditions** ([`docs/policies/expedition.md`](docs/policies/expedition.md)): a controller
(team lead) delegates to thread teammates around a central question. Theory develops in markdown; a stable
claim is formalised in Lean and gated on an AUDIT that the Lean statement matches the claim; the result is a
statement card linking claim ↔ Lean. Reader-facing digests live under `docs/expositions/`.

The Lean library is factored **engine vs application**: `DLNFibre.Core.*` is the network-free quiver/orbit/
codimension engine (reusable on its own), and `DLNFibre.DLN.*` is the DLN fibre + loss + RLCT application
that depends on it. `Core` must never import `DLN`.

## Launch an expedition

1. Read the expedition's `brief.md` (central question) and `priorities.md`.
2. As controller (this session), enable Agent Teams and create the team
   (`CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`; cwd = this repo root).
3. Spawn thread teammates (explore / formalisation / infra) per the brief; spawn reviewers to audit.
4. Run the controller tick each turn: recover → ingest → re-anchor → triage → delegate → integrate → surface → review-to-equilibrium.
5. Close: final integration, synthesis pass, commit on the expedition branch, signal-and-wait before any PR.

## Lean

```
cd lean
source ~/.elan/env
lake exe cache get   # first time on a machine — fetches Mathlib oleans
lake build           # or: lake build DLNFibre.<Module>
scripts/sorries      # audit: expect zero
```

First expedition:
[`expeditions/2026-06-12-paper-digest/`](expeditions/2026-06-12-paper-digest/) — produce a
formalisation-ready digest, a Core/DLN target ladder, and a map of what Mathlib already provides.
