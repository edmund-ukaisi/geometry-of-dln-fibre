# TEMPLATE — instantiate this harness for a new paper

This repo is a **paper-digestion + Lean-formalisation harness** split into two layers:

- **Layer 1 — the process engine (domain-agnostic; copy it forward).** The disposition, the research-process
  policies, the team roles, the skills, and the Lean hygiene scripts. These encode *how* research runs, not
  *what* paper it is about.
- **Layer 2 — project content (rewrite per paper).** The destination, the roadmap, the theory, the Lean
  library, and the expeditions.

To start a new paper project, copy Layer 1, scrub the worked-examples, and write Layer 2 fresh. The steps:

## 1. Copy the Layer-1 set
From an existing instance (this repo, or the `ai-research-assistant` source):

```
docs/policies/   principles.md  expedition.md  expedition-map.md  expedition-cli-notes.md
                 worktree-branch-hygiene.md  bedrock.md  precision.md  statement-cards.md
                 review.md  writing-style.md  codex-consultation.md
                 draft-policy-semantic-auditing.md  README.md
.agent-team/     README.md  teammate-brief-template.md
                 roles/{controller,scout,pen-and-paper,formaliser,architect,reviewer,cartographer,navigator,elder}.md
                 logs/.gitkeep  comms/.gitkeep
scripts/         expedition  expedition_map/  hooks/pre-commit   (+ tests/ for the CLI)
.claude/skills/  lean-formalisation/SKILL.md   local-codex-consult/SKILL.md
.claude/agents/  scout.md  pen-and-paper.md  lean-formaliser.md  reviewer.md
lean/scripts/    sorries   lean-search
TEMPLATE.md      (this file — itself Layer 1)
```

If your project also wants the reader-facing **exposition-format trio** (`scholium-writing-format.md`,
`writing-style-graduate-math-textbook.md`, `writing-style-agent-exposition.md`), copy those too; they sit
alongside the research-process policies.

## 2. Scrub the worked-examples (Layer 1 carries illustrations, not just rules)
Most Layer-1 files are domain-agnostic; `principles.md` deliberately carries the prior project's
provenance (it is the evidence record — keep or trim at taste), and a handful of others thread *worked examples* from the prior project that must be
recast or neutralized. Run a residual-token grep and recast each hit to your paper's mathematics (prefer a
faithful recast over bland neutralization — the prior project's RLCT/codimension example, e.g., often has a
natural analogue):

```
grep -rniE 'relu|neuroalgebraic|<prior-module-prefix>|<prior worked-example tokens>|<prior remotes>' \
  docs/policies .agent-team .claude theory lean/scripts
```

Files that typically need recasting: `precision.md` (the name-vs-content worked example), `bedrock.md` (the
"what we built" sentence), `expedition.md` (the programme name + a stage-slug or two), `review.md` and
`draft-policy-semantic-auditing.md` (the domain crux-check / dependency examples), the role/agent files (a
hypothesis-tag token, the harness-root + paper-source paths, one or two domain examples).

## 3. Rename the Lean library
- `lean/lean-toolchain`, `lean/lakefile.toml` — set the lib `name`/`defaultTargets`/`[[lean_lib]]` and the
  Mathlib `rev` (matching the source instance's toolchain lets its v4.29-style Mathlib notes transfer).
- Aggregator `lean/<Lib>.lean` + the module tree `lean/<Lib>/...`.
- `lean/scripts/sorries` — update the glob from the old module prefix to `<Lib>/`.
- `lean/CLAUDE.md` — keep the generic sections; **reset** the "Mathlib gotchas" to only the
  toolchain-generic notes (drop the prior project's proof-specific ones — they were a different theory).
- Decide the library factorization up front (here: `Core` engine vs `DLN` application, `Core` never imports
  the application) — bake it into the namespace/dependency structure, but prove at claim-specificity and lift
  to shared API on the *second* use, not in anticipation.

## 4. Write the Layer-2 set fresh
- `CLAUDE.md` — keep the **Disposition** + **Writing discipline** sections verbatim; rewrite **the
  destination**, **how research runs** (paths), **branch discipline** (your remote), **team structure** (same),
  **Memory** (in-repo only), and **pointers**.
- `README.md`, `ROADMAP.md` — orientation + result-map/ladder for your paper.
- `theory/README.md`, `theory/setup.md` — the theory workspace + the core-objects substrate.
- `AGENTS.md` — a pointer to `CLAUDE.md` + (optionally) the reader-facing exposition workflow.
- First expedition `expeditions/<date>-<slug>/` — `brief.md` (central question + closing criterion),
  `priorities.md`, `threads.md`, `synthesis.md`, `lessons.md`, `loop-prompt.md`, `expositions/.gitkeep`.

## 5. git
`git init`; working branch `dev`; add your `origin` remote. Do not push without an explicit instruction
(the operator performs merges and the `dev → master` promotion).

## 6. Verify (the green gate for the scaffold)
- `cd lean && source ~/.elan/env && lake exe cache get && lake build` → green (stubs compile).
- `lean/scripts/sorries` → zero.
- **Residual-token grep** (step 2) → only intentional, recast mentions remain.
- **Link-consistency** → every relative markdown link in `docs/policies/`, `.agent-team/roles/`,
  `.claude/{skills,agents}/` resolves to a file that exists.

That is the whole recipe. The reusable part is Layer 1 + this checklist; everything else is the paper.
