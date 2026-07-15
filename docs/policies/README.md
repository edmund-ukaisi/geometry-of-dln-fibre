# Policies

How research is done in this harness — the conventions, sitting upstream of the
skills and code that codify them. Read the relevant policy before the matching
work.

## Research process

- [`principles.md`](principles.md) — P1–P9, the *why* the process shares; other docs cite P-numbers.
- [`expedition.md`](expedition.md) — the multi-agent expedition machine: phases (adjudication → build loop → close), controller tick, offices, thread types and gates, the scaffold, heartbeat, close.
- [`expedition-map.md`](expedition-map.md) — the plan layer (absorbs the former claims policy: kill-conditions are battery scripts, the two-tier discipline is the `tier` field): claims.yaml, ladders, battery, skeleton linkage, contracts, the CLI (`scripts/expedition`; notes: [`expedition-cli-notes.md`](expedition-cli-notes.md)).
- [`worktree-branch-hygiene.md`](worktree-branch-hygiene.md) — branch/worktree naming, origin-is-the-bank, cleanup.
- [`review.md`](review.md) — reviewer functions (fidelity, simplification, claim-soundness, precision, synthesis-coherence, wording) and the object-level wording rule.
- [`precision.md`](precision.md) — name and state a result at exactly what is proven (Proved/Assumed/Cited/Deferred); the completeness corollary.
- [`bedrock.md`](bedrock.md) — the bar above the sorry-gate: building results worth standing on (non-vacuity, hygiene, characterization, fenced interfaces); defeats *conceptual* slop, not just technical; the controller judges against this taste.
- [`codex-consultation.md`](codex-consultation.md) — when and how to consult Codex as the independent second model.
- [`statement-cards.md`](statement-cards.md) — linking a formalised claim to its Lean theorem in markdown.
- [`writing-style.md`](writing-style.md) — the umbrella research-writing discipline: object-level focus + the banned-wording list, elementary build-up, layered detail (footnotes / collapsibles), and the scholium renderer's rendering rules.
- [`draft-policy-semantic-auditing.md`](draft-policy-semantic-auditing.md) — draft, to be discussed: checking that compiled Lean statements, definitions, and APIs match the mathematics the research programme actually needs.

## Reader-facing exposition (formatting + prose)

These three predate the research-process port and govern the **reader-facing expositions** under
`docs/expositions/` (see [`../../AGENTS.md`](../../AGENTS.md) for which to use when):

- [`scholium-writing-format.md`](scholium-writing-format.md) — markdown formatting, frontmatter, collapsibles, theorem-like blocks, math rendering, images, and `.data.yaml` sidecar conventions.
- [`writing-style-graduate-math-textbook.md`](writing-style-graduate-math-textbook.md) — prose style, reader model, proof pacing, examples, theorem restatement, source traceability.
- [`writing-style-agent-exposition.md`](writing-style-agent-exposition.md) — (legacy) agent-work summaries / synthesis notes, not graduate-textbook expositions unless asked.

`writing-style.md` is the umbrella research-writing discipline; the trio above are the detailed
exposition-format references. They are complementary and agree on the scholium specifics; if they ever
diverge, the operator reconciles.

Disposition (the stance all of this runs under) is in [`../../CLAUDE.md`](../../CLAUDE.md).
Lean build conventions are in [`../../lean/CLAUDE.md`](../../lean/CLAUDE.md). The
executable workflows are the skills under [`../../.claude/skills/`](../../.claude/skills/).
