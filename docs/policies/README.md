# Policies

How research is done in this harness — the conventions, sitting upstream of the
skills and code that codify them. Read the relevant policy before the matching
work.

## Research process

- [`expedition.md`](expedition.md) — the multi-agent expedition machine (controller / threads / reviewers / operator), thread types and gates, synthesis, close.
- [`claims.md`](claims.md) — what a claim is, the kill-condition discipline, the new-vs-established two-tier rule.
- [`review.md`](review.md) — reviewer functions (fidelity, simplification, claim-soundness, precision, synthesis-coherence, wording) and the object-level wording rule.
- [`precision.md`](precision.md) — name and state a result at exactly what is proven (Proved/Assumed/Cited/Deferred); the completeness corollary.
- [`bedrock.md`](bedrock.md) — the bar above the sorry-gate: building results worth standing on (non-vacuity, hygiene, characterization, fenced interfaces); defeats *conceptual* slop, not just technical; the controller judges against this taste.
- [`library-building.md`](library-building.md) — when to build a well-established-maths library vs cite a monument (the build-vs-cite test), Mathlib-grade API discipline, foundation-first execution, and the extraction trigger.
- [`lean-build-workflow.md`](lean-build-workflow.md) — running `lake` across many worktrees/sessions: the shared rev-keyed dependency store, the `scripts/lb` wrapper, and the global build-concurrency cap.
- [`codex-consultation.md`](codex-consultation.md) — when and how to consult Codex as the independent second model.
- [`statement-cards.md`](statement-cards.md) — linking a formalised claim to its Lean theorem in markdown.
- [`citation-cordon.md`](citation-cordon.md) — the machine-enforced, forget-proof Proved-vs-Cited invariant: `@[cited]` axioms in located `…Cited.lean` files, `collectAxioms − foundational − @[cited] = ∅` as the `scripts/cited` gate, `#audit_cited` in-file, the adversarial fixtures.
- [`writing-style.md`](writing-style.md) — the umbrella research-writing discipline: object-level focus + the banned-wording list, elementary build-up, layered detail (footnotes / collapsibles), and the scholium renderer's rendering rules.
- [`draft-policy-semantic-auditing.md`](draft-policy-semantic-auditing.md) — draft, to be discussed: checking that compiled Lean statements, definitions, and APIs match the mathematics the research programme actually needs.

## Reader-facing exposition (formatting + prose)

These three predate the research-process port and govern the **reader-facing expositions** under
`docs/expositions/` (see [`../../AGENTS.md`](../../AGENTS.md) for which to use when):

- [`scholium-writing-format.md`](scholium-writing-format.md) — markdown formatting, frontmatter, collapsibles, theorem-like blocks, math rendering, images, and `.data.yaml` sidecar conventions.
- [`writing-style-graduate-math-textbook.md`](writing-style-graduate-math-textbook.md) — prose style, reader model, proof pacing, examples, theorem restatement, source traceability.
- [`writing-style-agent-exposition.md`](writing-style-agent-exposition.md) — stub/alias of [`writing-style.md`](writing-style.md) (its content was consolidated there); kept so existing links resolve.

`writing-style.md` is the umbrella research-writing discipline; the first two above are the detailed
exposition-format references (the third is now a stub/alias of `writing-style.md`). They are complementary
and agree on the scholium specifics; if they ever diverge, the operator reconciles.

Disposition (the stance all of this runs under) is in [`../../CLAUDE.md`](../../CLAUDE.md).
Lean build conventions are in [`../../lean/CLAUDE.md`](../../lean/CLAUDE.md). The
executable workflows are the skills under [`../../.claude/skills/`](../../.claude/skills/).
