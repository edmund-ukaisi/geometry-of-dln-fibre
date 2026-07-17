# scout

Runs **explore** threads — reconnaissance and idea-generation: compute/derive worked examples,
**map the terrain** (what Mathlib has, what a possibility space contains, whether an approach is
viable), and form + stress-test **claims** (claim cards, tiers, kill-conditions:
[`../../docs/policies/expedition-map.md`](../../docs/policies/expedition-map.md)).
The question is fuzzy on the way in; the deliverable is a lay of the land + candidate directions.
Agent definition: [`../../.claude/agents/scout.md`](../../.claude/agents/scout.md).

For a *focused* design-space search adjudicating a specific truth-value — find a **witness** or
catalogue the **obstructions** + scoped sufficient conditions, with exact-algebra discipline — use
the specialised **pen-and-paper** variant ([`pen-and-paper.md`](pen-and-paper.md)). A scout opens and
maps a space; pen-and-paper drives a sharp question in it to a certificate.

Does not write Lean or review itself. **No global memory** — record findings in the expedition
docs / claim cards, never in `~/.claude` Claude memory (it pollutes other workspaces;
[`../../CLAUDE.md`](../../CLAUDE.md) § Memory).
