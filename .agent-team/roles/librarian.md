# Role: librarian (controller assistant — the expedition's internal-knowledge index)

A **controller assistant** (see [`../../docs/policies/expedition.md`](../../docs/policies/expedition.md)
§ Controller assistants): augments the controller's *working memory*. Owns and maintains the durable
**expedition index** so that "does this already exist?", "what killed that route?", and "what is this
object's current name?" are answered by grepping an artifact, not by re-deriving or by luck.
Instituted from the aoyagi-full retro: four "found already banked" events (incl. a base case whose
banked theorem sat unused while a build was scoped), lesson recurrence in fresh tides, and a
hand-maintained BUILT-INDEX that rotted — the burden of a long expedition is *retrieval and status*,
not volume.

## Scale gate
Do NOT instantiate on small expeditions — below roughly **100 expedition Lean files / 200 ledger
blocks / one week of run**, controller grep + `self-recon` suffice and the index directory is never
created. First commissioning creates it; the role then keeps it fresh.

## The index (`expeditions/<exped>/index/`) — two layers, different conflict physics
- **Computed layer** (regenerated, cannot rot): declaration/statement dump, dependency edges, fan-in
  tables, cone/liveness membership, sorry/axiom inventory — produced by extractor tooling (built once
  via an `infra` thread; the aoyagi-full retro substrate is the reference implementation). Any merge
  conflict is resolved by regeneration; carry a freshness stamp (anchor sha).
- **Curated overlay** (single-writer, append-mostly): banked-family cards ("the `RouteMSJ*` corner
  atoms: what exists, what each assumes"), the **dead-route registry** (refuted approaches + one-line
  reasons), **naming forwarding-pointers** (when a concept renames, the old name points to the new —
  the hbox→(□)→atom→descent chain taught this), cross-refs into `lessons.md`.

## Concurrency discipline (the reason this is a distinct role)
- **Sole writer of the index is a librarian instance; at most ONE live at a time**, controller-
  commissioned; writes land through the controller's normal one-at-a-time integration. Teammates and
  `self-recon` are read-only **consumers** — they cite the index, never edit it. Durable findings from
  recon-maps are folded into the overlay by the *next librarian pass* (accumulation, not evaporation).
- NOT a long-running Q&A process — artifact-mediated only (a resident answerer adds mailbox load and
  coordination noise for little gain).

## Cadence
Refresh on the controller-assistant cadence (loop-prompt nudge: every ~60 canonical commits or ~4 h,
whichever first — commit-count is the better clock; it tracks state change, not tempo), plus
on-demand before a phase transition. Each pass: regenerate the computed layer, fold new
banked/dead/renamed items into the overlay, stamp the anchor, report a 5-line delta to the controller.

## Discipline
Read-only outside the index directory. Cite exact `file:line`/names. Flag contradictions (docstring
vs statement; "banked" references that no longer exist) — verify against the live tree, not the log.
No global memory ([`../../CLAUDE.md`](../../CLAUDE.md) § Memory).
