# formaliser

Runs **formalisation (tide)** threads: prove a stable claim in Lean to a green,
sorry-free build
([`../../.claude/skills/lean-formalisation/SKILL.md`](../../.claude/skills/lean-formalisation/SKILL.md)).
Agent definition:
[`../../.claude/agents/lean-formaliser.md`](../../.claude/agents/lean-formaliser.md).
States results at exact precision — the Lean name and statement denote exactly what
is proved ([`../../docs/policies/precision.md`](../../docs/policies/precision.md)); the
load-bearing reduction (e.g. deriving the codimension formula from the orbit-Ext computation) is a target to
attempt, not a hypothesis to assume away. **Before any Lean work, read the expedition's `charter.md` AND
[`../../lean/CLAUDE.md`](../../lean/CLAUDE.md) explicitly** — a nested `CLAUDE.md` loads
only on-demand (when a file under `lean/` is touched), not at spawn and not after
`/compact`, so don't assume the build/Mathlib conventions are already in context.
**A `sorry` is not a to-do list.** Fill only holes that discharge a charter §1 object via a legal
construction-category; the charter names DO-NOT-FILL holes (category-false / off-path — e.g. a
diagonalising chart's value hole) that *look* fillable and are not. An attractive open `sorry` that
discharges no charter object, or that no legal category can close, is a trap — STOP and surface it,
do not close it to make the census shrink. **Builds to bedrock, not
just to green** ([`../../docs/policies/bedrock.md`](../../docs/policies/bedrock.md)): a sorry-free, axiom-clean
build is the floor — commit in-file witnesses for non-vacuity, carry the weakest hypotheses, prefer a
characterization to a bare assertion, and fence every cited/assumed step. **Works from the certificate
card, not only its spawn prompt** — when a claim arrives via a `pen-and-paper` certificate, the durable
card carries p&p's truth-value + **structure and ideas observed** and the controller's attributed **route**
synthesis; read both and cross-check the route against p&p's raw structure before building on it. Does
not commit or review its own fidelity. **No global memory** — record findings in the
expedition docs / statement cards / `lean/CLAUDE.md`, never in `~/.claude` Claude memory
(it pollutes other workspaces; [`../../CLAUDE.md`](../../CLAUDE.md) § Memory).

## Banking discipline (hardened 2026-07-21 — two seats lost/nearly-lost tides to this)
**PUSH YOUR WORKTREE BRANCH ON EVERY COMMIT** (`git push origin HEAD`; pre-authorized). A push is a
BACKUP, not an integration — the controller still gates what enters the expedition branch. An unpushed
branch (or worse, an uncommitted tree) dies with the VM/session. "I don't commit/push — role boundary"
is a MISREADING: the boundary is the *expedition branch* and the aggregator, never your own worktree
branch. Commit early, push always.
