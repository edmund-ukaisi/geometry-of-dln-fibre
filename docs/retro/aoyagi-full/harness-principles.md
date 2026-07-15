# Harness principles (distilled 2026-07-15 from the aoyagi-full retro)

Durable design principles for multi-agent research expeditions — Lean formalization of known proofs,
large Lean library building, and open research mathematics alike. Each principle carries its
provenance in this expedition's record. Implementations live in
[`expedition-map-design.md`](expedition-map-design.md), the `.agent-team/roles/` drafts, and the
policy proposals; this file is the *why* they share.

## P1 — Match binding strength to knowledge half-life

Knowledge in a multi-agent system is stored at four binding strengths: **types** (checked at every
use), **tests/witnesses** (checked at gates), **indexes** (checked if consulted), **prose** (checked
only if read *and recognized*). Turnover — fresh agents, compaction — destroys the attention-bound
strata on a timescale of days; the system's effective long-term memory is types and tests, full
stop. Therefore: **decisions as types (skeleton), refutations as executable witnesses (battery),
frontier as typed holes, prose only for what is allowed to fade.**
*Provenance:* the June-25 route adjudication ("coupled is the route; decoupled provably breaks at
corank ≥ 2") stored as prose, lapsed, and was re-litigated five times in the endgame; meanwhile the
strongest store (the Lean tree) faithfully preserved a *wrong* decision (the false bridge) whose
pull misled a recon. Corollary: honesty obligations concentrate at the strongest stratum.

## P2 — Capability is convened, not possessed

Agent depth is real but per-instance and stateless: fully expressed when convened with the right
frame and context on a sharp question; absent at joints where nobody is convened as a
mathematician. There is no persistent professor; all of the professor's function must be
externalized into artifacts. "Local incentives" names the composition defect, not an instance
defect — the fix is not reward reform but **convening depth at the joints** (gates, seats,
adjudications are convening devices) and **binding depth once expressed** (P1) so it never needs
re-convening. The alternative to a gate is not trust; it is an unconvened moment.
*Provenance:* all five endgame forks were adopted at unconvened moments (route memos between
builds); every catch came from a convened one (t2adjud, thresholdhunt, bltj, the operator's seats,
routeverify). incidencepp proved the "wall" in one night when finally convened on it.

## P3 — Claims travel; understanding doesn't

Every handoff (cert → memo → brief → build) serializes conclusions and strips their support, and
paraphrase drift at consumption edges runs *toward what the consumer needs the claim to say*. Only
two serializations preserve binding without the reader reconstructing the why: types and tests.
Hence: anchor-pins (verbatim statements, never re-typed prose) at every consumption edge; the
composition skeleton elaborated before adoption; executable kill-conditions on claims.
*Provenance:* five forks, five different well-intentioned authors, one shape — a verified object
whose *sufficiency* was an unverified paraphrase ("mechanical", "2 fills", "exposes decLoss",
"gated by hpiv"). Reviews verified objects (which don't travel) and never fits (which do).

## P4 — Intuition is cheap; elaboration is the product

Deep hunches ("this is secretly simple", "this frame makes the moving locus fixed") are abundant,
genuinely valuable, and the raw material of both the wins and the forks — the difference is
entirely downstream treatment. Never dismiss, never adopt: **seat it** (decorrelated elaboration
under adversarial instruction, exact witnesses, bounded time). The harness quality metric: the
cost of elaborating a hunch to a verdict. Everything else (seats, battery, gates) is machinery for
making that cost low.
*Provenance:* the retro side's adapted-frame coordinatization (same cognitive species as cruxfin's
"MAJOR SIMPLIFICATION") was seated rather than adopted; its pointwise-in-z flaw surfaced in hours
instead of becoming fork six.

## P5 — The record is the reward model

Future agents learn what good looks like from the ledger's celebrations; the corpus is the
operative incentive structure for LLM agents. Celebrating confident bypass-headlines trains
bypass-production; celebrating verified fits, honest retractions, and elaborated hunches trains
those. The writing policy's ban on the selling register is training-data hygiene for the system's
own future selves — and any "suffices / bypasses / just wiring / mechanical" sentence in a route
document is a checkable obligation (point at a compiled witness or battery pass), not a style nit.
*Provenance:* the fork vocabulary and the banned vocabulary coincide exactly; ★-celebration
analysis in facet-incentives (credit exclusively for named-target closures).

## P6 — Pull is architecture, not exhortation

The only pull that survives turnover is a named, typed hole wired to a consumer; dispositions
("attack the hard part") do not. Paid-by-the-brick is not the enemy — it is an engine bolted to
whatever frame the skeleton provides. Therefore: **a settled fork becomes skeleton immediately
(promotion lag ≈ zero)** — the driver + obligation-record pattern at fork granularity (churn-robust;
statement detail free to move underneath); a wrong skeleton is worse than none (pull is strong and
neutral), so skeleton revisions are rare, loud, gated events priced by the old fork's witnesses,
and refuted map nodes retire their holes mechanically.
*Provenance:* the endgame went well exactly where a faithful skeleton existed (the (d)-dispatch,
the mint prestage) and badly where the spine had no hole (the crux, prose-targeted for days) or a
wrong one (the false bridge, followed by capstonerecon). The three-week gap between the June
adjudication and any skeleton is the single most expensive absence in the record.

## P7 — The map is gestalt, not citation

(Recorded in full in [`expedition-map-design.md`](expedition-map-design.md).) Read the map to
decide what matters; read the territory to decide what is true. Decision-load-bearing cells are
re-verified against the territory at decision time — cheap, because the map converts verification
from search to lookup — together with their ripples.

## P8 — Waste-fear points backwards at the domain level

Route-glue dies with routes; domain-general machinery survives them (measured: survival ⇔
domain-generality, almost perfectly). Fund the toolkit the source's proof-moves dictate as a
parallel library lane — skeleton holes name their tools, so the lane always has a proven consumer,
dissolving the scope-creep objection. Treat "Mathlib-worthy" as an immediate integration
obligation (canonical, never a side branch), not an aside.
*Provenance:* the one-night incidence-chart build (feasibility); #112 parked on a worktree branch,
lost, rebuilt (the cost of narrow treatment); Brick F as the honest cap (general machinery built
into a Mathlib gap, droppable from the cone — build the *dictated* toolkit, not every generality).

## Scope note

P1/P2/P3/P4/P5 are substrate-independent (they apply to open research questions with no kernel:
witnesses become exact-arithmetic scripts, the skeleton becomes the map's decomposition under its
contracts — the plan must live in a medium at least as strong as the work). P6/P8 assume some
formal or executable substrate. For open problems the adjudication phase never ends: forks settle
progressively and the skeleton ratchets, one settled fork at a time.
