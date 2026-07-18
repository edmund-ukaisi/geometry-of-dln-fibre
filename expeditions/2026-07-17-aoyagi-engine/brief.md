# Expedition: aoyagi-engine — Aoyagi's mechanism as a standalone library; destination = the learning coefficient theorem

**Central question (REFRAMED by operator, 2026-07-18 — this framing has PRIORITY).** Build
**Aoyagi's resolution-of-singularities mechanism (her 2023 DLN paper) FULLY and FAITHFULLY as a
free-standing Lean library** — her objects, her invariants (sharing/support INCLUDED, never
deferred for being off some consumer's path), her construction end-to-end — independent of
downstream consumption. THE DESTINATION IS THE LEARNING COEFFICIENT THEOREM
(`aoyagi_learning_coefficient` unconditional modulo standard nondegeneracy, kernel footprint
`[propext, Classical.choice, Quot.sound]`, no carried or cited Aoyagi hypothesis). Two consumption
paths from the library, priced by the paper-map recon: (A) the hbox adapter —
`RouteMBoxThresholdFinite M` ∀M into the proven `aoyagi_learning_coefficient_gen` assembly
(current default); (B) her native λ-theorem transcribed. PATH QUESTION RESOLVED (council #3,
2026-07-18): Path A ratified as the SOLE critical path — Path B contains Path A's coverage
content and is not shorter; the prize is the UNCONDITIONAL CLEAN-THREE headline (killing the
5 skeleton-rung sorryAx). PRECISION PIN: `cited_aoyagi_dln` was never in the λ cone — it is the
OUT-OF-SCOPE RlctPayoff layer's (needs minAdm=codim; the next expedition's runway). Method
(operator): mathematical sense over case analysis — understand each piece at conceptual altitude,
build the uniform object, DERIVE the cases.

**Closing criterion.** `aoyagi_learning_coefficient` (unsuffixed) proven via `…_gen ∘ hbox`
(L≥2) + the SEPARATE L=1 fold; forced `#print axioms` clean-three with an ENFORCED axiom-gate
installed at the repoint (a #print diagnostic alone is confirmed-by-discipline, not enforced);
the full-mechanism library standing as bedrock (faithful to her paper, not trimmed to the
consumer — R1 faithful carrier, R4 genDivExp propagation, R6 peel per its cost-probe); skeleton
legacy stubs re-pointed; cordon audit clean; close PR at signal-and-wait.

**Why this route (the founding adjudication — full whys in `compass.md`).** The predecessor
expedition's integrate-early engine (RouteM peel-and-integrate) repeatedly manufactured
false-or-over-demanding residual obligations; the terminal one (`det(QQᵀ)^{−a/2}` naked weight) was
proven FALSE on legal cuts (battery: `w-naked-weight-*.py`). Root cause is structural: the target
exponent is exactly tight at binding cells (zero slack), so **any lossy factorization is
automatically false there**. Aoyagi's own proof is exact at every step — coordinate changes and
blow-ups only, integration deferred to monomialized leaves — and her paper works the construction
out completely for the DLN case (verified by direct read + decorrelated seat, 2026-07-17; the
"future research" caveat belongs to the 2013 general-Vandermonde paper, NOT to this construction).
The wall object never forms on this route.

**The four layers** (see `map/claims.yaml`):
A. *Reduction* — Lemma 2 / Theorem 3 block-elimination peel to the reduced chain (mostly banked
   analogues; transcription).
B. *The resolution tree* — the paper's pp.14–22 double induction as a Lean structure; node data
   MUST carry the divisor-support (sharing) maps — flattened invariants provably break
   (battery: `g-coupled-binding-334.py`, `g-delta-flatten.py`).
C. *Coverage* — the ONE genuine reconstruction: the chart family covers, and no untracked chart
   yields a smaller ratio. The paper asserts ("by a blow-up process"); we prove. This is the named
   hard part; it holds a lane from day one.
D. *Thresholds + budget* — monomial reads and the minAdm/QIP arithmetic: banked wholesale.

**Interface contract (non-local invariant).** The engine owes exactly ONE Prop —
`RouteMBoxThresholdFinite (H−r)` (`RouteMBoxReduction.lean:165`) — and nothing else. Everything
above it is proven (`HeadlineGenAssembly`). The worked precedent for the whole pattern is
`RouteMBoxThresholdRR4` (0-sorry end-to-end instance).

**Standing rules (this expedition's additions to policy):**
1. **Exact-steps-only inside the engine.** Every step is an ideal identity, a unit-Jacobian /
   measure-preserving CoV, or a blow-up substitution with tracked monomial Jacobian. No early
   integration; no lossy upper-bound factorization on any path that must reach a binding cell.
2. **Truth witness at pin time.** No obligation is named, built toward, escalated, or cited without
   a smallest-instance satisfiability check in the battery. (Provenance: obligation-2, false for
   ~3 days, caught by a one-line integral.)
3. **Never transcribe the paper's Def-3 inequalities** (verified typo; battery guard) — use the
   geometric `½·min_t Mval(t)` form already banked.

**Non-goals (revised at the reframe).** The order θ remains out UNLESS the paper-map recon shows
her λ theorem needs it (then it enters as HER content, priced honestly). `cited_aoyagi_dln` is no
longer untouchable: path (B) REPLACES it natively — building her theorem is the opposite of
leaning on the cite; `RlctPayoff`/fibre payoff stay out. The predecessor's coupled/residual route
stays superseded (banked bricks consumed as-is where types fit, never rebuilt).

**Boundary with the predecessor.** `expedition/aoyagi-full` runs independently; we NEVER touch its
branches, worktrees, or scaffold. Its tip is merged in at genesis (63b3e8cb0); later banked pieces
arrive only as reviewed merges. Within THIS branch we may restructure Lean freely per our strategy.

**Placement note (controller).** Main checkout is occupied by the predecessor; per
`worktree-branch-hygiene.md` the controller sits in `.claude/worktrees/aoyagi-engine/root`.
Teammate isolation therefore does NOT come from `isolation:"worktree"` (it would collapse onto
root) — the controller creates explicit worktrees per seat:
`git worktree add .claude/worktrees/aoyagi-engine/<seat> expedition/aoyagi-engine--<seat>`.
One-builder-at-a-time in any shared tree.

**Sources.** Paper: `paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/
aoyagi-2023-neural-networks-preprint.pdf` (§5 = the construction; pp.14–22 the recursion; p.22 the
candidates; Lemma 3 p.24; Lemmas 4–5 + Eqs (1)–(5) pp.25–27 the achievers). Week-one reproduction:
`theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex` (+ typo ledger — read it before
transcribing anything). Architecture + reuse certs: `threads/00-genesis/`.
