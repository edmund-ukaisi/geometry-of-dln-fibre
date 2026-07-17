# Expedition: aoyagi-engine — the transform-only resolution engine for (□)

**Central question.** Build Aoyagi's resolution machinery (her 2023 DLN paper, §5) as a standalone
Lean development — the **transform-only engine** — producing `RouteMBoxThresholdFinite M` for every
chain `M`, with kernel footprint `[propext, Classical.choice, Quot.sound]` and **no carried or cited
Aoyagi hypothesis anywhere in (□)**; then re-point the mint so `aoyagi_learning_coefficient` stands
unconditional modulo standard nondegeneracy hypotheses only.

**Closing criterion.** `aoyagi_learning_coefficient` (unsuffixed) proven via
`aoyagi_learning_coefficient_gen ∘ (the engine's ∀-M hbox)` + the L=1 endpoint fold; forced
`#print axioms` clean-three; skeleton legacy stubs re-pointed at their proven twins; cordon audit
clean; close PR at signal-and-wait.

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

**Non-goals.** The order θ (meromorphic-continuation seam — separate, flagged); `cited_aoyagi_dln`
/ `RlctPayoff` (untouched; separate operator decision); the predecessor's coupled/residual route
(superseded — its banked bricks are consumed as-is where types fit, never rebuilt).

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
