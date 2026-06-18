# synthesis.md - controller integrative read (aoyagi-rlct)

The controller's internal ground. Flush here before compaction, long operations,
and branch/integration decisions.

## Initial read

This expedition treats Aoyagi 2023 as its own formalisation target, independent
of the Lehalleur-Rimanyi quiver proof, quiver notation, and quiver Lean branch.
The one planned cited boundary is the general analytic theorem extracting RLCT
and pole order from a normal-crossing resolution. The expedition should prove
the elementary Aoyagi-specific content unless a probe shows that a step is
genuinely analytic background.

Active worktree:
`/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct`.
If this file is read from another checkout, switch to that worktree before
continuing expedition work.

The current repo process already has good durable memory files, but a paper-sized
Aoyagi run needs two extra ledgers:

- `claims.md`: claim cards with Proved / Assumed / Cited / Deferred and
  kill-conditions.
- `theorem-ledger.md`: source theorem -> local claim -> Lean status -> review
  status.

These ledgers are part of the controller's compaction recovery state.

Additional gate: each substantial Aoyagi calculation needs a pen-and-paper
reproduction, written as a derivation rather than a summary, plus an independent
checker verdict before Lean work treats it as a stable target. This applies to
the block/product reductions, deepest-singular-point probe, blow-up recursion,
arithmetic tail, notation translation, and final assembly.

## Current source picture

Initial PDF reconnaissance gives these page-pinned source clusters. Thread 01
must still verify them against the PDF.

- PDF pp. 5-6: RLCT definition, ideal convention, matrix norm/ideal notation,
  and the cited normal-crossing extraction formula.
- PDF pp. 6-7: Theorem 1, a cited previous three-layer theorem from [12].
- PDF pp. 8-9: Definition 3 and Theorem 2, the multi-layer main theorem and
  final formula. The final target is Theorem 2, not Theorem 1.
- PDF pp. 10-13: Lemma 2 and Theorem 3, the block/product reductions.
- PDF p. 14: Theorem 4, deepest singular point statement; probe before deciding
  whether it is cited or proved.
- PDF pp. 14-23: recursive Case 1 / Case 2 blow-up bookkeeping, terminal
  diagonal ideal, and candidate exponents.
- PDF pp. 24-27: Lemmas 3-5, finite arithmetic minimisation and pole-order
  count.

The source inventory thread must replace this with page-pinned, source-faithful
entries.

## Lean shape hypothesis

Likely modules, subject to source inventory:

- `DLNFibre.DLN.Aoyagi.Basic` or `DLNFibre.DLN.Aoyagi.Notation` for Aoyagi's
  dimension vectors and finite arithmetic.
- `DLNFibre.DLN.Aoyagi.Reduction` for block/product reductions.
- `DLNFibre.DLN.Aoyagi.Blowup` or `...Certificate` for the transition system.
- `DLNFibre.DLN.Aoyagi.Formula` for the final Aoyagi-specific theorem.
- A separate cited analytic interface only if needed, named for the cited
  interface rather than pretending the analytic theorem was proved.

Do not place Aoyagi/DLN application code in `DLNFibre.Core`.

## Lean baseline

Initial scanner run in the Aoyagi worktree: `lean/scripts/sorries` reports
`0 sorry`, `0 #exit`, `0 native_decide`, and `0 axiom`. Full `lake build` has
not yet been run in this expedition.

Analytic-interface caution: PDF p. 5 includes an RLCT ideal-generator comparison
lemma. The user's allowed cited boundary is only the normal-crossing-to-RLCT
extraction theorem, so do not introduce that lemma as a second cited Lean
interface without surfacing it.

## Reproduction status

- A1/A2 block and product reduction: draft reproduction landed at
  `threads/03-block-product-reduction/reproduction-draft.md`; independent
  check landed at `threads/03-block-product-reduction/reproduction-check.md`.
  A1 is checked only for algebraic chart identities/rank formula. A2 is not
  formalisation-ready as stated: it needs explicit neighborhood/rank/open-chart
  hypotheses, a through-layer basis/open-chart lemma, and a decision on hidden
  analytic steps (local coordinate invariance, generator replacement,
  regular-coordinate additivity).
- A3 Theorem 4: xhigh scout reports this is an analytic RLCT comparison theorem
  cited to Aoyagi [22], not proved in the 2023 paper. Because the user allowed
  only the normal-crossing extraction citation in Lean, this is a scope conflict
  unless we can avoid it or prove a restricted homogeneous version.
- A4 blow-up certificate: draft reproduction/certificate design landed at
  `threads/04-blow-up-certificate/reproduction-draft.md`; independent check
  landed at `threads/04-blow-up-certificate/reproduction-check.md`. Verdict:
  blocked, not formalisation-ready. Main blockers are a source-fidelity error
  conflating actual layer widths `M^{(S+1)}` with prefix minima `M(S+1)`,
  missing pivot charts, incomplete invariant recurrence, regularity/divisibility
  of `P`, unstable termination measure, and unchecked boundary cases.
- A5 arithmetic tail: draft reproduction landed at
  `threads/05-arithmetic-tail/reproduction-draft.md`; independent check landed
  at `threads/05-arithmetic-tail/reproduction-check.md`. Verdict: blocked, not
  formalisation-ready. Interior quadratic algebra is promising, but the draft
  drops Aoyagi's `\tilde t_{s,k}=0` terminal-variable restriction, leaves
  Lemma 3 endpoints unresolved, has not proved minimiser feasibility, and does
  not reproduce Lemma 5's chart-family/order-count construction.

## Current next target

The broad A2/A4/A5 targets are blocked by reproduction checks. The only checked
mathematical surface currently suitable for a first Lean tide is the narrow A1
algebraic block-elimination chart identity and rank formula on an explicit
invertible chart. This tide must avoid naming any RLCT/local-germ consequence
and should state only matrix/block algebra under explicit hypotheses.

## Drift guard

- Normal-crossing extraction: Cited.
- Aoyagi-specific block/product/blow-up/arithmetic steps: Prove by default.
- Source summaries are not enough. Reproduce substantial calculations on paper
  and check them carefully before formalising.
- No theorem name may say more than its statement proves.
- Aoyagi's `theta` means pole order / RLCT multiplicity. Use a distinct
  Lean/display name such as `rlctOrder` rather than reusing any existing
  component-count convention.
- Universal or exhaustive case-split claims need decorrelated counterexample
  hunting or a proof of completeness before being treated as established.
