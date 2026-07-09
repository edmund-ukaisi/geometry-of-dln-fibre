# Reference notes — the (S,J) blow-up termination kernel (de-risk asset for the DEFERRED `(□)`-discharge)

**Purpose.** Not on the S2-free milestone path. A pointer to reusable prior work for IF/WHEN the
operator greenlights discharging `(□) = RouteMBoxThresholdFinite (H−r)` (the sole remaining hypothesis
of `aoyagi_learning_coefficient_gen`) via the native `(S,J)` blow-up chart-tree — i.e. making the
general-L *equality* headline unconditional. Point 5 of the close plan defers this; do NOT charge it
without an operator decision. (The unconditional bounds `_gen_le`/`aoyagi_deepest_reduction_gen` +
`_L2` need none of this.)

## Where it lives
`BlowupBranchProgress.lean` — in the `aoyagi-rlct` worktree
(`.claude/worktrees/aoyagi-rlct/lean/DLNFibre/DLN/Aoyagi/BlowupBranchProgress.lean`) and in git history
(commits `e7fc4ed3` "Add combined recurrence branch progress", `68c00f37` "Add Case 1 same-domain
plateau progress"). The `aoyagi-rlct` branch was a reference-only exploration (assumed not
integration-ready); treat this as **notes, not an import**.

## What the kernel PROVES (reusable)
A small **well-founded termination kernel** for the blow-up branch bookkeeping:
- `AoyagiIntroducedLabelBranchState L n` — the branch state: stage `S` (`1 ≤ S ≤ L`) + branch index `J`.
- `support` — the finite `Finset` of labels introduced at a branch state (`introducedLabelFinset L n S J`).
- `remaining L n s := (actualWidthLabelFinset L n).card − s.support.card` — the termination measure
  (# source labels not yet introduced).
- `support_subset_actual` — the introduced support is always ⊆ the finite source-label support.
- `remaining_lt_of_support_ssubset` — **strict support growth strictly decreases `remaining`** (via
  `Finset.card_lt_card`) ⟹ the branch recursion terminates. This is the `(S,J)` double-induction's
  well-foundedness, ready to reuse.

## What it does NOT do (the honest gaps — the real work of a `(□)`-discharge)
Per its own docstring, it does NOT: construct source-production payloads; prove that all **Case 1 /
Case 2** branches satisfy the progress relation; or fill the selected-entry analytic-atlas producer's
branch-termination field. So the kernel is the *scaffolding* (termination measure) — the analytic
content (the per-branch box-finiteness / chart construction that would actually discharge `(□)`)
remains to be built.

## The Case-2 pitfall (flagged, not transcribed)
The `aoyagi-rlct` exploration recorded a **Case-2 printed-mismatch** (the Case-2 branch's produced
chart data not matching the expected printed form) — a known trap when wiring the Case-1/Case-2 branch
dispatch. If the `(□)`-discharge is greenlit, consult the `aoyagi-rlct` branch's Case-2 notes before
re-deriving the branch payloads (the mismatch bit a prior attempt).

## Relation to this expedition's `(□)`
`(□) = RouteMBoxThresholdFinite M` = "∀ c' < ½·minAdm M, the layer-product box integral is finite."
Discharging it natively = building the `(S,J)` blow-up chart-tree whose leaves give that finiteness.
The termination kernel above supplies the recursion's well-foundedness; the seam spec
(`threads/genm-seam/spec.md`, the abandoned option-A route + the banked `gaugeAbsorption` crux on
`origin/genm-seambuild`) + the `RouteMSJResolution` deferred machinery are the other reusable pieces.
See also `cards/theta-analytic-multiplicity-seam.md` for the *other* deferred analytic seam (the θ
multiplicity), which is a different open direction.
