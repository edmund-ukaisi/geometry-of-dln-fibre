# priorities.md - taste ledger (aoyagi-rlct)

The controller proposes this ranking; the operator may edit this file directly.

## Operator standing choice

- The general normal-crossing-to-RLCT extraction theorem is Cited.
- Other Aoyagi-specific steps default to Prove. Do not mark them Cited or
  Deferred without a probe.
- This is an Aoyagi-only expedition. Do not use the quiver paper, quiver Lean
  results, or quiver notation as source evidence or proof input.

## Active workspace

Work from
`/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct`
on branch `expedition/aoyagi-rlct`. If a resumed controller finds itself in the
main checkout, it should move to this worktree before doing expedition work.
Use absolute paths or explicit `workdir` settings for tool calls; do not rely
on the session's original cwd.

## Ranked next

1. Through-layer basis/open-chart lemma for A2. The through-subspace theorem
   and per-edge transported `sumQuot` / direct-sum matrix block forms are
   Lean-proved; prefix-transported through-bases and endpoint total-product
   normal form are Lean-proved; the unitriangular chart-form preservation
   corollary is Lean-proved; supplied local complement data is bundled; and
   finite-dimensional Lean chains now supply finite-indexed chart data and a
   kernel-complement version, with concrete finite-basis edge/unitriangular and
   endpoint block corollaries. The paper-order bridge artifacts `paperChainMap`
   and `chainMap_reverse_eq_paper` are Lean-proved, finite paper-order
   edge/endpoint block wrappers are Lean-proved, and algebraic determinant-chart
   membership for adapted paper edge matrices is Lean-proved; next assemble the
   product-reduction induction from these adapted-coordinate ingredients and
   explicit determinant-unit hypotheses.
2. Product reduction repair beyond the landed chart-local and entry-ideal
   steps. Re-state A2 with source-faithful rank/open-chart hypotheses and keep
   certificate transport separate from the algebraic induction identity now
   proved in Lean.
3. Analytic interface shape after A4 data. Keep A0 extraction-only; do not
   smuggle Aoyagi Lemma 1, Theorem 4, or regular-coordinate additivity as extra
   citations.
4. Source inventory completion. Fill remaining `theorem-ledger.md` source refs
   and exact hypotheses from the PDF where the first scout still left TBDs.
5. Repair A4 blow-up reproduction. Separate actual layer widths from prefix
   minima, redo Case 1/2 updates, cover pivot charts, prove `P`
   regularity/divisibility, and replace the termination measure.
6. Repair A5 arithmetic reproduction. Split Lemma 3 endpoints, preserve
   `\tilde t_{s,k}=0`, prove minimiser feasibility, and reproduce Lemma 5's
   chart-family/order-count construction.
7. DLN notation translation. Translate Aoyagi dimension/rank notation to repo
   DLN notation only after the Aoyagi-side statements are stable.
8. Review/hardener cadence. Gate every broad theorem name, every universal
   case-split/exhaustiveness claim, and the final theorem.

## Parked but live

- Whether Aoyagi's deepest-singular-point theorem is needed as a source result
  or can be reproved in the homogeneous/square-Frobenius setting. Default:
  probe and prove if elementary.
- Whether the source PDF text extraction is reliable enough to serve as line
  references. If not, use page references and quote only short labels.
- Whether a small certified script is useful for the blow-up transition system.
  If useful, build it under the expedition and make Lean the final authority.

## Worktree caution

The repository was inspected while the checkout was on
`expedition/core-quiver-engine` with unrelated dirty/untracked work. The Aoyagi
worktree now exists separately. Use surgical staging inside the Aoyagi worktree;
do not use `git add -A` from the main checkout while unrelated expedition
artifacts are present.
