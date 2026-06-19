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
`0 sorry`, `0 #exit`, `0 native_decide`, and `0 axiom`. After the first A1 Lean
tide, controller verified `lake build DLNFibre.DLN.Aoyagi.BlockElimination`,
`lake build DLNFibre`, and `scripts/sorries`; the full build succeeds with only
pre-existing Core linter/style warnings, and the scanner remains at
`0 sorry`, `0 #exit`, `0 native_decide`, and `0 axiom`.

Analytic-interface caution: PDF p. 5 includes an RLCT ideal-generator comparison
lemma. The user's allowed cited boundary is only the normal-crossing-to-RLCT
extraction theorem, so do not introduce that lemma as a second cited Lean
interface without surfacing it.

## Reproduction status

- A1/A2 block and product reduction: draft reproduction landed at
  `threads/03-block-product-reduction/reproduction-draft.md`; independent
  check landed at `threads/03-block-product-reduction/reproduction-check.md`.
  A1 algebraic block identities are now proved in Lean as
  `schurComplement_leftBlockElim_fromBlocks` and
  `schurComplement_blockElim_fromBlocks` in
  `lean/DLNFibre/DLN/Aoyagi/BlockElimination.lean`, over `[CommRing K]` with
  explicit chart hypothesis `IsUnit A1.det`. The A1 rank formula is now proved
  as `rank_fromBlocks_eq_card_add_rank_schurComplement_of_isUnit_det`, using
  the reusable block-diagonal theorem `rank_fromBlocks_zero_zero`. The A2
  chart-local algebraic induction step is now proved in Lean as
  `productReduction_chartLocalInductionStep_fromBlocks` in
  `lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`, with xhigh hardener and
  fidelity-review passes at that narrow scope. Full Aoyagi Theorem 3 is still
  not formalisation-ready as stated: it needs explicit
  neighborhood/rank/open-chart hypotheses, a through-layer basis/open-chart
  lemma, and a decision on hidden analytic steps (local coordinate invariance,
  generator replacement, regular-coordinate additivity).
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

The A1 algebraic core and the A2 chart-local induction step are Lean-proved, but
the broad A2/A4/A5 targets remain blocked by reproduction checks. The first
elementary A2 transport layer is now Lean-proved in `EntryIdeal.lean`:
determinant-unit left/right multiplication preserves matrix-entry ideals,
product entries lie in the ideal generated by factor entries, and `D - F3 F2`
is interchangeable with `D` inside the four-family entry ideal. This remains
algebraic only. The analytic-interface repair says A0 stays extraction-only;
regular variables must be included in a full normal-crossing certificate so the
post-Theorem-3 `c/2` shift is finite certificate arithmetic, not a second
citation.

Through-layer basis repair: xhigh reproduction/check says product rank `r` is
enough to choose through-layer bases existentially so true layer maps have
block form `[I B; 0 D]` and induction charts contain the base point. Product
rank is not enough for a fixed preselected chart; counterexamples are recorded
in `threads/03-block-product-reduction/through-layer-basis-reproduction.md`.
The elementary through-subspace layer is Lean-proved as
`exists_chain_throughSubspaces` in
`lean/DLNFibre/DLN/Aoyagi/ThroughLayerBasis.lean`, using source-to-target
indexing opposite to Aoyagi's prose order. It constructs subspaces through the
chain, proves edge transport and adjacent restricted-edge equivalences, and
identifies the last subspace with the range of the total composite.

The per-edge matrix block form is now Lean-proved in
`lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`: in transported
`Module.Basis.sumQuot` bases,
`exists_toMatrix_throughSubspaceEdge_eq_fromBlocks_one_zero` gives each edge
matrix form `[I B; 0 D]`; in complement/direct-sum adapted bases,
`exists_toMatrix_throughSubspaceEdge_basisOfIsCompl_eq_fromBlocks_one_zero`
gives the same form using `basisOfIsCompl`. This is basis-coordinate
bookkeeping only. It uses explicit through-subspace bases plus quotient or
complement bases as inputs, and it is not a fixed-coordinate chart theorem.
The stronger per-edge variant
`exists_toMatrix_throughSubspaceEdge_prefix_basisOfIsCompl_eq_fromBlocks_one_zero`
uses `throughSubspacePrefixEquiv` to transport one initial basis of `U₀` to
both adjacent through-subspaces, so the top bases are compatible across the
chain.

The local complement choices are now packaged when supplied: `ThroughSubspaceChartData`
stores complements, complement bases, and one initial through-basis, and
`exists_unitriangular_toMatrix_throughSubspaceEdge_chartData_eq_fromBlocks_one_zero`
states the per-edge transformed matrix remains in identity-corner chart form.
The finite-dimensional existence layer is also Lean-proved:
`throughSubspaceComplement` chooses per-layer complements,
`throughSubspaceComplementIndex` indexes them by `Fin (finrank ...)`, and
`throughSubspaceChartDataOfFiniteDimensional` builds concrete chart data using
`Module.finBasis`. The theorem
`exists_isCompl_ker_throughSubspaceChartDataOfFiniteDimensional` chooses `U₀`
complementary to the total kernel while preserving the already proved
`finrank U₀ = finrank range P` equality. Concrete finite-basis corollaries now
instantiate the per-edge `[I B; 0 D]` form, the unitriangular chart-preservation
form, and the endpoint `[I 0; 0 0]` form with these chosen complements and
`Module.finBasis` bases. This is still an existential through-basis coordinate
construction, not Aoyagi's printed fixed-coordinate chart theorem.

Still open for this repair: translate the source-to-target Lean orientation
back to Aoyagi's paper order, express the paper-side rank/open-chart hypotheses
against these finite chart-data statements, and connect the matrix corollaries
to the chart-local product-reduction identity. Full Theorem 3 remains blocked
until those corollaries, the induction assembly, and analytic certificate
transport are built. The current bridge inventory is saved in
`threads/03-block-product-reduction/paper-order-bridge-notes.md`.

The first paper-order bridge artifact is Lean-proved in
`lean/DLNFibre/DLN/Aoyagi/ThroughLayerBasis.lean`: `paperChainMap` is the
descending composite for Aoyagi-order maps `W_(s+1) -> W_s`, with identity,
one-edge, transitivity, and full-product prefix/suffix split lemmas. This is
product-order bookkeeping only.

The reversal bridge is now Lean-proved in the same file: `reverseVertex`
reverses the paper-order vertex family, `reverseEdge` is the one-edge
paper-order composite viewed as a source-to-target edge, and
`chainMap_reverse_eq_paper` proves that the source-to-target `chainMap` on
these reversed vertices is exactly the corresponding `paperChainMap`. This
removes the orientation bookkeeping obstruction.

The finite paper-order edge block wrappers are now Lean-proved in
`lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`.
`disjoint_ker_reverse_total_of_disjoint_ker_paperChainMap` turns the paper-order
total-kernel disjointness hypothesis into the reversed chain hypothesis,
`isCompl_ker_reverse_total_of_isCompl_ker_paperChainMap` does the same for
kernel complements, and
`exists_toMatrix_reverseEdge_finiteDimensional_eq_fromBlocks_one_zero` plus
`exists_unitriangular_toMatrix_reverseEdge_finiteDimensional_eq_fromBlocks_one_zero`
instantiate the finite adapted-basis edge and unitriangular block statements on
the reversed paper chain. The endpoint wrapper
`toMatrix_paperChainMap_ker_finiteDimensional_eq_fromBlocks_one_zero_zero`
gives the total paper product the adapted `[I 0; 0 0]` form. Still open:
determinant/open chart wrappers and Theorem 3 assembly.

Indexed block algebra is also Lean-proved now:
`schurComplement_leftBlockElim_fromBlocks_indexed`,
`schurComplement_blockElim_fromBlocks_indexed`, and
`productReduction_chartLocalInductionStep_fromBlocks_indexed`. These are exact
finite-index generalisations of the existing `Fin`-indexed block identities and
the chart-local induction step. They do not add a new mathematical claim; they
remove index-conversion friction for future chart-data assembly.

The algebraic determinant-chart predicate layer is Lean-proved in
`ProductReduction.lean`: `identityCornerForm` implies the selected
`topLeftCorner` is `1` and hence `identityCornerDetChart`; upper-unitriangular
multiplication preserves `identityCornerForm`. In `ThroughLayerMatrix.lean`,
`paperAdaptedReverseEdgeMatrix` and `paperUnitriangularLeft` name the adapted
paper-order edge matrix and left multiplier. The adapted edge matrix and its
unitriangular transform are proved to satisfy the determinant-chart predicate.
This is only algebraic `IsUnit` at the adapted base matrix, not a topological
open-neighborhood theorem.

One-edge right elimination is Lean-proved. The bedrock identity
`productReduction_blockDiagonal_mul_fromBlocks_one_zero_rightElim_indexed`
states the explicit block multiplication over a `NonAssocRing`; the equality
corollary
`productReduction_blockDiagonal_mul_eq_fromBlocks_one_zero_rightElim_indexed`
and convenience wrapper
`productReduction_blockDiagonal_mul_identityCornerForm_rightElim` package it
for a matrix known to have identity-corner form. If a block-diagonal prefix is
followed by such an edge, a right upper-unitriangular source-side multiplier
removes the top-right block and updates the residual prefix by multiplying the
old residual block with the edge's lower-right block. The paper-order corollary
`productReduction_paperAdaptedReverseEdgeMatrix_rightElim` applies this to the
named adapted reversed paper edge. This is still one-edge algebra only; it does
not iterate the product reduction or prove endpoint compatibility.

The endpoint total-product normal form is Lean-proved as
`toMatrix_chainMap_zero_last_ker_basisOfIsCompl_eq_fromBlocks_one_zero_zero`: with
source basis adapted to `U₀ ⊕ ker P` and target basis adapted to
`throughSubspace last ⊕ Wlast`, the total composite has matrix
`[I 0; 0 0]`. The zero complement columns use the source complement being
`ker P`; this is not a fixed-coordinate statement and does not choose all
intermediate layer bases simultaneously.

The endpoint-compatible shared-basis layer is now Lean-proved in
`ThroughLayerMatrix.lean`. `throughSubspaceAdaptedBasis` names the ambient
basis at each vertex from a supplied `ThroughSubspaceChartData` bundle.
`toMatrix_chainMap_zero_last_chartData_eq_fromBlocks_one_zero_zero_of_maps_complement_to_zero`
states the endpoint `[I 0; 0 0]` form using that same basis family whenever
the source complement maps to zero. The finite endpoint construction chooses
the source complement to be the total kernel and arbitrary complements
elsewhere, and
`endpointChartData_edge_and_totalProduct_blocks` packages one edge block and
the total-product block in the same bases. Paper-order wrappers instantiate
this on the reversed Aoyagi chain. Remaining work: prove the ordered product
of edge matrices is the endpoint matrix in this basis family, then iterate the
product-reduction step.

The first matrix-composition bridge is now Lean-proved:
`throughSubspaceAdaptedChainMapMatrix` and `throughSubspaceAdaptedEdgeMatrix`
name chain-segment and one-edge matrices in the supplied adapted bases, and
`throughSubspaceAdaptedChainMapMatrix_succ` proves the one-step recurrence.
For the source-to-target Lean chain the order is `edge * prefix`, coming from
`chainMap_succ` and Mathlib's `LinearMap.toMatrix_comp`. This is composition
bookkeeping only; it does not yet iterate over all edges or run the
product-reduction induction.

The local chart-stability block calculation from this repair is Lean-proved as
`upperUnitriangular_mul_fromBlocks_one_zero`: `[I -F; 0 I] [I B; 0 D] =
`[I B - F D; 0 D]`. The corollary
`exists_fromBlocks_one_zero_of_upperUnitriangular_mul` packages this as
preservation of the identity-corner chart form once a matrix is known to have
some form `[I B; 0 D]`; indexed variants support the arbitrary basis index
types used by `ThroughSubspaceChartData`. It does not run Aoyagi's full
induction.

## Drift guard

- Normal-crossing extraction: Cited.
- Aoyagi-specific block/product/blow-up/arithmetic steps: Prove by default.
- Source summaries are not enough. Reproduce substantial calculations on paper
  and check them carefully before formalising.
- No theorem name may say more than its statement proves.
- A0 is a concrete normal-crossing extraction citation, not a general
  ideal-generator invariance or regular-additivity theorem. Aoyagi Lemma 1 and
  Theorem 4 remain outside the citation boundary unless the operator expands it.
- Aoyagi's `theta` means pole order / RLCT multiplicity. Use a distinct
  Lean/display name such as `rlctOrder` rather than reusing any existing
  component-count convention.
- Universal or exhaustive case-split claims need decorrelated counterexample
  hunting or a proof of completeness before being treated as established.
