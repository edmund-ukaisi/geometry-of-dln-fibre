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
  blocked, not formalisation-ready. The current repair report
  `threads/04-blow-up-certificate/reproduction-repair-a4.md` separates actual
  widths `M^{(s)}` from prefix minima `M(S)`. Page-image inspection and xhigh
  source/pen-and-paper rechecks confirm a sharper Case 2 obstruction: the
  printed new vector has
  `t_{S,J+1}^{(i)}=M^{(i+1)}` for `i<S`, while the same chart records
  `M'_{S,J+1}=(M(S)-J)(M^{(S+1)}-J)`. The terminal exponent formula on PDF p. 22
  uses actual widths, so substituting the printed vector gives
  `(M^{(S)}-J)(M^{(S+1)}-J)` unless `M(S)=M^{(S)}`. The prefix-minimum vector
  repairs the arithmetic but is not the printed source data. Other blockers are
  missing pivot charts, incomplete invariant recurrence,
  regularity/divisibility of `P`, the printed `b'_i`/standalone-`u` ambiguity,
  unstable termination measure, and unchecked boundary cases.
  The safe arithmetic split is now Lean-proved in
  `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  `terminalExponent_printedCase2Vector` evaluates the printed vector to the
  actual-width expression, and `terminalExponent_prefixCase2Vector` evaluates
  the corrected prefix-minimum vector to the printed update. This does not
  prove any blow-up chart or transition.
  The `P` quotient regularity arithmetic is also Lean-proved in the same file:
  `monomialRec_dvd_of_le` and `pivotMul_monomialRec_dvd_of_le` show that
  recurrence monomials divide later recurrence monomials, even after common
  pivot multiplication. This is the arithmetic witness for `b'_i/b'_(J+1)`,
  not yet a construction of the row-operation matrix.
  The normalized `P` row-operation algebra is now also Lean-proved:
  `weightedPivotBlockRowOp_mul_diagonal_mul` packages the pivot split
  `[1 0; x D]` and proves the lower first column is cleared under quotient
  witnesses `b_i=q_i*b0`. This still assumes the `Q`-normalised shape and a
  consistent choice about whether the common pivot factor is inside the
  diagonal weights or outside.
  The normalized `Q` column-operation algebra is now Lean-proved in the same
  file: `pivotPreQBlock_mul_pivotQ` proves
  `[1 y; x D] * [1 -y; 0 I] = [1 0; x D-x*y]`,
  `pivotQ_mul_pivotQinv` and `pivotQinv_mul_pivotQ` prove the displayed inverse
  is two-sided, and `pivotPreQBlock_mul_eq_postQ_mul_Qinv_mul` proves that
  replacing the following factor by `Q^-1 C` preserves the local product. This
  closes the narrow normalized pivot-algebra layer, not pivot-chart coverage,
  exponent recurrence, termination, or a full transition theorem.
  The `Q/P` composition is now also Lean-proved:
  `pivotPostQBlock_eq_weightedPivotBlockMatrix`,
  `weightedPivotBlockRowOp_mul_diagonal_mul_pivotPostQBlock`,
  `weightedPivotBlockRowOp_mul_diagonal_mul_pivotPreQBlock_mul_pivotQ`, and
  `weightedPivotBlockRowOp_mul_diagonal_mul_pivotPreQBlock_mul` package the
  displayed local pivot calculation into one product identity, including the
  following-factor replacement by `Q^-1`. This is still finite matrix algebra
  only; it does not prove chart coverage, regular coordinate-change/Jacobian
  facts, exponent updates, or the transition invariant.
  The label-range part of the width repair is now Lean-proved too:
  `prefixMinNat`, `actualWidthLabel`, `prefixWidthLabel`, and the undercount
  theorem `actualWidthLabel_not_prefixWidthLabel_of_prefixMinNat_lt_width`
  separate actual source labels from prefix-minimum bounds. The Case 2 new-label
  lemmas record that `(S,J+1)` is an actual label under the actual-width bound
  and a prefix-width label only under the stronger continuation bound. This is
  bookkeeping for the corrected vector invariant, not the invariant itself.
  `correctedCase2PivotVector` and
  `terminalExponent_correctedCase2PivotVector` also package the prefix-minimum
  Case 2 repair over natural widths.
  The introduced-label convention is now Lean-proved as `introducedLabel` with
  monotonicity in `J` and before/after lemmas for the new pivot label
  `(S,J+1)`. This gives a finite active-label domain for later vector/exponent
  assignments; it does not yet assign or update those data. The prefix-bound
  corollary keeps the actual-width label validity separate from the stronger
  source continuation condition.
  The corrected Case 2 vector now has a finite minimum certificate in Lean:
  prefix-minimum antitonicity plus component formulas prove that, under
  `J<=mu_S`, all components are at least `J` and the `S` component is exactly
  `J`; `correctedCase2PivotVector_isLeast_valueSet_Icc` packages this over
  the finite source range `1..L`. This is the repaired `tilde_t=J`
  bookkeeping for the new Case 2 label, not a transition theorem or
  comparability result.
  The one-label package `CorrectedCase2NewLabelCertificate` now combines, only
  for `(S,J+1)`, introducedness after the pivot advance, the corrected terminal
  exponent, and the finite least-value certificate. Its main constructor keeps
  actual source-label validity `J+1<=n_(S+1)` separate from the state bound
  `J<=mu_S`; the continuation-bound constructor derives both from
  `J+1<=mu_(S+1)`. This still does not assign vector data to every introduced
  label or prove a Case 2 transition.
  The finite exponent-domain layer is now explicit:
  `LabelExponentCertificate` certifies one introduced label, and
  `IntroducedLabelExponentCertificates` certifies all labels introduced at a
  state. The extension lemmas only extend the domain from `(S,J)` to
  `(S,J+1)` when old data is supplied unchanged and the new label is already
  certified; they are not transition theorems. The Case 2 residual-block entry
  set is also recorded as rows `J+1..mu_S` and columns `J+1..n_(S+1)`, with the
  displayed pivot included under continuation; no chart-cover theorem is
  claimed.
  The selected-entry substitution scaffold `selectedEntryChartMap` now captures
  the finite algebraic pattern in the displayed pivot charts: selected generator
  maps to `u`, other center generators map to `u` times residual coordinates.
  The Case 2 displayed-pivot specialization is proved, but no chart cover or
  non-displayed transition formula is claimed.
  Case 1 now has the tail-lowering exponent increment in Lean:
  `terminalExponent_lowerTailVector_of_flatFromPred` and the source-shaped
  `terminalExponent_lowerTailVector_of_flatFromPred_add` prove that lowering a
  flat tail from level `J+J1` to `J` adds `J1(n_(S+1)-J)`. The flat-tail
  hypothesis and boundary conditions `2<=S<=L` remain explicit invariant
  obligations. The lower-tail component/minimum facts and the one-label
  transformer `LabelExponentCertificate.lowerTailVector_of_flatFromPred_add`
  are also proved; the transformer is conditional on old least value `J+J1`
  and `J<=J+J1`, and is not an all-label transition.
  Case 1 center generators are now finite symbols in Lean: one chosen old
  exceptional generator plus the actual-width row strip. This supports later
  selected-entry chart bookkeeping, but does not encode old-label hypotheses,
  row-strip source validity, chart coverage, or transition formulas.
  The row-strip source-validity containment is now isolated: under
  `J+J1<=mu_S`, the Case 1 strip rows and entries lie in the residual-block
  entry set. This is only finite containment, not the full Case 1 first-jump or
  chart transition theorem.
  The first-jump hypotheses are now separately packaged in Lean as
  `Case1FirstJumpHypotheses`: strict nonterminal boundary `J+J1<mu_S`,
  selected introduced label, selected level, empty intermediate gap, and
  componentwise minimality on `1..L`. The package derives row containment and a
  Nat-to-Int selected-level cast, but still does not prove the `b` recurrence
  equality/inequality, `level = leastValue`, flat-tail, chart coverage, or a
  transition invariant.
  The Case 1(1) same-domain lower-tail update is now packaged conditionally:
  `case1_selectedLowerTail_sameDomain` reassembles
  `IntroducedLabelExponentCertificates` at the same `(S,J)` after replacing
  the selected label by its lower-tail certificate, assuming `leastValue =
  level`, flat-tail, selected post-data, and unchanged non-selected labels. It
  is not a chart transition and does not prove `b'_i` bookkeeping or domain
  advancement. The selected-label update-data helpers instantiate this theorem
  with total assignment overrides; they add no source geometry.
  The level/tail invariant bridge is now isolated as
  `IntroducedLabelLevelTailInvariants`: it assumes `leastValue=level` for
  introduced labels and flat-tail only above the current pivot. This feeds the
  selected Case 1 update via `lt_selectedLevel`, but it is not a proved or
  preserved invariant.
  Arbitrary selected-entry finite-center facts are now proved for Case 1 and
  Case 2 centers: `u` occurs in the finite substitution value set, witnessed
  by the selected pivot, and all transformed center generators are divisible by
  `u`. This helps chart-family indexing but is not chart coverage or a
  non-displayed transition theorem.
  The generic pivot-first `Q/P` algebra bridge is also proved: a matrix with a
  selected pivot entry equal to `1` can be reindexed to the existing
  `pivotPreQBlock` shape, and the normalised `Q/P` identities apply under
  explicit quotient witnesses. This still leaves the Aoyagi-specific arbitrary
  chart construction, coordinate transport, row-weight quotient witnesses, and
  exponent updates open.
  The generic pivot-row quotient witness layer is now proved: divisibility,
  equality, monomial recurrence tails, equality-or-later recurrence data, and
  common pivot multiplication can all produce witnesses `b_i = q_i*b0` for the
  `P` theorem. Aoyagi-specific arbitrary chart construction, pivot-first
  transport, and row hypotheses are still open.
  The pivot-first existential `Q/P` wrappers now combine these two generic
  layers: divisibility or equality-or-later recurrence hypotheses choose `q`
  inside the pivot-first `Q/P` identities, including the common-pivot-multiple
  variant. This removes a mechanical bridge but does not prove selected-entry
  chart construction, coordinate/weight transport, or Aoyagi-specific row
  hypotheses.
  The source-displayed Case 2 top-left pivot is now Lean-instantiated:
  displayed residual row/column index types, displayed pivot row/column
  elements, selected-entry normalisation, and the flat-row-weight
  product-preservation `Q/P` identity are proved. This remains local to
  `d_(J+1,J+1)` and still does not prove arbitrary-pivot charts, atlas
  coverage, full source-variable transport, or exponent updates.
  The finite following-factor reindexing transport is also proved:
  `pivotFirstFollowingFactor` is the following factor in pivot-first column
  coordinates, and multiplying by it commutes with reindexing the original
  product. This handles only matrix reindexing, not the source coordinate
  construction or regularity of the chart.
  The diagonal row-weight reindexing is also proved:
  `weightedPivotDiagonal_eq_pivotFirst_diagonal` identifies the split pivot
  diagonal with the original supplied diagonal after pivot-first row/column
  reindexing. This does not prove source row-weight assignment or flatness.
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
this on the reversed Aoyagi chain. The ordered adapted edge-product theorem now
identifies the endpoint matrix with the recursively ordered product in any
supplied adapted basis family. Remaining work: iterate the product-reduction
step.

The adapted matrix-composition bridge is now Lean-proved:
`throughSubspaceAdaptedChainMapMatrix` and `throughSubspaceAdaptedEdgeMatrix`
name chain-segment and one-edge matrices in the supplied adapted bases, and
`throughSubspaceAdaptedChainMapMatrix_succ` proves the one-step recurrence.
For the source-to-target Lean chain the order is `edge * prefix`, coming from
`chainMap_succ` and Mathlib's `LinearMap.toMatrix_comp`.
`throughSubspaceAdaptedChainMapMatrix_succ_right` proves the suffix-oriented
version `suffix * edge`, using `chainMap_trans`; this is the orientation needed
for right elimination.
`throughSubspaceAdaptedEdgeProductMatrix` is a dependent recursive product of
the adapted edge matrices, and
`throughSubspaceAdaptedChainMapMatrix_eq_edgeProductMatrix` proves that it is
the chain-map matrix for any interval. This is composition bookkeeping only; it
does not yet run the product-reduction induction.

The right-elimination interface now has canonical blocks:
`upperRightBlock` and `lowerRightBlock` are the actual submatrices of a block
matrix. `productReduction_blockDiagonal_mul_identityCornerForm_rightElim_submatrix`
eliminates an identity-corner matrix using `upperRightBlock M` and returns
`lowerRightBlock M` in the residual product, and
`productReduction_blockDiagonal_mul_unitriangular_identityCornerForm_rightElim`
packages the same step after an accumulated upper-unitriangular left
multiplier. This removes the existential witness from the next induction step.

The suffix-chain right-elimination theorem is now Lean-proved in two layers.
`productReduction_identityCorner_suffixStep_rightElim` proves the induction
step after inserting the inverse of the previous upper-unitriangular right
multiplier, using the cancellation lemmas
`upperUnitriangular_neg_mul_upperUnitriangular` and
`upperUnitriangular_neg_mul_upperUnitriangular_neg_neg`.
`productReduction_identityCorner_suffixChain_rightElim` iterates this over a
dependent chain of identity-corner edge matrices, assuming only identity empty
segments, suffix composition, and proof-irrelevance of the segment matrix in
the order proof. `productReduction_throughSubspaceAdaptedChainMapMatrix_suffixChain_rightElim`
instantiates the theorem for supplied through-subspace adapted bases, using
`throughSubspaceAdaptedChainMapMatrix_proof_irrel`,
`throughSubspaceAdaptedChainMapMatrix_self`, and
`identityCornerForm_throughSubspaceAdaptedEdgeMatrix`. This still does not
provide a rank/open chart statement or any analytic/RLCT consequence.

The paper-order endpoint wrapper is now Lean-proved as
`productReduction_paperChainMap_endpointChartData_suffixChain_rightElim` in
`ThroughLayerMatrix.lean`. It instantiates the supplied suffix-chain theorem on
`(reverseVertex W) (reverseEdge W B)` with endpoint-compatible finite chart
data and rewrites the total reversed chain map as Aoyagi's `paperChainMap` via
`chainMap_reverse_eq_paper`. This is still pointwise adapted-coordinate
bookkeeping: the bases depend on the actual chain and the statement does not
assert fixed coordinate charts, an open rank/determinant neighborhood, regular
coordinate changes, residual-factor identification, or RLCT/certificate
transport.

The first rank/open split is now Lean-proved. In
`BlockElimination.lean`, `rank_toMatrix_eq_finrank_range` packages Mathlib's
basis-invariance of matrix rank for `LinearMap.toMatrix`, and
`rank_schurComplement_eq_sub_rank_fromBlocks` gives the subtraction form of the
Schur-complement rank formula. In `ThroughLayerMatrix.lean`,
`lowerRightBlock_paperAdaptedReverseEdgeMatrix_rank_eq_sub` applies these facts
to a paper adapted edge: the residual lower-right block has rank
`finrank range(reverseEdge) - finrank U₀`. In `ChartTopology.lean`,
`isOpen_identityCornerDetChart` proves the selected determinant chart is open
over a topological ring with open units, and paper adapted edge matrices plus
unitriangular transforms have that chart as a neighborhood. This is still not
a source-faithful local theorem: exact rank strata are explicit hypotheses, not
open sets, and the current adapted bases are chosen from the actual chain
rather than fixed from a basepoint for nearby variable chains.

The endpoint fixed-chain basepoint certificate is now Lean-proved in
`lean/DLNFibre/DLN/Aoyagi/BasepointCertificate.lean`. It names
`paperTotalMap`, endpoint chart data, endpoint adapted edge matrices, and the
endpoint adapted total matrix. The new theorem
`lowerRightBlock_throughSubspaceEndpointAdaptedEdgeMatrix_rank_eq_sub` repeats
the Schur-rank bridge in the endpoint chart data, so the paper wrapper
`lowerRightBlock_paperEndpointAdaptedEdgeMatrix_rank_eq_sub` is aligned with
the same endpoint basis family used for the total product. The structure
`PaperEndpointBasepointCertificate`, together with
`paperEndpointBasepointCertificate_of_isCompl` and
`exists_paperEndpointBasepointCertificate`, bundles the finrank/range equality,
edge identity-corner form, determinant-chart neighborhoods for edges and
unitriangular transforms, residual edge ranks, total `[I 0; 0 0]` block form,
and suffix-chain right elimination. This is still explicitly basepoint-only:
no variable-chain fixed-coordinate family, exact rank-stratum neighborhood,
regular coordinate-change certificate, normal-crossing extraction, or RLCT
claim is asserted.

The fixed-basepoint variable-chain layer is now Lean-proved in
`lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean`. The base chain `B` supplies
the endpoint bases; the variable chain `C` supplies only the maps being
represented. `paperEndpointFixedBaseEdgeMatrix`,
`paperEndpointFixedBaseChainMapMatrix`, and
`paperEndpointFixedBaseTotalMatrix` give the fixed-coordinate matrices, with
`paperEndpointFixedBaseChainMapMatrix_succ_right` proving suffix composition
and `paperEndpointFixedBaseTotalMatrix_eq_chainMapMatrix` linking the total
matrix to the full reversed chain. At `C = B`, the fixed-base matrices are
definitionally the endpoint adapted basepoint matrices. The generic block API
now includes `lowerLeftBlock`, `schurResidualBlock`, and
`rank_schurResidualBlock_eq_sub_rank_of_identityCornerDetChart`; the paper
wrapper `rank_schurResidualBlock_paperEndpointFixedBaseEdgeMatrix_eq_sub` keeps
both determinant-chart membership and exact rank as explicit hypotheses. A
two-edge wrapper records the first nontrivial product equality without relying
on brittle `Fin` definitional equality. This prepared the fixed-base
chart-local induction that is recorded next.

The first fixed-base variable-chart suffix step is now Lean-proved.
`productReduction_chartLocal_suffixStep_fromBlocks_indexed` in
`ProductReduction.lean` packages one Aoyagi Lemma 2 induction move with a
supplied transformed edge `M`: a previously reduced suffix
`Lprev * Ptail * Rprev = [Ctop 0; 0 Dprev]` and a factorisation
`E = Rprev * M` advance to a reduced form with top block
`Ctop * topLeftCorner M` and residual block
`Dprev * schurResidualBlock M`, under explicit determinant-unit hypotheses.
`paperEndpointFixedBase_chartLocal_suffixStep` instantiates this for fixed-base
variable-chain segment matrices. The rank bridge
`rank_paperEndpointFixedBaseEdgeMatrix_eq_finrank_range` lets later exact-rank
hypotheses be stated as source map rank, and
`rank_schurResidualBlock_paperEndpointFixedBaseEdgeMatrix_eq_range_sub`
computes the Schur residual rank from the actual variable edge range rank under
the determinant-chart hypothesis.

The all-layer explicit-chart induction is now Lean-proved.
`productReduction_chartLocal_suffixChain_blockDiagonal_indexed` mirrors the
identity-corner suffix-chain induction but assumes determinant-chart membership
for each transformed edge `[I Bprev; 0 I] * E p`. It returns a determinant-unit
left multiplier, a source-side upper-unitriangular right multiplier, a
determinant-unit top block, and a residual block putting the chain segment in
block-diagonal form. The fixed-base wrapper
`productReduction_paperEndpointFixedBaseChainMapMatrix_chartLocal_blockDiagonal`
applies the theorem to `paperEndpointFixedBaseChainMapMatrix`. This is the
first source-faithful fixed-coordinate product-reduction theorem at the
algebraic/chart level. Still open: proving the transformed determinant-chart
hypotheses on an actual fixed-coordinate neighborhood, exact rank-stratum
packaging, regular coordinate-change/certificate transport, and RLCT
consequences.

The matrix-level basepoint determinant-neighborhood package is now Lean-proved.
`leftMul_identityCornerDetChart_mem_nhds` and
`fromBlocks_leftMul_identityCornerDetChart_mem_nhds` in `ChartTopology.lean`
pull the selected determinant chart back along fixed left multiplication. The
fixed-base wrapper
`paperEndpointFixedBaseEdgeMatrix_selfBase_mem_nhds_transformed_identityCornerDetChart`
in `FixedBasepointChart.lean` applies this at `C = B`: for a fixed edge `p` and
fixed accumulated upper block `Bprev`, the predicate
`identityCornerDetChart ([I Bprev; 0 I] * M)` is an ambient matrix-space
neighborhood of the base fixed-base edge matrix. This is pointwise in `Bprev`;
it is not an infinite-intersection statement over all possible previous blocks,
and it is not yet a neighborhood theorem for variable chains. At this checkpoint
the missing bridge was a topology on fixed-coordinate edge parameters and
continuity of the fixed-basis coordinate map; the next paragraph records the
one-edge version now proved.

The first edge-parameter topology bridge is now Lean-proved. The generic lemma
`continuous_linearMap_toMatrix` says that for fixed source and target bases,
the map from a continuous linear map to its coordinate matrix is continuous.
The fixed-base wrapper
`paperEndpointFixedBaseContinuousEdge_selfBase_mem_nhds_transformed_identityCornerDetChart`
pulls the transformed determinant-chart neighborhood back to a neighborhood of
the base edge in the `ContinuousLinearMap` topology. This is still a one-edge
statement with fixed `p` and fixed `Bprev`, not a product topology theorem for
all chain variables and not a statement that the induction-produced `Bprev`
varies continuously. This left the finite-intersection/product assembly as the
next topology bridge, recorded in the following paragraph.

The fixed-family edge-product topology assembly is now Lean-proved as
`paperEndpointFixedBaseContinuousEdges_selfBase_mem_nhds_transformed_identityCornerDetChart`.
For a prescribed family `Bprev p`, the set of continuous reversed-edge families
whose fixed-basis coordinate matrices satisfy all transformed determinant-chart
predicates is a neighborhood of the base edge family in the finite Pi topology.
This is the honest finite-intersection step; it does not quantify over every
possible accumulated upper block and does not show that the `Bprev` family
constructed during the suffix-chain induction varies continuously. The
remaining topology handoff at this stage was to allow a supplied `Bprev` family
to vary continuously with the edge parameters, with exact rank strata kept as
explicit hypotheses.

That continuity handoff is now Lean-proved in parameter-space form as
`paperEndpointFixedBaseContinuousEdges_variableBprev_mem_nhds_transformed_identityCornerDetChart`.
For an arbitrary topological parameter space, if the continuous reversed-edge
family and the accumulated-upper-block family `Bprev` are continuous at a
parameter and the transformed determinant charts hold there, then the same
transformed chart predicates hold on a neighborhood of that parameter. This is
not a construction of the induction-produced `Bprev`; it is the reusable
topological lemma that will apply once that recursive data is made
deterministic and continuous.

Pen-and-paper reproduction of the suffix-chain proof identifies the recursive
right-elimination block. With `U_+(B) = [I B; 0 I]`, the transformed edge is
`M_p = U_+(Bprev) * E p`, and the next block is
`(topLeftCorner M_p)⁻¹ * upperRightBlock M_p`. The existing existential proof
already passed this witness forward. Lean now makes this deterministic
recurrence explicit and proves the corresponding chart-local reduction under
recursive chart hypotheses; continuity on a neighborhood where those chart
hypotheses hold remains open.

The deterministic state layer is now Lean-proved in `ProductReduction.lean`.
`ChartLocalSuffixState` packages the current left multiplier,
right-elimination block `B`, top block `Ctop`, and residual block `D`.
`ChartLocalSuffixState.transformedEdge` forms `[I B; 0 I] * E p`,
`ChartLocalSuffixState.step` updates the state with
`Bnext = (topLeftCorner M)⁻¹ * upperRightBlock M`, and
`ChartLocalSuffixState.step_blockDiagonal` proves that this deterministic
update preserves the block-diagonal invariant under the recursive
determinant-chart hypothesis on `M`. The recursive layer is also proved:
`ChartLocalSuffixState.terminal`, `ChartLocalSuffixState.suffixState`,
`ChartLocalSuffixState.suffixState_self`, and
`ChartLocalSuffixState.suffixState_castSucc` define and unfold the state
obtained by descending from endpoint `j` to `i`, while
`ChartLocalSuffixState.suffixState_blockDiagonal` proves the full recursive
block-diagonal invariant. The public existential theorem
`productReduction_chartLocal_suffixChain_blockDiagonal_indexed` is now a
wrapper extracting the four fields from this deterministic state. The next
topological target is the recursively produced `Bprev` field and the fixed-base
chart neighborhood it controls.

The `Bprev` part of that topology target is now Lean-proved. In
`ChartTopology.lean`, `continuousAt_matrix_inv_of_isUnit_det` packages
continuity of matrix inversion at a unit determinant over a normed field,
`continuousAt_chartLocalSuffixState_step_B` proves continuity of the
one-step accumulated upper block, and
`continuousAt_chartLocalSuffixState_suffixState_B` iterates this down the
deterministic suffix recursion. In `FixedBasepointChart.lean`,
`paperEndpointFixedBaseContinuousEdges_recursiveBprev_mem_nhds_transformed_identityCornerDetChart`
feeds the actual recursively produced `Bprev` family into the existing
variable-`Bprev` handoff. This gives a fixed-base neighborhood where the
recursive transformed-edge determinant charts persist, assuming those charts
hold at the base parameter. It still does not prove exact-rank neighborhoods,
certificate transport, or continuity of the remaining `L`, `Ctop`, and `D`
state fields.

The endpoint handoff from recursive chart persistence to the actual
block-diagonal product form is now Lean-proved. `FixedBasepointChart.lean`
adds fixed-base matrix coordinates for arbitrary reversed edge families, so the
continuous-edge topology statements no longer need to pass through a
paper-order variable chain. The theorem
`paperEndpointFixedBaseChainMapMatrixOfReverseEdges_recursiveChart_blockDiagonal`
uses `ChartLocalSuffixState.suffixState_blockDiagonal` directly for
`i = 0`, `j = Fin.last N`; this avoids the older public all-`Bprev` chart
wrapper and matches the topology theorem, which supplies charts only for the
actual recursive accumulated upper blocks. The neighborhood wrapper
`paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_blockDiagonal_mem_nhds`
says that if a continuous reversed-edge family is based at `reverseEdge W B`,
then nearby endpoint products have the deterministic block form in endpoint
bases fixed from `B`. The pen-and-paper check is the same recurrence:
`M = [I Bprev; 0 I] * E p`, `Bnext = (topLeftCorner M)^-1 *
upperRightBlock M`, and the basepoint determinant chart follows from the
endpoint unitriangular identity-corner theorem with `F = -Bprev`.

The residual block data needed for a later reduced-product certificate is now
named, but only in the adapted recursive sense. In `ProductReduction.lean`,
`ChartLocalSuffixState.residualBlock` is
`schurResidualBlock ([I Bprev; 0 I] * E p)` for the actual suffix state, and
`ChartLocalSuffixState.suffixState_D_castSucc` proves that the `D` field
updates by multiplying this visited residual block. This is deliberately not a
closed-form `Finset.prod` of raw edge residuals; the matrix types vary with the
vertices, and the left unitriangular transform changes the Schur residual. In
`FixedBasepointChart.lean`, the transformed fixed-base reversed-edge residual
rank is proved pointwise from determinant-chart membership and an exact rank
hypothesis on the edge map. Exact-rank conditions remain hypotheses, not
neighborhood conclusions. The combined theorem
`paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_blockDiagonal_rankImp_mem_nhds`
therefore states the safe source-facing boundary: near the base chain,
recursive determinant charts and endpoint block form hold, and exact edge ranks
may be supplied pointwise to obtain residual ranks. It does not prove a
neighborhood of exact edge ranks.

The local chart-stability block calculation from this repair is Lean-proved as
`upperUnitriangular_mul_fromBlocks_one_zero`: `[I -F; 0 I] [I B; 0 D] =
`[I B - F D; 0 D]`. The corollary
`exists_fromBlocks_one_zero_of_upperUnitriangular_mul` packages this as
preservation of the identity-corner chart form once a matrix is known to have
some form `[I B; 0 D]`; indexed variants support the arbitrary basis index
types used by `ThroughSubspaceChartData`. It does not run Aoyagi's full
induction.

The source-facing elementary A2 boundary is now packaged in
`ProductReductionBoundary.lean`. The fixed-base certificate records exactly the three
nearby facts proved so far: recursive determinant charts, deterministic
endpoint block form, and transformed residual-rank implications from exact
pointwise edge ranks. The local fixed-base certificate adds the basepoint
certificate and a neighborhood membership statement; the existential local
certificate chooses a total-kernel complement. This closes the previous A2
packaging target, but not the full printed triangular product-reduction theorem
from Aoyagi's source hypotheses; the post-Theorem-3 RLCT/regular-variable
transport is a separate deferred analytic/certificate problem. The next honest
target is A4 reproduction repair. The actual-width/prefix-minimum split is now
clear, but the printed Case 2 vector disagrees with the printed numerator
increment after substitution into the terminal exponent formula unless
`M(S)=M^{(S)}`. Resolve that source-level mismatch or split a corrected
certificate from the printed transition before attempting a full Lean
transition theorem. Narrow Lean work may proceed only where independent of this
issue, such as finite bookkeeping or monomial divisibility for regularity of
the `P` matrices.

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
