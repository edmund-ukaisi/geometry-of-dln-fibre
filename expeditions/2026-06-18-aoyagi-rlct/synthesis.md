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

## Latest A2 Update

The triangular endpoint-multiplier wrapper for Aoyagi Theorem 3 has landed.
Pen-and-paper reproduction:
`threads/03-block-product-reduction/reproduction-a2-triangular-block-diagonal.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-triangular-block-diagonal.md`.
Review:
`threads/03-block-product-reduction/review-a2-triangular-block-diagonal.md`.

Lean names:
`lowerUnitriangular_mul_fromBlocks_one_zero_indexed`,
`ChartLocalSuffixState.step_L_eq_lowerUnitriangular`,
`ChartLocalSuffixState.suffixState_L_eq_lowerUnitriangular`,
`ChartLocalSuffixState.suffixState_blockDiagonal_exists_triangularBlockDiagonal`,
`productReduction_chartLocal_suffixChain_triangularBlockDiagonal_indexed`, and
`PaperEndpointFixedBaseProductReductionCertificate.exists_triangularBlockDiagonal`.
The fixed-base endpoint theorem extracts regular triangular multipliers
`[I 0; F3 I]` and `[I F2; 0 I]` from the existing source-facing certificate,
with the proof witness `F2 = -S.B`.  This closes the narrow "triangular
multiplier shape" gap in the certificate.

Nonclaims remain: no chart coverage from only source rank hypotheses, no
exact-rank openness, no Aoyagi Lemma 1/analytic ideal transport, no
regular-coordinate RLCT additivity, no normal crossings, and no RLCT
consequence.

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
  coordinates, and multiplying by it commutes with reindexing the pre-reindexed
  product. This handles only matrix reindexing, not the source coordinate
  construction or regularity of the chart.
  The diagonal row-weight reindexing is also proved:
  `weightedPivotDiagonal_eq_pivotFirst_diagonal` identifies the split pivot
  diagonal with the original supplied diagonal after pivot-first row/column
  reindexing. This does not prove source row-weight assignment or flatness.
  The displayed Case 2 `Q/P` theorem now accepts a residual following factor
  before pivot-first reindexing: `case2DisplayedFollowingFactor` reindexes it
  into pivot-first coordinates, and
  `case2DisplayedNormalizedMatrix_mul_followingFactor` relates the pivot-first
  product to the product before pivot-first row reindexing. This still does
  not construct the full source coordinates.
  The displayed Case 2 source-substitution factor is now Lean-proved:
  `case2DisplayedSubstitutionMatrix` represents the selected-entry chart before
  factoring out the selected variable, and
  `case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst` moves that
  selected variable into updated row weights `u * weight` in pivot-first
  coordinates. The wrapper
  `exists_case2DisplayedQP_mul_sourceSubstitution_of_flat_weights` then applies
  the existing displayed `Q/P` theorem. This still does not prove the full
  source blockdiag identity, chart regularity, or exponent update.
  Lean also names the displayed transported following factor
  `case2DisplayedTransportedFollowingFactor` as `Q^{-1}` times the pivot-first
  following factor, and proves
  `exists_case2DisplayedQP_mul_transportedFollowingFactor_of_rowIndex_monomialRec`.
  That wrapper supplies the `P` quotient witnesses from monomial recurrence
  divisibility using the residual source-row bound `J+1 <= rowLevel`. It
  assumes the row weights already have the form `u * monomialRec step rowLevel`;
  it does not prove the source recurrence or the full transition.
  The displayed Case 2 source-block tail lift is now Lean-proved:
  `verticalBlock`, `fromBlocks_mul_verticalBlock`, and
  `fromBlocks_mul_verticalBlock_eq_of_tail` lift a residual-tail identity
  through unchanged top rows, while
  `exists_case2DisplayedQP_verticalBlock_sourceSubstitution_of_flat_weights`
  and
  `exists_case2DisplayedQP_verticalBlock_transportedFollowingFactor_of_rowIndex_monomialRec`
  apply this to the displayed source-substitution and row-index recurrence
  tail identities. This closes only the finite top-row reattachment
  bookkeeping; arbitrary pivots, source recurrence production, source chart
  regularity, exponent updates, and transition invariants remain open.
  The displayed Case 2 recurrence-gap row-weight bridge is also Lean-proved:
  `monomialTail_eq_one_of_forall_eq_one` and
  `monomialRec_eq_of_step_eq_one_on_Ico` prove constancy across a recurrence
  interval with all factors `1`, and
  `case2ResidualRow_monomialRec_eq_pivot_of_gap` applies this to
  residual rows `J+1..mu_S`. The wrapper
  `exists_case2DisplayedQP_mul_sourceSubstitution_of_gap_monomialRec` feeds
  the resulting flatness into the source-substitution `Q/P` theorem. The gap
  itself remains an explicit hypothesis, not a proved transition invariant.
  The finite label-product source of the gap is now Lean-proved conditionally:
	  `levelProductStep` is the product over supplied labels with a given level,
	  `levelProductStep_eq_one_of_forall_ne` and
	  `levelProductStep_eq_one_of_gap` prove that no supplied label at a level
	  makes that factor `1`, and
	  `case2ResidualRow_levelProduct_monomialRec_eq_pivot_of_gap` plus
	  `exists_case2DisplayedQP_mul_sourceSubstitution_of_labelGap` feed this into
	  the displayed Case 2 row-weight and `Q/P` wrappers. The introduced-label
	  finite-domain bridge is also Lean-proved: `introducedLabelFinset` enumerates
	  Lean's introduced-label predicate, and
	  `exists_case2DisplayedQP_mul_sourceSubstitution_of_introducedLabelGap`
	  applies the same wrapper over that domain. The recurrence-state interface
	  now packages the same conditional bridge with named `level`, `var`, derived
	  `step`, derived row `weight`, equality-only least-value gap bridge, and
	  displayed residual-row weight flatness. The bridge still assumes the level and
	  variable maps are the recurrence data, the introduced-label gap holds, and
	  row weights are generated by that recurrence. It keeps residual rows
	  `J+1..mu_S` separate from actual-width residual columns `J+1..n_(S+1)`, and
	  counts the selected variable once in the updated weights `u*b_i`. The Case
	  2 comparability sentence remains outside this bridge.
  The Case 2 recurrence-weight update is now Lean-proved conditionally:
  advancing the introduced-label finite domain from `(S,J)` to `(S,J+1)` adds
  exactly the new label `(S,J+1)` when it is source-valid; inserting a new label
  at recurrence level `J` multiplies the step factor at `J` by `u` and leaves
  other step factors unchanged; hence a supplied post-state satisfying those
  old/new recurrence-data assumptions has `post.weight i = u * pre.weight i`
  for every `J+1 <= i`. The source-facing wrapper
  `CorrectedCase2NewLabelCertificate.case2_weight_succ_current_eq_newVar_mul`
  packages this against the corrected new-label certificate, and the residual
  flatness consequence preserves displayed Case 2 flat row weights after common
  multiplication by `u`. This still does not prove chart production, the
  printed vector repair, comparability, exponent updates, transition
  invariants, normal crossings, or RLCT extraction.
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

The A4 displayed Case 2 source-substitution line is now connected to supplied
successor recurrence weights. The earlier local algebra proved
`diag(weight) * D_J = diag(u*weight) * D'_J`, and the recurrence update proved
`post.weight_i = u * pre.weight_i` for `i >= J+1`. Lean now combines these:
the pivot-first source-substituted block and the displayed `Q/P` wrapper can
write the cleared-side diagonal using `post.weight (J+1)` and
`post.weight rowLevel`. This is the intended single-count normalization of the
source's `D_J = uD'_J` and `b'_i = u b_i` displays. It still assumes the
successor recurrence state is supplied and does not prove the chart produces
that state, nor arbitrary-pivot coverage, regularity/Jacobian facts, exponent
updates, transition invariants, or the printed Case 2 vector repair.

The repeated post-state assumptions in this Case 2 recurrence layer are now
packaged as `IntroducedLabelRecurrenceState.Case2SuppliedPostData`. This is a
recurrence-local package: old labels keep levels and variables, and the new
label `(S,J+1)` has level `J` and variable `u`. The package intentionally does
not contain the old gap, displayed pivot bounds, or corrected certificate. Lean
now proves that `case2Succ` supplies the package and adds `_of_postData`
wrappers for the recurrence update, successor residual flatness, displayed
source-substitution, and displayed `Q/P` handoff. This reduces hypothesis
sprawl while preserving the boundary: the supplied post-state is still assumed,
not produced by a chart.

The corrected Case 2 exponent-domain update now has a concrete selected-label
update wrapper. It uses `updateSelectedLabelVector` and
`updateSelectedLabelScalar` to change only `(S,J+1)` to the corrected vector,
numerator, and least value, then applies the existing corrected new-label
domain-extension theorem. This checkpoint deliberately does not use
`Case2SuppliedPostData`: recurrence `level/var` post-data is not evidence that
old exponent vectors or numerators are unchanged.

The corrected Case 2 exponent post-data package is now Lean-proved as
`Case2CorrectedExponentPostData`. It records the six exponent-map equalities
needed for an arbitrary supplied exponent post-state: old vector/numerator/
least-value preservation plus the corrected new vector, numerator, and least
value at `(S,J+1)`. The all-label extension theorem
`IntroducedLabelExponentCertificates.extendDomain_correctedCase2NewLabel_of_postData`
uses the package with a corrected new-label certificate, and the concrete
selected-label update wrapper now factors through it. The recurrence-side
bridge
`IntroducedLabelRecurrenceState.Case2SuppliedPostData.case2Gap_of_leastValueGap_of_correctedExponentPostData`
shows that supplied recurrence post-data plus supplied corrected exponent
least-value data advances the least-value/level bridge and the Case 2 gap. This
is corrected invariant bookkeeping only; it does not prove chart production or
that the corrected vector is the PDF's printed Case 2 vector. Next A4 target:
arbitrary selected-entry Case 2 source-substitution transport, with coverage,
Jacobian, recurrence production, and full `Q/P` transition still out of scope.

The arbitrary selected-entry Case 2 source-substitution transport is now
Lean-proved as finite algebra. `case2ResidualBlockPivotRowOfMem` and
`case2ResidualBlockPivotColOfMem` extract row/column subtype pivots from finite
center membership, and `case2ResidualBlockPivotOfMem_pair` records the paired
source-coordinate equality. The `case2Selected...` API names the normalised
selected matrix, source-substitution matrix, pivot-first diagonal transport,
following-factor reindexing, and transported `Q^-1 C` factor for any supplied
residual-block pivot. The conditional wrappers
`exists_case2SelectedQP_mul_sourceSubstitution_of_forall_dvd` and
`exists_case2SelectedQP_mul_sourceSubstitution_of_flat_weights` apply the
generic pivot-first `Q/P` identity under explicit row-weight divisibility or
flatness. This still does not prove an affine blow-up atlas, chart coverage,
regularity/Jacobian facts, recurrence post-state production, exponent updates,
transition invariants, source comparability, normal crossings, or RLCT
extraction.

The arbitrary selected-entry recurrence handoff is now Lean-proved. The theorem
`exists_case2SelectedQP_mul_sourceSubstitution_of_recurrenceStateGap` feeds an
old packaged recurrence state and `case2Gap` into the arbitrary selected-pivot
`Q/P` wrapper. The corrected-certificate namespace now has arbitrary selected
successor-weight transport and `Q/P` wrappers, including `_of_postData`
versions using `IntroducedLabelRecurrenceState.Case2SuppliedPostData`. The
right-side diagonal is rewritten at the actual selected row level
`case2ResidualRowLevel n S J rowPivot`, not forced back to the displayed
`J+1` row. This remains supplied-pivot/supplied-post-state finite algebra, not
chart production or coverage.

The source-selected pair wrapper is now Lean-proved. The adapter restricts
source-coordinate residual data and source-column following factors to the
Case 2 residual row/column subtypes, then uses
`case2ResidualBlockPivotRowOfMem` and `case2ResidualBlockPivotColOfMem` to
instantiate the arbitrary selected-pivot recurrence-gap and supplied-post-data
wrappers from a supplied pair `p ∈ case2ResidualBlockPivotEntries n S J`. This
is only a source-coordinate usability bridge. It does not prove that Aoyagi
displays non-top-left Case 2 charts, arbitrary-pivot chart coverage,
source-order transition formulas, chart-produced post-data, regularity,
Jacobian facts, exponent transitions, normal crossings, or RLCT extraction.

The finite selected-entry principalization layer is now Lean-proved. The
weighted pivot row operation `P`, the pivot column operation `Q`, and the
displayed inverse `Q^-1` are matrix units with unit determinants. The theorem
`selectedEntryChartMap_centerIdeal_eq_span_singleton` proves that, for any
finite center and supplied pivot in that center, the ideal generated by the
transformed selected-entry center generators is exactly `(u)`. Case 1 and
Case 2 specializations apply this to `case1CenterGenerators` and
`case2ResidualBlockPivotEntries`. This is the elementary ideal-principalization
part of the selected-generator chart story, not affine atlas coverage,
polynomial-coordinate Jacobian control, source-order transition, or
chart-produced recurrence/exponent post-data.

The Case 2 chart-family boundary is now named in Lean. The generic
`SelectedEntryChartFamilyBoundary` packages supplied `ChartRegular` and
`TransitionRegular` predicates for all members of a finite selected-entry
center. `Case2ResidualBlockChartFamilyBoundary` specializes this to
`case2ResidualBlockPivotEntries n S J`. The only new proved source fact is
`case2ResidualBlockPivotEntries_nonempty_of_cont`: under the continuation
hypothesis, the displayed top-left pivot belongs to the residual-block center,
so the finite center is nonempty. The boundary projections deliberately assume,
rather than prove, chart regularity and transition regularity.

The Case 1 chart-family boundary is now named in Lean too.
`Case1CenterChartFamilyBoundary` specializes the same generic boundary to the
finite center consisting of the `Unit` old-exceptional generator and the
actual-width row-strip entries. Lean proves only finite nonemptiness,
right-branch membership, and supplied regularity projections for the old chart
and displayed top-left row-strip pivot. This matches the source-scout verdict:
Aoyagi displays the old-variable chart and top-left selected-entry charts, but
does not enumerate arbitrary selected-entry atlas formulas. The `Unit` branch
still hides an externally chosen old label, so old-label source validity,
minimality, comparability, and transition production remain separate
obligations.

The displayed top-left source-order adapter is now Lean-proved. The new
`WeightedPivotFirstSubstitutionData` package is the generic handoff point after
a selected chart has already been transported to pivot-first coordinates and
weighted. Its theorem applies the existing finite `Q/P` algebra to a supplied
weighted source block; the existential wrapper chooses quotient witnesses from
divisibility. This deliberately avoids claiming Case 1(2) full residual-block
substitution: the row-strip chart and hidden old-variable factorisation must
still supply the weighted source block. The Case 1 helper
`continuationBound_of_colBound` proves only finite width bookkeeping for the
displayed pivot.

The Case 1(2) displayed row-strip weighted source block is now Lean-proved as
finite algebra. The generic `case1RowStripSourceMatrix` takes an already
normalised pre-`Q` matrix `A`, reconstructing source entries as `u*A` on the
row strip and leaving lower residual rows unchanged. The old row-weight
convention `case1RowStripOldWeight` puts the hidden old-variable factor `u`
only below the strip. The theorem `case1RowStrip_diagonal_mul_sourceMatrix`
proves that these two sources of `u` combine to a single post row-weight
factor `u*baseWeight` on every residual row; the pivot-first and
`case1RowStrip_sourceOrder_identity` wrappers feed this equality into the
generic displayed top-left `Q/P` adapter under supplied quotient witnesses.
The Case 1-specific `Case1DisplayedRowStripSuppliedWeightedSourceData` package
adds first-jump/source-column hypotheses and projects displayed continuation
and pivot membership facts, but still does not construct the chart, identify
the hidden old label, prove quotient regularity from recurrence data, or
produce exponent/transition post-data.

The displayed Case 1(2) row-strip quotient layer is now Lean-proved for the
top-left pivot. The new theorems choose right-oriented witnesses for
`u * monomialRec step rowLevel_i = q_i * (u * monomialRec step (J+1))` using
ordinary monomial recurrence divisibility from the displayed pivot row level
`J+1` to every residual row level. The recurrence-state wrapper uses supplied
`IntroducedLabelRecurrenceState` weights, and the source-order wrappers feed
these witnesses into `case1RowStrip_sourceOrder_identity`. This deliberately
does not use the Case 1 first-jump gap as if it were a full Case 2 gap; it
also does not prove arbitrary row-strip pivot quotients, chart production,
hidden old-label factorisation, or exponent/transition post-data.

The displayed Case 1(2) local handoff is now Lean-proved as a supplied
boundary. The source-order theorem rewrites the left diagonal in original
source-recurrence form,
`monomialRec (mulStepAt factoredBase.step u (J+J1))`, while the right diagonal
uses supplied post-state recurrence weights. The boundary also carries the
supplied pre-state exponent certificates, level-tail invariants, and Case 1
displayed row-strip exponent post-data, so `extendExponentDomain` extends the
certificate package to `(S,J+1)`. This is not chart production: the
factored-base state, recurrence post-data, exponent post-data, normalized pivot
block, and hidden old-label source validity remain external.

The selected-old source substitution boundary is now Lean-proved as recurrence
bookkeeping. The generic finite-product update lemmas show that changing one
existing label variable from `old'` to `u*old'` changes exactly the recurrence
factor at that label's level. The Case 1 wrapper
`Case1SelectedOldFactoredBaseData` then proves that the pulled-back source
recurrence after `old = u*old'` satisfies
`source.step = mulStepAt factoredBase.step u (J+J1)`. The row-strip corollary
identifies the old-weight convention with these substituted source weights.
This still assumes the hidden old label and substituted source recurrence; it
does not construct the selected-old chart or identify the `Unit` generator.

The Case 1 source-substituted local handoff is now Lean-proved. The theorem
`Case1DisplayedRowStripSuppliedTransitionBoundary.sourceOrder_identity_substitutedSourceWeights`
combines the displayed row-strip local handoff with the selected-old source
substitution boundary, rewriting the left diagonal from the explicit
`mulStepAt factoredBase.step u (J+J1)` recurrence to supplied `source.weight`
values on residual row levels. The explicit hypothesis
`level = factoredBase.level` is required and intentional: first-jump data and
recurrence-state data still live in separately supplied packages. This is still
a supplied local handoff, not chart production or hidden old-label validity.

The selected-old pullback boundary is now Lean-packaged as
`Case1DisplayedRowStripSelectedOldPullbackBoundary`. It bundles the supplied
selected-old source pullback with the supplied displayed row-strip handoff
specialized to `factoredBase.level`, so downstream source-facing statements no
longer need a separate level-map equality. The projections expose the selected
old source step, `Unit` center-token membership, selected-level facts,
row-strip source-weight rewriting, the source-order identity, and the exponent
domain extension. This is still an assumption interface: it does not construct
the selected-old chart, identify the `Unit` token with `(s0,k0)` from first
principles, or prove chart coverage/regularity/Jacobians.

The selected-old supplied chart-family boundary is now Lean-packaged as
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary`. It combines
the selected-old pullback boundary with a supplied
`Case1CenterChartFamilyBoundary`, then projects chart regularity for the old
`Unit` token and displayed top-left row-strip pivot, and transition regularity
in both directions. It also carries through the source-label, source-step,
source-order, and exponent-domain projections. This is a supplied regularity
interface, not chart production or atlas coverage.

The selected-old source-coordinate wrapper is now Lean-proved. It restricts a
source-coordinate residual function `Nat x Nat -> R` to the residual block and
a source following factor `Nat -> tau -> R` to the residual columns, then
applies the selected-old supplied chart-family boundary under the displayed
pivot normalization `residual (J+1,J+1)=1`. The checkpoint also projects the
finite selected-entry principalization facts for the displayed top-left
row-strip pivot: the selected variable occurs, divides all transformed finite
center generators, and generates the transformed finite center ideal. It does
not project selected-old `Unit` principalization with this same variable,
because `u` is the displayed row-strip pivot factor in `old = u*old'`. This
remains an adapter/projection layer; it does not construct the selected-old
chart, source pullback, atlas coverage, chart post-data, Jacobian, normal
crossings, RLCT, or a transition invariant.

The Case 1(1) selected-old chart source-coordinate identity is now Lean-proved
as elementary row-wise algebra. The new `case1SelectedOldPostWeight` absorbs
the selected old chart denominator on exactly the Case 1 row strip, and
`case1SelectedOld_diagonal_mul_sourceMatrix` proves
`diag(baseWeight) * sourceMatrix = diag(postWeight) * dividedMatrix`. The
source-coordinate specialization uses `case2SourceResidualBlock residual`,
with prefix-minimum residual rows and actual-width residual columns kept
separate. This is separate from displayed Case 1(2): it does not introduce the
label `(S,J+1)`, does not use the displayed pivot `u_(S,J+1)`, and does not
assert `Q/P`, chart production, coverage, Jacobians, normal crossings, RLCT, or
a transition invariant. Xhigh review found only a low docstring hazard in the
shared row-strip helpers; the helper comments now explicitly distinguish the
Case 1(1) old denominator from the Case 1(2) displayed pivot.

The Case 1(1) selected-old same-domain boundary is now Lean-proved as a
supplied interface. `Case1SelectedOldLowerTailExponentPostData` records the
selected old label lower-tail vector, actual-width numerator increment
`J1*(n(S+1)-J)`, least value `J`, and unchanged non-selected introduced labels.
The post-data theorem reuses the existing same-domain lower-tail certificate
update, and `Case1SelectedOldSuppliedSameDomainBoundary` projects both the
same-domain exponent certificate update and the row-wise source-coordinate
identity. It remains strictly at `(S,J)`: no `(S,J+1)`, no displayed
Case 1(2) pivot, no `Q/P`, no chart production, no coverage/regularity,
Jacobian, normal crossings, RLCT, or transition invariant. Xhigh review passed
with no findings; residual risk is the intended one that the scalar `u` is not
type-level identified with the actual coordinate `u_(s0,k0)` and source
validity remains future integration work.

The Case 1(1) selected-old recurrence post-weight calculation is now
Lean-proved as standalone algebra over a supplied base recurrence. Moving the
selected old factor from level `J+J1` down to level `J` yields exactly the
piecewise strip post weights on active residual rows; below the strip both old
and lowered recurrences already contain the factor. The source-coordinate
matrix corollary writes the right diagonal as the lowered recurrence. This
does not construct the base recurrence from source data, does not prove a
recurrence-state post-data theorem, and still avoids `(S,J+1)`, the displayed
Case 1(2) pivot, `Q/P`, chart production, coverage/regularity, Jacobians,
normal crossings, RLCT, and transition invariants. Xhigh review passed with no
findings.

The Case 1(1) selected-old lowered-recurrence boundary is now Lean-packaged as
a supplied source-facing interface. It carries pre/post recurrence states over
the same `(S,J)` domain, a supplied base recurrence, and fields
`pre.step = mulStepAt baseStep u (J+J1)` and
`post.step = mulStepAt baseStep u J`. The projections rewrite the
Case 1(1) source-coordinate identity from `pre.weight` to `post.weight`, and
re-export the same-domain exponent update. This still does not construct the
selected-old chart, derive the base recurrence or states from source
coordinates, produce chart post-data, introduce `(S,J+1)`, use the displayed
Case 1(2) pivot, assert `Q/P`, or prove coverage/regularity, Jacobians,
normal crossings, RLCT, or a transition invariant. Xhigh review passed with no
findings.

The Case 1(1) selected-old `Unit` chart-family boundary is now Lean-packaged
as a supplied interface. `Case1SelectedOldUnitSuppliedChartFamilyBoundary`
combines the selected-old lowered recurrence boundary with the supplied finite
Case 1 chart-family boundary. The projections keep the old-label facts in the
carried lowered recurrence data, while the finite center chart token is only
`Sum.inl ()`. The package exposes supplied chart regularity for this token,
supplied transition regularity from/to any finite Case 1 center generator,
finite selected-entry principalization by the selected-old scalar, the
pre/post recurrence source identities, and the same-domain exponent update.
It remains over `(S,J)`: no `(S,J+1)`, no displayed Case 1(2) pivot, no raw
source chart construction, no derivation of `baseStep` or pre/post states from
coordinates, no `Q/P`, no coverage/regularity proof from coordinates, no
Jacobian, no normal crossings, no RLCT, and no transition invariant. Xhigh
reviews passed with no findings; residual risk is the intended one that Lean
does not derive the coordinate identification `u = u_(s0,k0)` in this wrapper.

The Case 1(1) selected-old erased-base source model is now Lean-proved as
finite-product recurrence bookkeeping. `IntroducedLabelRecurrenceState.erasedStep`
defines the recurrence factor with `(s0,k0)` removed from the introduced-label
product. `Case1SelectedOldLevelMoveData` records the source-shaped level move:
the selected old label moves from `J+J1` to `J`, keeps the same variable `u`,
and all non-selected introduced labels keep their level and variable data.
Lean proves the erased base recurrence is unchanged and derives both step
equalities previously supplied to the lowered boundary. The constructor
`Case1SelectedOldLoweredRecurrenceBoundary.of_levelMoveData` instantiates the
existing boundary with `baseStep = pre.erasedStep s0 k0`. This still does not
construct the selected-old chart, infer `(s0,k0)` from the `Unit` token, prove
chart-produced moved-level data, introduce `(S,J+1)`, use Case 1(2), assert
`Q/P`, or prove coverage/regularity, Jacobians, normal crossings, RLCT, or a
transition invariant.

The Case 1(1) selected-old concrete level move is now Lean-proved. The
same-domain post-state `case1SelectedOldLevelMove` lowers only the selected
old label's recurrence level to `J`; recurrence-label variables are unchanged,
and non-selected levels are unchanged. Under selected introducedness and
`pre.level s0 k0 = J+J1`, it supplies the existing
`Case1SelectedOldLevelMoveData`, and
`Case1SelectedOldLoweredRecurrenceBoundary.of_sameDomain_case1SelectedOldLevelMove`
instantiates the erased-base boundary with the concrete post-state. This is a
canonical recurrence-state witness, not raw chart production: source residual
matrix coordinates are still handled by the row-strip identity, and chart
coverage/regularity/Jacobians/normal crossings/RLCT/full transition invariance
remain open.

The Case 1(1) selected-old Unit concrete level-move wrapper is now Lean-proved.
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.of_sameDomain_case1SelectedOldLevelMove`
packages the concrete lowered recurrence boundary with a supplied
`Case1CenterChartFamilyBoundary`, using
`post = pre.case1SelectedOldLevelMove s0 k0`,
`u = pre.var s0 k0`, and `baseStep = pre.erasedStep s0 k0`. This is only a
boundary-instantiation theorem: chart regularity and transition regularity are
still supplied, and no raw coordinate chart, coverage theorem, Jacobian,
normal-crossing certificate, RLCT extraction, or transition invariant is
proved.

The Case 2 printed mismatch boundary is now Lean-proved as arithmetic
source-gap isolation. `terminalExponent_printedCase2Vector_sub_prefixFormula`
states that the printed vector's terminal exponent differs from the
prefix-minimum Case 2 increment by
`(M^(S)-M(S))*(M^(S+1)-J)`. The equality theorem
`terminalExponent_printedCase2Vector_eq_prefixFormula_iff` keeps the degenerate
zero-column-factor case explicit: equality holds iff `M^(S)=M(S)` or
`M^(S+1)=J`. The continuation corollary
`terminalExponent_case2Printed_ne_corrected_of_prefixDrop_of_cont`
then proves genuine mismatch under `J+1<=M(S+1)`, with `M(S+1)` the prefix
minimum, and `M(S)<M^(S)`. This does not prove a Case 2 transition, erratum,
reachable-state equal-width invariant, chart coverage, Jacobian, normal
crossings, RLCT, or termination.

The displayed Case 1(2) paper `Q/P` adapter is now Lean-packaged as a
paper-facing notation layer over the already supplied source-coordinate
identity. It names the normalized source-coordinate block, the source
row-strip block, `Q`, `Q^-1`, `D''`, `C'`, and `D'''`, proves that `D''` is the
generic post-`Q` block under `residual (J+1,J+1)=1`, and pins the orientation
`D'' * C' = D_chart^pivot * C`. The main theorem
`sourceOrder_identity_sourceCoordinates_paperQP` restates the supplied
source-order identity in this notation. This still does not construct the
displayed chart, raw selected-old pullback, recurrence/exponent post-data,
chart coverage, regularity from coordinates, Jacobian, normal crossings,
RLCT, or a transition invariant. Xhigh Lean/API review passed; source review
confirmed the no-double-counting `u` convention after the local proof repair.

The Case 2 supplied source-selected pivot boundary is now Lean-proved.
`Case2SourceSelectedSuppliedChartFamilyBoundary` packages a supplied source
pivot membership proof, source-coordinate residual/following-factor
restriction, supplied chart-family regularity predicates, corrected exponent
post-data, recurrence post-data, finite selected-entry principalization, and
the source-selected arbitrary-pivot `Q/P` identity. It derives the corrected
new-label certificate and old/successor Case 2 gap bookkeeping from
prefix-bound and least-value hypotheses. It remains a supplied boundary, not
chart production or coverage; non-top-left source-order transition formulas,
chart-produced post-data, Jacobians, normal crossings, RLCT extraction,
termination, and the printed-vector mismatch remain open.

The Case 2 displayed concrete-update boundary is now Lean-proved.
`Case2DisplayedSuppliedChartFamilyBoundary` specializes the supplied
source-selected boundary to Aoyagi's displayed top-left pivot `(J+1,J+1)`;
the continuation bound supplies the finite residual-block membership.
`of_case2Succ_updateSelected` chooses the concrete recurrence successor
`pre.case2Succ u` and the corrected selected-label exponent update package,
and the displayed boundary projects the source-coordinate displayed `Q/P`
identity. This is still assignment bookkeeping, not chart production:
chart-family predicates remain supplied, and chart-produced post-data,
coverage, coordinate regularity, Jacobians, normal crossings, RLCT extraction,
termination, and the printed-vector mismatch remain open.

The Case 2 displayed source-chart map is now Lean-proved. The new
`case2DisplayedSourceChartMap` and `case2DisplayedSourceNormalizedMap` name
Aoyagi's displayed top-left substitution in source coordinates:
`(J+1,J+1)` maps to `u`, off-pivot residual entries map to `u` times their
residual coordinate, and the normalised pivot is `1`. The restricted source
blocks `case2DisplayedSourceSubstitutionBlock` and
`case2DisplayedSourceNormalizedBlock` are proved equal to the existing
displayed block-indexed substitution and normalised matrices after
`case2SourceResidualBlock` restriction; the dependent bridge is
`case2Displayed_source_pair_eq_pivot_iff`. The transported following factor
`case2DisplayedSourceTransportedFollowingFactor` is proved to be the existing
displayed `Q^-1 C` after source restriction, and
`Case2DisplayedSuppliedChartFamilyBoundary.sourceDisplayedQP_sourceChartMap`
rewrites the displayed supplied `Q/P` theorem in these source-chart names.
This is a chart-map adapter only: no chart coverage, non-top-left formula,
chart-produced recurrence/exponent post-data, coordinate regularity, Jacobian,
normal crossings, RLCT extraction, termination, transition invariant, or
printed-vector repair is proved.

The Case 2 displayed center count is now Lean-proved. The new lemmas
`case2ResidualBlockRows_card`, `case2ResidualBlockCols_card`, and
`case2ResidualBlockPivotEntries_card` prove that the displayed Case 2
residual-block coordinate set has cardinality
`(prefixMinNat n S - J) * (n (S+1) - J)`, keeping prefix-minimum residual rows
separate from actual-width residual columns. The named integer expression
`correctedCase2NewLabelNumerator` is proved equal to this coordinate count
under explicit bounds and under displayed continuation. This supports the
corrected scalar update as a selected-coordinate count only: it is not a
Jacobian exponent, chart-produced post-data, chart coverage, normal-crossing
certificate, RLCT extraction, termination, transition invariant, or
printed-vector repair.

The Case 2 corrected post-data center-count projection is now Lean-proved. The
new generic projections
`Case2CorrectedExponentPostData.numerator_new_eq_correctedNumerator` and
`Case2CorrectedExponentPostData.numerator_new_eq_card_of_cont` say that the
supplied corrected exponent post-data assigns the new label `(S,J+1)` the
corrected numerator, and under displayed continuation that numerator is the
cardinality of `case2ResidualBlockPivotEntries n S J`. The source-selected and
displayed supplied boundary packages export the same facts as
`numerator_new_eq_correctedNumerator` and `numerator_new_eq_card`. This is
only a projection from supplied corrected post-data to the selected-coordinate
count; it does not prove chart-produced post-data, a Jacobian/volume exponent,
coverage, coordinate regularity, normal crossings, RLCT extraction,
termination, transition invariance, or printed-vector repair.

The Case 2 displayed source-chart principalization is now Lean-proved in
source-chart names. The new global lemmas
`case2DisplayedSourceChartMap_value_mem`,
`case2DisplayedSourceChartMap_center_dvd`, and
`case2DisplayedSourceChartMap_centerIdeal_eq_span_singleton` say that, for the
displayed top-left source-coordinate chart map, `u` occurs as the transformed
value at `(J+1,J+1)`, every transformed finite residual-block center value is
divisible by `u`, and the generated finite center ideal is `Ideal.span {u}`.
The displayed supplied boundary package exports the same facts as
`displayedPivot_sourceChartMap_value_mem`,
`displayedPivot_sourceChartMap_center_dvd`, and
`displayedPivot_sourceChartMap_centerIdeal_eq_span_singleton`. This is only
finite residual-block center ideal algebra for the displayed pivot; it is not
arbitrary-pivot source chart data, not a loss/Kullback ideal or analytic germ
statement, and not chart production, atlas coverage, coordinate regularity,
Jacobian/volume arithmetic, normal crossings, RLCT extraction, termination,
transition invariance, or printed-vector repair.

The Case 2 displayed successor gap projections are now Lean-proved. The new
displayed-boundary projections
`Case2DisplayedSuppliedChartFamilyBoundary.postLevelInvariants`,
`Case2DisplayedSuppliedChartFamilyBoundary.successorLeastValueGap`, and
`Case2DisplayedSuppliedChartFamilyBoundary.postCase2Gap` forward the
corresponding source-selected supplied-boundary successor facts through
`sourceSelectedBoundary`. This is only API bookkeeping: supplied recurrence
post-data and supplied corrected exponent post-data still provide the
successor invariants, and the displayed chart is not proved to produce those
post-data.

The Case 2 source-selected chart-map adapter is now Lean-proved. The new
source-coordinate maps
`case2SourceSelectedChartMapOfMem` and
`case2SourceSelectedNormalizedMapOfMem` are defined for a supplied
residual-block pivot `p in case2ResidualBlockPivotEntries n S J`; their
residual-block restrictions agree with the existing source-selected
substitution and normalized matrices. The source-selected supplied boundary
exports the existing arbitrary-pivot `Q/P` theorem as
`Case2SourceSelectedSuppliedChartFamilyBoundary.sourceSelectedQP_sourceChartMap`.
This is only finite source-coordinate adapter algebra for a supplied pivot. It
does not prove atlas coverage, does not claim Aoyagi displays non-top-left
source charts, and does not prove chart-produced recurrence/exponent
post-data, coordinate regularity, Jacobian/volume arithmetic, normal
crossings, RLCT extraction, termination, transition invariance, or printed
vector repair.

The Case 2 displayed source-chart recurrence boundary is now Lean-proved. The
new theorems
`case2DisplayedSourceChartMap_case2Succ_postData`,
`case2DisplayedSourceChartMap_case2Succ_weight_update`, and
`case2DisplayedSourceChartMap_case2Succ_residualRowWeight_update` say that the
concrete successor recurrence state `pre.case2Succ u` can be read as using the
displayed source chart pivot value as its new variable, and that all weights
from row `J+1` onward are multiplied by that pivot value. This is recurrence
bookkeeping only: it uses the displayed chart map only through its pivot value
and does not prove affine chart construction, chart-produced exponent
post-data, Jacobian/volume arithmetic, coverage, coordinate regularity, normal
crossings, RLCT extraction, termination, transition invariance, or printed
vector repair.

The Case 2 displayed source-chart boundary constructor is now Lean-proved.
`Case2DisplayedSuppliedChartFamilyBoundary.of_sourceChartMap_case2Succ_updateSelected`
packages the displayed supplied boundary with scalar equal to
`case2DisplayedSourceChartMap(...)(J+1,J+1)` and post state
`pre.case2Succ` of that same pivot value. This is a source-facing wrapper over
the concrete displayed boundary and the recurrence pivot theorem; the corrected
exponent post-data and chart-family regularity predicates are still supplied.
It does not prove chart-produced post-data, non-top-left displayed charts,
coverage, coordinate regularity, Jacobian/volume arithmetic, normal crossings,
RLCT extraction, termination, transition invariance, or printed-vector repair.

The Case 2 post-pivot exhaustion boundary is now Lean-proved. The new finite
domains `case2PostPivotRows`, `case2PostPivotCols`, and
`case2PostPivotEntries` record the lower-right row range `J+2..M(S)`, column
range `J+2..M^(S+1)`, and product domain after the displayed pivot. Lean proves
their cardinals and shows that `case2PostPivotEntries` is nonempty iff the
next continuation bound `J+2 <= prefixMinNat n (S+1)` holds. If that next
bound fails, at least one side is empty and the lower-right entry set is
empty; if the current pivot was valid but the next is not, then the frontier
prefix minimum is exactly `J+1`. This is finite domain bookkeeping only, not
the `S+1` advance transition, chart production, Jacobian arithmetic,
termination, transition invariance, or printed-vector repair.

The Case 2 displayed pivot-complement exhaustion boundary is now Lean-proved.
The new equivalences identify the displayed pivot row and column complements
with the old post-pivot domains `J+2..M(S)` and `J+2..M^(S+1)`. If the
displayed pivot is valid and the next continuation bound fails, Lean proves
that one complement type is empty. Matrix-level corollaries then show the
lower-right complement matrix type is subsingleton, and any such matrix is
zero over a type with zero. This is only lower-right domain-vacuity
bookkeeping. It is not Aoyagi's full terminal statement
`D'''_J = (1,0,...,0)` or its transpose, and it does not construct `D'''_J`,
the whole post-`Q/P` zero pattern, `C'^(S+1)`, the `S+1` recurrence/exponent
state, chart production, coverage, Jacobians, normal crossings/RLCT,
termination, transition invariance, or printed-vector repair.

The Case 2 stage-relabel domain audit is now Lean-proved. The frontier split
`case2_next_frontier_currentPrefixMin_or_nextWidth_eq_of_cont_of_not_next`
says that, when the displayed pivot is valid and the next continuation bound
fails, the terminal frontier comes from either `prefixMinNat n S = J+1` or
`n(S+1)=J+1`. The introduced-label domains at old `(S,J+1)` and `(S+1,0)` are
proved equal under the actual-width side condition `n(S+1)=J+1`. The theorem
`introducedLabel_succStage_zero_extra_witness_of_nextWidth_ge` records the
row-side obstruction: if `J+2 <= n(S+1)`, then `(S,J+2)` is introduced at
`(S+1,0)` but not at old `(S,J+1)`. This is only finite label-domain
bookkeeping, not an `S+1` transition theorem, terminal `D'''` theorem,
following-factor construction, chart-production result, Jacobian calculation,
normal-crossing/RLCT result, termination theorem, transition invariant, or
printed-vector repair.

The Case 2 displayed cleared-block vacuity corollary is now Lean-proved.
`case2DisplayedClearedBlock_eq_pivotOnly_of_not_next_cont` applies the
displayed pivot-complement matrix-vacuity theorem to the already-cleared
pivot-first block, proving
`weightedPivotClearedBlock (D - x*y) = weightedPivotClearedBlock 0` under
displayed pivot validity and failed next continuation. This is only the
lower-right vacuity part of the terminal block shape in pivot-first
coordinates. It does not construct Aoyagi's full `D'''_J` terminal branch,
choose the row-vs-column presentation, construct `C'^(S+1)`, build the
`S+1` recurrence/exponent state, prove chart production or coverage,
Jacobian arithmetic, normal crossings/RLCT, termination, transition
invariance, or printed-vector repair.

The Case 2 displayed cleared-block following-factor absorption scaffold is
now Lean-proved. The generic identity
`weightedPivotClearedBlock_zero_mul_verticalBlock` says that a pivot-only
cleared block multiplied by a pivot-first following factor keeps only the top
row. The displayed specialization combines this with the failed-continuation
cleared-block vacuity theorem. This is only block multiplication in
pivot-first coordinates; it does not construct or identify `C'^(S+1)`,
construct the full terminal `D'''_J` branch, choose the row-vs-column
presentation, build `S+1` post-data, prove chart production or coverage,
Jacobians, normal crossings/RLCT, termination, transition invariance, or
printed-vector repair.

The Case 2 displayed paper terminal absorption layer is now Lean-proved.  The
new paper-facing names `case2DisplayedPaperDchart`,
`case2DisplayedPaperQ`, `case2DisplayedPaperQinv`,
`case2DisplayedPaperDpp`, `case2DisplayedPaperCprime`, and
`case2DisplayedPaperDppp` mirror Aoyagi's displayed Case 2 `Q/P` notation.
The supplied displayed source-chart `Q/P` identity is re-exported in that
notation as
`Case2DisplayedSuppliedChartFamilyBoundary.sourceDisplayedQP_sourceChartMap_paperQP`.
The generic ideal lemma `matrixEntryIdeal_sumElim_zero_bottom` proves that
zero bottom rows do not affect a matrix-entry ideal, and
`matrixEntryIdeal_case2DisplayedPaperDppp_mul_Cprime_eq_top_of_not_next_cont`
applies the failed-continuation cleared-block theorem to show that
`D''' * C'` has the same matrix-entry ideal as the pivot row of `C'`.  This
is not a construction or identification of Aoyagi's next-stage
`C'^(S+1)`, not a source-order row/column terminal presentation, and not
chart production, Jacobian arithmetic, normal crossings/RLCT, termination,
transition invariance, or printed-vector repair.

The Case 2 displayed terminal stack layer is now Lean-proved.  The generic
entry-ideal facts `matrixEntryIdeal_sumElim_eq_sup` and
`matrixEntryIdeal_sumElim_congr_bottom` say that stacking row blocks gives
the supremum of entry ideals and permits replacement of the bottom block by
one with the same entry ideal.  The displayed specialization
`matrixEntryIdeal_case2DisplayedPaperTerminalStack_eq_topStack_of_not_next_cont`
stacks an arbitrary supplied old top block `Cold` over the stopped terminal
bottom block and proves
`<entries([Cold; D''' * C'])> = <entries([Cold; C0])>`, where `C0` is the top
pivot row of `C'`.  This still does not identify `Cold` with the source old
top rows or `[Cold;C0]` with Aoyagi's full `C'^(S+1)`, and it remains outside
the diagonal-weighted full terminal product ideal, chart production, Jacobian
arithmetic, normal crossings/RLCT, termination, transition invariance, and
printed-vector repair.

The Case 2 displayed weighted terminal-product layer is now Lean-proved.  The
suffix-aware entry-ideal facts `sumElim_mul`,
`matrixEntryIdeal_sumElim_zero_bottom_mul`, and
`matrixEntryIdeal_sumElim_congr_bottom_mul` let the supplied following product
`F` be multiplied before deleting zero lower rows.  The displayed
specialization
`matrixEntryIdeal_case2DisplayedPaperWeightedTerminalProduct_eq_topStack_of_not_next_cont`
proves
`<entries((blockdiag(Wold,diag(b0,b))*[Cold;D'''*C'])*F)> =
<entries([(Wold*Cold)*F;(b0*C0)*F])>` under failed next continuation.  This
keeps the pivot weight `b0` and does not assume it is a unit. It still does
not identify `Cold`, `Wold`, or `F` with source old top rows, source diagonal
weights, or the source remaining product, does not identify the right hand
side with Aoyagi's `C'^(S+1)`, and remains outside source-order terminal
presentation, chart production, Jacobian arithmetic, normal crossings/RLCT,
termination, transition invariance, and printed-vector repair.

The Case 2 displayed source-terminal candidate layer is now Lean-proved.  The
definitions `case2DisplayedPaperTerminalWeight` and
`case2DisplayedPaperTerminalCnext` name the source-order pieces, and
`case2DisplayedPaperTerminalCprimeCandidate` names their product
`(blockdiag(Wold,[b0]) * [Cold;C0]) * F`, keeping the weight `b0` outside the
unweighted stack.  The expansion theorem identifies it with the expanded stack
from the previous checkpoint.  The supplied-boundary wrapper
`Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceDisplayedWeightedTerminalProduct_entryIdeal_eq_topStack_of_not_next_cont`
then combines the supplied displayed source-chart `Q/P` identity with the
stopped terminal absorption, sourcing `b0` from `post.weight (J+1)` while
leaving `Atop`, `Ctop`, and `F` supplied.  This still does not identify those
supplied objects with Aoyagi's actual old weights, old top rows, or remaining
product, and does not prove `[Ctop;C0]` is source-produced `C'^(S+1)`.

The Case 2 displayed terminal source-model layer is now Lean-proved.  The new
structure `Case2DisplayedSuppliedActualWidthTerminalSourceModel` packages
supplied `Atop`, `Ctop`, and `F` together with actual next-width exhaustion
`n(S+1)=J+1`.  Its projections name the supplied source-order terminal
candidate `(blockdiag(Atop,[b0]) * [Ctop;C0]) * F`.  The model derives failed
next continuation and the finite introduced-label-domain equality
`introducedLabelFinset L n S (J+1) = introducedLabelFinset L n (S+1) 0`.
The supplied-boundary wrapper
`Case2DisplayedSuppliedChartFamilyBoundary.exists_weightedTerminalProduct_entryIdeal_eq_terminalProductCandidate_of_actualWidth`
then applies the previous terminal theorem using
`model.not_next_cont_of_actualWidth_exhausted`.  This is only a supplied
candidate source model: the label-domain equality is not recurrence/exponent
post-data over `(S+1,0)`, and the result does not prove that `Atop`, `Ctop`,
`F`, or `[Ctop;C0]` are source-produced.

The actual-width terminal relabel is now Lean-proved as supplied-data
bookkeeping.  Generic lemmas relabel all-label exponent certificates and
`leastValue = level` invariants from old `(S,J+1)` to `(S+1,0)` under
`n(S+1)=J+1`.  The copied recurrence state keeps the old post-state `level`
and `var`, and the finite-product `step` and row `weight` agree under the
same domain equality.  Displayed-boundary projections expose the relabelled
post-state, level invariant, and exponent-domain certificate.  This is not
chart production, not source-produced `C'^(S+1)`, not automatic transport of
Case 2 gap/tail data, and not normal-crossing/RLCT extraction.

The terminal relabel-weight candidate bridge is also Lean-proved.  It restates
the stopped supplied terminal entry-ideal theorem with surviving scalar
`terminalRelabelPost.weight(J+1)` instead of `post.weight(J+1)`, using
actual-width exhaustion to derive both failed next continuation and weight
equality.  The source-model wrapper is intentionally specialized to
`b0 = terminalRelabelPost.weight(J+1)` to avoid dependent transport between
model types.  The source old-top/source suffix theorem also has the same
relabelled scalar form when a terminal `Cterm` bridge is supplied.  This is
presentational API only; `Atop`, `Ctop`, `F`, and `Cterm` remain supplied, and
no source-produced `C'^(S+1)` or transition invariant is proved.

The displayed source-chart terminal model constructor is now Lean-proved.  It
instantiates `of_sourceChartMap_case2Succ_updateSelected`, so recurrence
post-data are the concrete `case2Succ` state for the displayed pivot value and
exponent post-data are the corrected selected-label overrides, then applies
the actual-width terminal relabel-model wrapper.  The terminal model is
indexed by the concrete relabelled post-state weight.  This removes arbitrary
post-data from this wrapper, but chart-family predicates plus `Atop`, `Ctop`,
and `F` remain supplied; no source-produced `C'^(S+1)` is proved.

The actual-width column-exhaustion fact is now Lean-proved.  Under
`n(S+1)=J+1`, the post-pivot residual columns `J+2..n(S+1)` are empty, so the
displayed pivot's column complement is empty.  The actual-width terminal
source model exports this fact.  This identifies the exhausted side only; it
does not construct source-produced terminal following data.

The current-prefix row-exhaustion companion is now Lean-proved.  Under
`prefixMinNat n S=J+1`, the post-pivot residual rows
`J+2..prefixMinNat n S` are empty, so the displayed pivot's row complement is
empty.  This is independent of actual-width exhaustion and is not projected
from the actual-width terminal source model.

The source old-top/suffix specialization is now Lean-proved.  It defines the
old top row type `1..J`, the old top diagonal `diag(pre.weight i)`, and the old
top source block `C(i,t)` for `i=1..J`, then specializes the stopped terminal
entry-ideal theorem to these source-shaped old top data.  The suffix `F`
remains supplied; no source-produced `C'^(S+1)` or suffix matrix chain is
constructed.

The source suffix-chain checkpoint is now Lean-proved.  The new
`MatrixChain.lean` module defines `paperMatrixChain`, with right-extension
recursion `chain(i,p+1)=chain(i,p)*C(p)`, plus source-layer/source-edge index
wrappers and `sourceSuffixProduct` for Aoyagi's
`prod_{s=S+2}^L C^(s)`.  The stopped source old-top theorem is instantiated
with this named suffix product as
`exists_sourceDisplayedOldTopSourceSuffixProduct_entryIdeal_eq_of_not_next_cont`.
This still does not construct the source-produced terminal stack
`C'^(S+1)`; it only replaces the abstract suffix matrix by the raw right
matrix-chain product.

The source terminal product candidate checkpoint is now Lean-proved.  It adds
`matrixEntryIdeal_submatrix_equiv`, the source terminal row type `1..J+1`, and
the equivalence from old rows plus the surviving pivot row to that source row
type.  The source-row `C'` and terminal product are named as candidates, with
the product explicitly named
`case2DisplayedSourceTerminalProductReindexedCandidate` because it is defined
by row-reindexing the existing stacked candidate.  The stopped source
old-top/source suffix theorem is restated with this reindexed source-row
candidate on the right.

The source terminal product-form bridge is now Lean-proved as
`case2DisplayedSourceTerminalProductReindexedCandidate_eq_weight_mul_cprimeCandidate_mul`.
It proves that the reindexed candidate is the product of the separately named
source terminal weight and source terminal `C'` candidate, followed by the
supplied suffix.  This closes the product packaging gap, but source production
of Aoyagi's full `C'^(S+1)` remains open.

The terminal-frontier bridges are now Lean-proved.  The new terminal prefix
row type `case2SourceTerminalPrefixRowIndex n S` is `1..M(S+1)`, and under
displayed continuation plus failed next continuation it is equivalent to
`case2SourceTerminalRowIndex J = 1..J+1`.  The source terminal weight,
source terminal `C'`, and terminal product candidates are reindexed onto this
prefix row type, and the stopped source old-top/source suffix theorem is
restated with the prefix-row product candidate.  A supplied terminal-matrix
handoff is also proved: any `Cterm` with the old source rows and the surviving
pivot row equal to the top row of `Q^-1 C` can replace the candidate in the
terminal product.  These row equations are also packaged as the supplied
boundary `SuppliedTerminalCprimeBridge`; the bridge now also rewrites the
terminal-prefix product and the stopped source old-top/source suffix theorem
through the supplied terminal `Cterm`, including the prefix-row form.  Lean now
also expands the top row of Aoyagi's transported following factor `Q^-1 C`
entrywise as `C(J+1,-)` plus the displayed pivot-row sum over the post-pivot
columns.  Under actual-width exhaustion `n(S+1)=J+1`, that post-pivot column
sum is empty, so the terminal `C'` candidate is the original source rows
`1..J+1`; Lean packages this as
`SuppliedTerminalCprimeBridge.of_originalRows_width_next_eq` and specializes
the relabelled old-top/source-suffix theorem to those rows.  The remaining
bridge-construction obligation is therefore for the non-column-exhausted
stopped frontier or for fuller chart-production data beyond this actual-width
subcase.
The row-exhausted side is now also separated.  Current-prefix exhaustion
`prefixMinNat n S=J+1` proves stopped continuation and gives terminal-prefix
source old-top/source suffix wrappers, but its explicit terminal matrix has
row `J+1` equal to the transported top row of `Q^-1 C`, not generally the
original source row.  This keeps the post-pivot column correction visible in
wide-next cases and prevents importing the actual-width recurrence relabel.

The source-chart terminal source-suffix wrappers are now Lean-proved.  They
compose the concrete displayed source-chart constructor
`of_sourceChartMap_case2Succ_updateSelected` with the two stopped terminal
source-suffix theorems.  In the actual-width branch, the terminal product is
rewritten with original source rows `1..J+1` and the relabelled successor
weight.  In the row-exhausted branch, the terminal prefix product is rewritten
with transported rows, keeping row `J+1` as the top row of `Q^-1 C`.  These
wrappers remove arbitrary recurrence/exponent post-data from this narrow
terminal source-suffix API, but `chartFamily`, `C`, and `Ctail` remain supplied;
they are not chart coverage, chart-produced post-data, source-produced
`C'^(S+1)`, Jacobian, normal-crossing/RLCT, termination, or transition
invariance theorems.

The raw source suffix chain split is now Lean-proved as `paperMatrixChain_trans`
in `MatrixChain.lean`: a raw paper-order chain from `i` to `j` splits as the
chain from `i` to `m` times the chain from `m` to `j`.  This gives a stable
cast-free algebraic base for later source-suffix empty/peel wrappers, but it
does not itself state those wrappers.

The actual-width source-chart terminal boundary is now Lean-proved as
`sourceChart_actualWidth_terminalOriginalRowsBoundary`.  It packages the
source-chart terminal source-suffix equality with original rows, the
actual-width relabelled level invariant, and the actual-width relabelled
exponent-domain certificate for `(S+1,0)`.  The theorem is restricted to
`n(S+1)=J+1`; it does not apply to row-exhausted wide-next cases and still does
not prove source-produced `C'^(S+1)`, chart coverage, chart-produced post-data,
Jacobian arithmetic, normal crossings/RLCT, termination, or transition
invariance.

The source suffix utilities are now Lean-proved in `MatrixChain.lean`:
`sourceSuffixProduct_proof_irrel`,
`sourceSuffixProduct_eq_paperMatrixChain`, and
`sourceSuffixProduct_split_at`.  The split theorem states the cast-light form
`sourceSuffixProduct(S)=chain(S+2,T)*chain(T,L+1)` under `S+2<=T<=L+1`.  The
split layer may be an endpoint, but endpoint split identity simplifications
remain unproved.  The terminal-last empty-suffix identity is now the separate
dependent-endpoint theorem `sourceSuffixProduct_terminalLast_eq_cast_one`, not
part of this split utility layer.

The source suffix one-edge peel is now Lean-proved in `MatrixChain.lean`.
The raw theorem `paperMatrixChain_succ_left` peels the first edge from a
nonempty raw chain, and the source wrapper `sourceSuffixProduct_peel` states
that under `S+2<=L`, `sourceSuffixProduct(S)` is the reindexed first source
edge `sourceSuffixFirstEdge(S)` times `sourceSuffixProduct(S+1)`.  This is a
dependent-endpoint wrapper around the supplied edge `C^(S+2)`, not a
chart-production theorem or source-produced terminal matrix.

The arbitrary supplied-suffix terminal wrapper layer is now Lean-proved in
`BlowupArithmetic.lean`.  The new stopped wrappers keep the following product
as an arbitrary matrix `F`, reindex the paper terminal candidate into source
rows, and optionally rewrite through a supplied `SuppliedTerminalCprimeBridge`.
The actual-width variants only use `n(S+1)=J+1` to force stopped continuation,
identify the relabelled pivot weight with the displayed post-state weight, and
specialize the terminal bridge to original rows `1..J+1`.  They do not apply to
row-exhausted wide-next cases and do not produce the suffix or terminal matrix.

The concrete displayed source-chart actual-width boundary now also has an
arbitrary-`F` form.  `exists_sourceChart_oldTopSuppliedSuffix_entryIdeal_eq_originalRowsProduct_of_actualWidth`
and `sourceChart_actualWidth_terminalOriginalRowsSuppliedSuffixBoundary`
compose the displayed source-chart constructor with the arbitrary-`F`
actual-width original-row wrapper.  This fixes the post state to the chart-map
successor and carries the actual-width relabelled level/exponent certificates,
but `F` remains supplied.

The displayed source-chart actual-width boundary now also has a finite-center
principalization package:
`sourceChart_actualWidth_terminalOriginalRowsSuppliedSuffixBoundary_withFiniteCenterIdeal`.
It conjoins the arbitrary-`F` actual-width terminal boundary with the finite
residual-block center facts that `u` is a transformed center value, all
transformed center values are divisible by `u`, and the transformed finite
center ideal is `Ideal.span {u}`.  This is not terminal-product
principalization, chart coverage, source production of `C'^(S+1)`, production
of the following product, or an analytic theorem.  That source-scout target
has now been discharged for the actual-width branch by the terminal-last
identity and wrapper recorded below; it should not be generalized to `F=1`
away from the empty-suffix case, and the row-exhausted wide-next branch remains
separate.

The terminal-last source suffix identity is now Lean-proved in
`MatrixChain.lean` as `sourceLayerIndex_terminalLast` and
`sourceSuffixProduct_terminalLast_eq_cast_one`.  The theorem keeps the
dependent endpoint transport explicit: under `S+1=L`, the lower suffix
endpoint is propositionally equal to the final endpoint, so the empty-chain
identity is an identity matrix transported along that equality.  This is raw
matrix-chain algebra only.

The actual-width identity-following boundary is now Lean-proved as
`sourceChart_actualWidth_terminalOriginalRowsIdentityFollowingBoundary`.  It
is the `F=1` specialization of the arbitrary-following displayed source-chart
actual-width terminal boundary and does not itself prove source suffix
emptiness.  The theorem keeps `n(S+1)=J+1`, the pre-state certificates,
least-value gap, and chart-family interface visible, and leaves row-exhausted
wide-next cases separate.

The actual-width terminal-last boundary is now Lean-proved as
`sourceChart_actualWidth_terminalLastOriginalRowsBoundary`, with helper
entry-ideal lemmas removing the transported terminal-last source suffix.  It
uses both `n(S+1)=J+1` and `S+1=L`, consumes the raw source suffix rather than
an arbitrary supplied following matrix, and packages the same relabelled
level/exponent certificates as the identity-following boundary.  It remains
separate from row-exhausted wide-next behavior because it uses original source
rows.

The row-exhausted terminal-last source-suffix removal is now Lean-proved as
`exists_sourceChart_oldTopTerminalLast_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted`,
with the supplied-boundary companion
`exists_sourceOldTopTerminalLast_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted`.
It uses `prefixMinNat n S=J+1` and `S+1=L`, consumes the raw source suffix, and
keeps the terminal side as transported prefix rows.  It does not identify the
transported pivot row with the original source row, and it does not relabel
recurrence/exponent data to `(S+1,0)`.  No chart coverage, source-produced
`C'^(S+1)`, chart-produced following product, Jacobian arithmetic,
normal-crossing/RLCT extraction, termination, transition invariance, or
printed-vector repair is claimed.

The terminal-last source-chart branches are now also packaged with finite
residual-block center principalization.  The actual-width theorem
`sourceChart_actualWidth_terminalLastOriginalRowsBoundary_withFiniteCenterIdeal`
adds the finite center facts to the terminal-last original-row boundary and
its relabelled certificates.  The row-exhausted theorem
`sourceChart_rowExhausted_terminalLastTransportedPrefixBoundary_withFiniteCenterIdeal`
adds the same center facts to the transported-prefix boundary, without
original-row equality or `(S+1,0)` relabelled certificates.  These are still
finite-center packages only, not terminal-product principalization, chart
coverage, source production, Jacobian arithmetic, normal-crossing/RLCT
extraction, termination, transition invariance, or printed-vector repair.

The first A5 arithmetic sub-slice is now Lean-proved in
`lean/DLNFibre/DLN/Aoyagi/ArithmeticTail.lean`.  It isolates only the integer
numerator algebra in Aoyagi's Lemma 3: `aoyagiLemma3A_eq_min_add` proves
`A(b)=a*ell*(ell-a)+ell^2*(b-a)*(b-a+1)`, `int_mul_succ_nonneg` supplies the
integer nonnegativity, and `aoyagiLemma3A_isLeast_image_Icc` proves the
endpoint-corrected least value over integer `0<=b<=ell-1` under `1<=ell` and
`0<=a<=ell`.  The endpoint cases `a=0` and `a=ell` are named separately.
The equality cases are now also Lean-proved: `aoyagiLemma3A_eq_min_iff` shows
that for `ell!=0`, equality with the lower bound occurs exactly at `b=a` or
`b=a-1`, and `aoyagiLemma3A_eq_min_iff_source_Icc` records the source-interval
truncation.  The finite equality set is now also Lean-proved and counted via
`aoyagiLemma3AMinimizerSet_card`: under `1<=ell` and `0<=a<=ell`, its
cardinality is `1 + if 0<a<ell then 1 else 0`.  This does not prove the
terminal candidate set, the `\tilde t_{s,k}=0` restriction, feasibility of
minimizing exponent chains, Lemma 4, Lemma 5, pole order, normal crossings, or
RLCT extraction.

The first Lemma 5 arithmetic sub-slice is now Lean-proved in
`lean/DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean`.  It isolates only the
finite interval-excess sum: `aoyagiLemma5IntervalExcess` is the closed formula
`min(j, ell-j, a, ell-a)`, `aoyagiLemma5IntervalExcessFiber_eq_excess`
identifies it with a rectangle fiber count, and
`aoyagiLemma5IntervalSize_excess_sum_Icc` proves
`1 + sum_{j=1}^{ell-1}(intervalSize-1)=a*(ell-a)+1` under `1<=ell` and
`a<=ell`.  This is not Lemma 5's chart-family/order-count theorem; the
admissibility, coverage, displayed vector constructions, pole-order
interpretation, normal crossings, and RLCT extraction remain open.

The first Lemma 4 arithmetic sub-slice is now Lean-proved in
`lean/DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`.  The reusable theorem
`twoStepInt_count_eq` and source-shaped wrapper `aoyagiLemma4_twoValueCount_int`
prove that an `ell`-indexed integer family with values only `M-1` or `M` and
sum `ell*(M-1)+a` has exactly `a` high entries and `ell-a` low entries.  The
corollary `aoyagiLemma4_twoValueCount_le_ell` records that the same hypotheses
force `a<=ell`.

The source sum bridge for Lemma 4 is now also Lean-proved in the same module.
`aoyagiLemma4F` names the increment
`F_j=H_(j-1)-H_j+M(S_(j+1))` using zero-indexed `Fin` arrays; the source's
separate definition of `F_1` is encoded by the explicit convention
`H 0 = m 0`.  Under this convention and `H (Fin.last ell)=0`,
`aoyagiLemma4F_sum_eq_selectedSum` proves `sum F_j=sum m`; with Definition 3's
selected-width sum, `aoyagiLemma4F_sum_eq_of_selectedSum_eq_pred_add_a` gives
`sum F_j=ell*(M-1)+a`.  The wrapper
`aoyagiLemma4_twoValueCount_of_terminalH` combines this with the two-value
hypothesis, so the sum identity is no longer a separate assumption for that
finite count.  This still assumes the selected-width sum and the two-value
increment hypothesis; vector admissibility, the proof of the two-value
hypothesis from `Ttilde <= T <= Ttilde'`, correspondence to `lambda`, Lemma 5,
pole order, normal crossings, and RLCT extraction remain open.

The next Lemma 4 bridge is now Lean-proved too.  `highCount_castSucc_add_last_eq_total`
splits a high-count over `Fin (n+1)` into the initial `Fin n` count plus the
last-coordinate indicator.  Therefore
`highCount_castSucc_int_eq_or_eq_pred_of_total` proves that if `a` of all
`n+1` increments are high, the free high-count over the first `n` positions is
`a` or `a-1` over integers.  `aoyagiLemma4_freeHighCount_lemma3A_eq_min_of_totalCount`
feeds this into `aoyagiLemma3A_eq_min_iff`, and the terminal-`H` wrapper
`aoyagiLemma4_terminalH_freeHighCount_lemma3A_eq_min` combines it with the
source sum bridge and the two-value increment hypothesis.  This removes the
finite count-to-Lemma-3 equality-case gap, but it does not prove the two-value
hypothesis, terminal exponent rewriting, vector admissibility, or
correspondence to `lambda`.

The endpoint squeeze in Aoyagi Lemma 4 is now Lean-proved at the terminal
arithmetic level.  `aoyagiLemma4TerminalEndpoint` names the common displayed
endpoint expression for `Htilde_ell` and `Htilde'_ell`; under `a<=ell` and
Definition 3's selected-width sum,
`aoyagiLemma4TerminalEndpoint_eq_zero_of_selectedSum` proves this endpoint is
zero.  `aoyagiLemma4_Hlast_eq_zero_of_terminalEndpoint_bounds` turns supplied
endpoint inequalities into `H_ell=0`, and the wrappers
`aoyagiLemma4_twoValueCount_of_terminalEndpointBounds` and
`aoyagiLemma4_terminalEndpointBounds_freeHighCount_lemma3A_eq_min` feed that
into the existing count and Lemma 3 free-count bridge.  This still assumes the
endpoint sandwich; the formal bridge from `Ttilde <= T <= Ttilde'` to endpoint
inequalities remains open.

A follow-up source check found that the source bridge cannot be taken from
Definition 4 alone.  Definition 4 defines componentwise order on vectors, but
not a unique endpoint-selection map from `T` to `(H_j),(S_j)`.  The nearest
source-facing coordinate relation appears in the Lemma 5 discussion, where
`t^(S_(j+1)-1)=H_j`.  Lean therefore now proves only the conservative
same-coordinate bridge: if lower, middle, and upper endpoint values are all
read from the same coordinate `p`, then componentwise `Tlo <= T <= Thi`
supplies the endpoint sandwich, and the existing endpoint-zero/count wrappers
apply.  Proving that Aoyagi's displayed `Ttilde <= T <= Ttilde'` supplies that
same-coordinate correspondence remains open.

The displayed `Htilde`/`Htilde'` chain arithmetic is now Lean-proved in
`lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`.  This module defines
total selected-width/prefix helpers and finite lower/upper chain wrappers,
proves the `H_0=M(S_1)` convention, proves the high-first and low-first
increment patterns, identifies both terminal values with
`aoyagiLemma4TerminalEndpoint`, and identifies the pointwise chain gap with
`aoyagiLemma5IntervalExcess`.  This is only the finite displayed-chain
arithmetic around Lemmas 4-5; it does not prove vector admissibility, the
source `T -> (H_j),(S_j)` correspondence, same-coordinate hypotheses for the
displayed extremal vectors, arbitrary-vector two-value increments,
chart-family coverage, pole order, normal crossings, or RLCT extraction.

The same module now also proves the finite interval-bound layer recommended by
the follow-up A5 checks.  The lower displayed chain is pointwise below the
upper displayed chain because their gap is the nonnegative Lemma 5
interval-excess.  `aoyagiHtildeIntervalValueSet` packages the integer values
between the two same-coordinate chain entries and proves its cardinality is
`aoyagiLemma5IntervalSize`; membership is equivalent to the same-coordinate
inequalities.  If an intermediate `H`-chain is squeezed between the two
displayed chains, then `H_ell=0`, and the existing Lemma 4 count wrappers apply
under the still-explicit two-value increment hypothesis.  A supplied vector
coordinate map can feed componentwise vector bounds into interval membership,
but no source theorem produces that coordinate map.

The binary prefix-delta bridge for the two-value increment blocker is now
Lean-proved in the same module.  For an arbitrary `H`-chain, define
`D_j=P(j)-H_j-j*(M-1)` using the zero-based inclusive selected-width prefix.
Then `aoyagiLemma4F_eq_pred_add_incrementPrefixDelta` proves
`F_j=(M-1)+(D_(j+1)-D_j)`.  Consequently a supplied hypothesis that all
successive deltas are `0` or `1` gives the two-value increment hypothesis, and
the existing terminal-`H` and chain-bound count wrappers can use that binary
interface.  This does not prove that source exponent vectors or chain bounds
provide binary deltas.

The endpoint/count bookkeeping for the same prefix-delta interface is also
Lean-proved.  With `D_j=P(j)-H_j-j*(M-1)`, the source convention gives
`D_0=0`, terminal `H_ell=0` plus the selected-width sum gives `D_ell=a`, and
the successive deltas telescope to `D_ell-D_0`.  Thus terminal source
hypotheses plus supplied binary deltas give exactly `a` ones and `ell-a`
zeroes among the deltas.  The same count has a chain-bound wrapper using the
already-proved `H_ell=0` consequence, but binary-ness remains an explicit
hypothesis.
Reproduction, statement cards, and reviews are in `threads/05-arithmetic-tail/`.

The same-coordinate `Htilde` value-set count is now also Lean-proved in
`HtildeChainArithmetic.lean`.  The Nat-indexed wrapper is empty outside the
source coordinate range, has Aoyagi's interval size in range, and proves
`1 + sum_{j=1}^{ell-1}(|I_j|-1)=a(ell-a)+1` under `1<=ell` and `a<=ell`.
This remains finite arithmetic only; it does not prove Lemma 5's displayed
vector constructions, chart-family admissibility/coverage, pole-order
interpretation, normal crossings, or RLCT extraction.

The same module now also packages the same-coordinate vector-bound interface
with named binary prefix deltas through to the free-count Lemma 3 minimum.  A
supplied coordinate map reads `Tlo`, `T`, and `Thi` as the lower `Htilde`
chain, the intermediate `H` chain, and the upper `Htilde'` chain.
Componentwise bounds supply the chain bounds, binary prefix deltas supply the
two-valued increments, and the existing Lemma 4-to-Lemma 3 bridge proves the
isolated numerator equality for the free high count.  This removes an API
awkwardness for future source-vector realisation, but it remains conditional:
it does not prove the source `T -> (H_j),(S_j)` correspondence, binary deltas
from source vectors, vector admissibility, terminal exponent rewriting,
correspondence to `lambda`, Lemma 5 chart-family/order count, normal
crossings, or RLCT extraction.  The next source-facing A5 target is still
Aoyagi's displayed Lemma 5 families, especially equations `(3)` and `(4)` on
pp. 26-27.

The first source-facing Lemma 5 audit is now recorded.  Equations `(3)` and
`(4)` on pp. 26-27 are not ready as full source-family theorems: equation
`(3)` needs legal-label and terminal-zero guards, equation `(4)` prints only
`j0<=a` while own-coordinate consistency also needs `j0<=ell-a`, and the
paper does not specify the Case 1(2) chart sequence that turns the displayed
one-step-above values into terminal variables with `tilde t=0`.  Lean now
proves only the equation `(4)` own-coordinate arithmetic sanity check:
under `p<=a` and `p<=ell-a`, the displayed chain gap at `p` is `p`, hence
`Htilde'_p-p=Htilde_p`.  This does not prove legal source labels,
`tilde t=0`, vector admissibility, Lemma 5 order count, normal crossings, or
RLCT extraction.

The next equation `(4)` guard layer is now isolated.  Lean exposes the
interval-excess specialization used by the own-coordinate theorem, proves that
the displayed cutoff `S_(p+ell-a+2)` is in the selected list exactly when
`p+1<=a`, and rewrites the label bounds for `k=Htilde_p+1` as a
prefix-crossing condition `P_p < pM <= P_(p+1)`.  A later Definition 3
tail estimate discharges this label condition; the printed `p<=a` guard still
does not prevent the boundary case `S_(ell+2)`.

The analogous equation `(3)` guard layer is now isolated.  Lean proves that
the special cutoff `S_(ell-a+2)` is selected exactly when `1<=a`, that the
first upper/lower Htilde gap is `1` in the interior case `1<=a` and `a<ell`,
and that the label bounds for `k=Htilde'_1+1` are equivalent to the two width
guards `M-1<=W_1+W_2` and `W_1+2<=M`.  This identifies the one-unit slack
condition missing from the displayed Htilde formulas alone.

One Definition 3 source inequality is now Lean-used rather than merely
recorded as a blocker.  If every selected width satisfies Aoyagi's strict
selected inequality `ell*W_i < sum W`, then under
`sum W=ell*(M-1)+a` and `a<=ell`, each selected width is at most `M-1`.
Consequently the previous prefix satisfies `P_p+1<=pM`, and the tail after
`P_(p+1)` satisfies
`sum_tail <= (ell-p)(M-1)`.  The tail estimate gives
`P_(p+1) >= p*(M-1)+a >= pM` under `p<=a`, so equation `(4)`'s full label
bound `1<=Htilde_p+1<=W_(p+1)` follows for `1<=p`, `p<=a`.  This does not
prove any terminal/vector realisation.

The corrected local equation `(4)` arithmetic package is now Lean-proved:
under Definition 3's selected-width hypotheses plus `1<=p`, `p+1<=a`, and
`p<=ell-a`, the selected cutoff is in range, the own-coordinate value is
`Htilde_p`, and the label `Htilde_p+1` is legal.  This is the strongest
source-faithful local equation `(4)` arithmetic currently available; it still
does not construct the displayed source vector or prove terminal `tilde t=0`.

A conditional source-vector-facing equation `(4)` certificate is now also
Lean-proved.  It introduces selected cutpoints, selected blocks, and a
supplied piecewise branch record matching the displayed equation `(4)` values.
From that supplied record, the theorem derives the own-coordinate value
`T(S_(p+1)-1)=Htilde_p` and the legal label bounds.  The result deliberately
does not assert vector existence, total source-layer coverage, terminal
`tilde t=0`, vector admissibility, the Case 1(2) chart sequence, or Lemma 5
order count.

The Case 2 post-pivot domain handoff is now Lean-proved.  The finite
lower-right domains after deleting the displayed pivot `(J+1,J+1)` are
definitionally the next same-stage residual domains at `(S,J+1)`, and the
next residual center is nonempty iff `J+2 <= prefixMinNat n (S+1)`.  Lean also
has direct equivalences from the displayed pivot row/column complements to the
next residual row/column index types.  This is only finite domain bookkeeping:
it does not produce the next residual matrix or following product, prove chart
coverage or coordinate regularity, compute Jacobians, prove normal
crossings/RLCT, prove termination or transition invariance, or handle the
terminal `(S+1,0)` relabel branch.

The continuing-branch next-block adapter is now also Lean-proved.  It names
the displayed cleared lower-right block `D - x*y` over the next same-stage
residual row/column types, names the tail of `C' = Q^-1 C` over the next
same-stage column type, and proves that the lower rows of `D''' * C'` are the
product of these two supplied objects.  The only continuing-branch
nonemptiness claim uses the explicit bound
`J+2 <= prefixMinNat n (S+1)`.  This is still supplied finite matrix algebra
and reindexing: it does not prove chart production, recurrence/exponent
post-data from coordinates, coverage, coordinate regularity, Jacobian
arithmetic, transition invariance, arbitrary pivot coverage, terminal
relabeling, normal crossings/RLCT, or printed-vector repair.  Next A4 target:
connect this adapter to the corrected supplied source-chart boundary and keep
stronger chart-production claims behind an explicit source/API audit.

The displayed source-chart post-pivot boundary now connects that supplied
next-block adapter to the corrected displayed source-chart post-data boundary.
From any supplied displayed boundary, Lean projects the lower-row
`D''' * C'` identity over the same `(S,J+1)` successor domains and preserves
the explicit next-center nonempty bound.  The concrete source-chart package
instantiates the boundary constructor with post state `pre.case2Succ` at the
displayed source-chart pivot value and conjoins the product identity with
corrected post-data projections: exponent-domain extension, post
level/least-value invariants, successor least-value gap, and successor
recurrence gap.  This is still supplied-data compatibility, not chart
production, atlas coverage, transition invariance, Jacobian arithmetic,
normal crossings/RLCT, arbitrary pivot coverage, terminal relabeling, or
printed-vector repair.

The following-factor part of that boundary has one more elementary closure:
Lean now proves that the lower tail of `C' = Q^-1 C` is unchanged.  After
reindexing the displayed pivot-column complement to the next same-stage
residual-column domain, `case2DisplayedPostPivotFollowingFactor` is exactly
`case2SourceFollowingFactor` at `(S,J+1)`.  This is finite block algebra for
`Q^-1 = [1 y; 0 I]` and actual-width column reindexing only.  It is not a
source production theorem for the full next `C'^(S+1)`, recurrence/exponent
post-data, chart-family boundary, transition invariant, Jacobian, normal
crossing, RLCT extraction, arbitrary pivot coverage, terminal relabeling, or
printed-vector repair.

Combining those two facts is now also Lean-proved.  The lower-row product
`D''' * C'`, reindexed to the next same-stage row domain, is rewritten as
`case2DisplayedPostPivotResidualBlock` times
`case2SourceFollowingFactor (J := J+1) C`; the supplied-boundary projection
and concrete corrected-post-data package expose the same identity.  This
removes the transported-tail nuisance adapter but keeps the same boundary:
no chart production, successor chart-family construction, full
source-produced `C'^(S+1)`, transition invariant, chart coverage, Jacobian,
normal crossing, RLCT extraction, terminal relabeling, arbitrary pivot
coverage, or printed-vector repair is claimed.

The reverse pivot-first coordinate direction for the displayed Case 2
following factor is now Lean-proved as finite matrix algebra.  Given an
arbitrary chart-coordinate following matrix `Cprime`, Lean defines the
constructed old pivot-first following factor as `Q*Cprime`, proves
`Q^-1*(Q*Cprime)=Cprime`, and rewrites `D''*Cprime` as
`D_chart*(Q*Cprime)`.  This moves one step from adapter to coordinate algebra
without constructing a total source-coordinate function `N -> tau -> R`,
successor chart family, recurrence/exponent post-data, transition invariant,
Jacobian, normal crossing, RLCT extraction, arbitrary pivot coverage,
terminal relabeling, or printed-vector repair.

That reverse coordinate direction is now connected to the displayed Case 2
`Q/P` product identity.  For a free pivot-first chart-coordinate matrix
`Cprime`, Lean constructs the old following factor as `Q*Cprime`, applies the
existing row-operation theorem, and rewrites `Q^-1*(Q*Cprime)` back to
`Cprime`.  The supplied-boundary conclusion is
`(P * weighted source-substituted block) * (Q*Cprime) =
(weighted D''') * Cprime`.  This is still finite product algebra below the
supplied-boundary interface: no total source-coordinate following function,
source-produced next `C'^(S+1)`, recurrence/exponent post-data production,
successor chart family, transition invariant, Jacobian, normal crossing, RLCT
extraction, arbitrary pivot coverage, terminal relabeling, or printed-vector
repair is claimed.

The old following factor in that reverse coordinate direction is now also
represented by a total source-coordinate function.  Lean zero-extends any
pivot-first following matrix outside the old residual-column block and proves
that `case2DisplayedSourceFollowingFactor` restricts the result back to the
supplied matrix.  Applying this to `Q*Cprime` gives the source-coordinate
version of `Q^-1*(Q*Cprime)=Cprime`, and the supplied-boundary `Q/P` product
identity now has a paper-named wrapper whose old following factor is a total
source function.  This still stops below full source production of the next
`C'^(S+1)`, recurrence/exponent post-data, successor chart family, transition
invariant, Jacobian, normal crossing, RLCT extraction, arbitrary pivot
coverage, terminal relabeling, or printed-vector repair.

The stronger A4 chart-production route has now been explicitly audited and
blocked at the current source/API boundary.  Aoyagi pp. 19-22 support the
displayed local Case 2 algebra and the continuation/terminal slogans, but do
not supply coordinate production of recurrence data, corrected exponent data,
the successor chart family, a full next following matrix, or a transition
invariant.  Future work must either build an independent selected-entry
atlas/transition construction or keep proving finite consequences below the
supplied-boundary interface.

The A5 equation `(4)` selected-span branch-value classifier is now
Lean-proved.  In `Lemma5DisplayedVector.lean`, selected-block endpoint helpers
show that a non-left-endpoint point is strictly after its block's left endpoint
and that every point in a later block is strictly after an earlier left
endpoint.  The inductive `AoyagiLemma5Eq4SelectedSpanBranchValue` records the
five advertised branch alternatives, and
`aoyagiLemma5Eq4_branchValue_of_block` classifies any selected-block point
from a supplied equation `(4)` piecewise certificate.  The certificate now
carries `a<=ell` and `p+1<=a`, and
`aoyagiLemma5Eq4_boundaryIndex_le_ell_of_piecewiseSourceVector` records
`p+(ell-a)+1<=ell`, so the displayed boundary is an in-range selected
cutpoint rather than only a totalized accessor value.  The boundary split is
also Lean-proved: `p+1<a` puts the boundary at the left endpoint of the next
selected block and inside the half-open selected span, while `p+1=a` makes it
the terminal selected endpoint and excludes it from every selected block.
Combining this with the selected-span coverage theorem gives
`aoyagiLemma5Eq4_selectedSpan_branchValue`: every
`S_1-1 <= S < S_(ell+1)-1` has one of the advertised supplied branch values.
The boundary singleton `S_(p+ell-a+2)-1` remains separate from the strict tail
branch.  This is still conditional branch bookkeeping only; it does not
construct the displayed vector, prove terminal `tilde t=0`, vector
admissibility, total source-layer coverage, source vector-to-chain
correspondence, the Case 1(2) chart sequence, Lemma 5 order count, normal
crossings, or RLCT extraction.

The A5 equation `(4)` terminal endpoint boundary is also now Lean-proved at a
strictly supplied-data level.  Nat-indexed wrappers expose the already-proved
terminal zero values `Htilde_ell=0` and `Htilde'_ell=0` under Definition 3's
selected-sum identity.  `AoyagiSelectedCutpoints.not_block_terminalEndpoint`
records that the terminal selected endpoint `S_(ell+1)-1` is not in any
half-open selected block.  The supplied piecewise certificate now also exports
left-endpoint values for the prefix, middle, and strict-tail branches.  Finally,
`aoyagiLemma5Eq4_terminalEndpoint_zero_of_upperNatExtension` says that if a
future record supplies `T(S_(ell+1)-1)=Htilde'_ell`, then
`T(S_(ell+1)-1)=0`.  The terminal-extension obstruction now combines this
with the terminal-collision branch: when `p+1=a`, a supplied equation `(4)`
certificate plus such a terminal extension forces
`W_(ell+1)=M-p+1`, and failure of that compatibility rules out the extension.
A uniform `p=1` source-selected corollary now rules out that supplied terminal
upper-chain extension without choosing concrete widths: when `p=1`, the
extension would force `W_(ell+1)=M`, but Definition 3's strict selected-width
inequality gives `W_(ell+1)<=M-1`.
The general terminal-extension necessary condition is now Lean-proved too:
under the same source-selected hypotheses, imposing the supplied terminal
upper-chain extension forces `2<=p`, and `p<2` rules it out.  The `p=0` edge
is recorded only as a Lean-totalized supplied-certificate consequence, not as
an additional printed source case.
A concrete supplied-data wrapper now combines this obstruction with the closed
Definition 3-shaped tuple `ell=3`, `a=2`, `p=1`, `M=3`, all selected widths
`2`: any supplied equation `(4)` certificate for that tuple is incompatible
with the supplied terminal upper-chain extension
`T(S_(ell+1)-1)=Htilde'_ell`.  Equivalently, the printed terminal-collision
branch value is `1`, while `Htilde'_ell=0`; these endpoint values are now
Lean-proved directly too.
A fresh source audit reconfirms that the printed paper does not supply the
Case 1(2) chart sequence, repeated gap checks, terminal endpoint convention,
or proof of `tilde t=0`; therefore this is not a displayed-vector realisation
theorem.

The first A5 source-label bridge for equation `(4)` is now Lean-proved in
`Lemma5SourceLabel.lean`.  The theorem
`aoyagiLemma5Eq4_actualWidthLabel_of_widthCompatibility` converts the selected
label bounds for `k=Htilde_p+1` into `actualWidthLabel` only under explicit
source-layer range, selected-width/actual-width compatibility, and Nat/Int
label compatibility hypotheses.  This keeps the selected-data layer separate
from actual source dimensions and still makes no introduced-label,
terminal-exponent, vector-construction, chart-sequence, or order-count claim.

The A5 equation `(3)` local-data and actual-label bridge is now Lean-proved.
The new Htilde arithmetic packages the selected cutoff, first upper/lower gap,
and selected-label bounds under `1<=a`, `a<ell`, and explicit width guards.
The source-shaped theorem uses Definition 3 only for the lower guard
`M-1<=W_1+W_2`; the one-unit slack `W_1+2<=M` remains explicit.  This is
essential: Lean now records the closed counterexample
`ell=3`, `a=2`, `M=3`, all selected widths `2`, where Definition 3 holds but
`W_1+2<=M` fails and `Htilde'_1+1=3>W_2=2`.  `Lemma5SourceLabel.lean` also converts the selected
label to `actualWidthLabel` under explicit source-layer range and
actual-width compatibility.  No equation `(3)` displayed vector, terminal
`tilde t=0`, introduced-label status, chart sequence, or order count is
claimed.

The A5 equation `(3)` supplied piecewise certificate is also now Lean-proved
in `Lemma5DisplayedVector.lean`.  The record
`AoyagiLemma5Eq3PiecewiseSourceVector` stores the four displayed branches as
data; `aoyagiLemma5Eq3_branchValue_of_block` and
`aoyagiLemma5Eq3_selectedSpan_branchValue` classify points in the half-open
selected span into those supplied branches, keeping
`S_(ell-a+2)-1` separate from the strict tail.  The source-shaped
own-coordinate theorem combines this supplied certificate with the local-data
and slack theorem to get `T(S_2-1)=Htilde'_1` and the selected label bounds.
This is still below the blocked displayed-family realisation boundary: no
vector construction, terminal endpoint coverage, terminal `tilde t=0`,
introduced-label status, chart sequence, or order count is claimed.

The equation `(3)` terminal obstruction at `a=1` is now Lean-proved.  For a
supplied equation `(3)` branch certificate, the special boundary becomes the
terminal selected endpoint `S_(ell+1)-1` when `a=1`.  Since the selected-sum
identity gives `Htilde'_ell=0`, the supplied branch assignment gives
`T(S_(ell+1)-1)=1`.  This records why equation `(3)` cannot be promoted to a
uniform terminal-zero theorem without additional chart-sequence or endpoint
data.

The complementary equation `(3)` boundary split is also Lean-proved.  The
boundary index `ell-a+1` is in range under the supplied guards, and
`ell-a+1<ell` is equivalent to `2<=a`.  Thus for `2<=a` the displayed special
point is the left endpoint of an ordinary selected block and lies in the
half-open selected span; for `a=1` it is the terminal selected endpoint and is
in no selected block.  Lean also records the no-zero corollary in the terminal
case: the existing value-one theorem rules out a simultaneous terminal
endpoint value `0`.  This is finite boundary bookkeeping only, not a
displayed-vector construction, terminal `tilde t=0`, chart sequence,
introduced-label theorem, or order count.

The equation `(3)` special boundary value is now also separated from the
same-coordinate interval count.  A supplied equation `(3)` certificate assigns
`T(C.point (ell-a+1)-1)=Htilde'_(ell-a+1)+1`, so Lean proves this value is
strictly greater than the upper endpoint of the same-coordinate interval and
is not in `aoyagiHtildeIntervalValueSetNat` at coordinate `ell-a+1`.  In the
strict case `2<=a`, the previous boundary split puts the same point inside the
half-open selected span; the new theorem says this selected-span singleton is
not part of the already-counted same-coordinate interval family.  This is
still not a displayed-vector construction, terminal `tilde t=0`, chart
sequence, introduced-label theorem, or Lemma 5 order count.

The analogous terminal-collision arithmetic for equation `(4)` is now
Lean-proved.  When `p+1=a`, the special boundary
`S_(p+ell-a+2)-1` is the terminal selected endpoint.  Definition 3's
selected-sum identity gives `Htilde'_(ell-1)=M-W_(ell+1)`, so the supplied
equation `(4)` boundary value is `M-W_(ell+1)-p+1`.  It is zero exactly when
`W_(ell+1)=M-p+1`, an extra compatibility condition not forced by Definition
3.  This is now Lean-certified by the concrete tuple
`ell=3`, `a=2`, `p=1`, `M=3`, with all selected widths equal to `2`: the
selected-sum and strict selected-width inequalities hold, while
`W_(ell+1)=M-p+1` fails.  This further reinforces the boundary that equations
`(3)` and `(4)` are not terminal-vector theorems from the printed display
alone.

The strict-boundary interval arithmetic for equation `(4)` is now
Lean-proved as a classifier.  For a supplied equation `(4)` certificate with
`1<=p`, `p+1<a`, and `p<=ell-a`, the special boundary value
`T(C.point (p+(ell-a)+1)-1)=Htilde'_(p+ell-a)-p+1` belongs to
`aoyagiHtildeIntervalValueSetNat ell a M m (p+(ell-a))` exactly when
`2*p<=a+1`.  The Lean names are
`aoyagiLemma5Eq4_boundaryValue_mem_intervalValueSetNat_iff_two_mul_le`,
`aoyagiLemma5Eq4_boundaryValue_mem_intervalValueSetNat_of_two_mul_le`, and
`aoyagiLemma5Eq4_boundaryValue_not_mem_intervalValueSetNat_of_lt_two_mul`.
This deliberately avoids the false Eq3-style claim that the Eq4 strict
boundary is uniformly outside the same-coordinate interval family.  It is
still finite supplied-branch bookkeeping only, not a displayed-vector
construction, terminal `tilde t=0`, chart sequence, introduced-label theorem,
Lemma 5 order count, normal crossings, or RLCT extraction.

The companion equation `(4)` boundary-coordinate window is now Lean-proved.
For the strict boundary point itself, let `r=p+(ell-a)+1`; the supplied value
is `Htilde'_(r-1)-p+1`, while the boundary-coordinate interval is
`[Htilde_r,Htilde'_r]`.  Lean proves the offset from the boundary-coordinate
upper endpoint,

```text
T(C.point r-1)-Htilde'_r = M-W_r-p+1,
```

and the exact membership window

```text
M-p+1 <= W_r <= M-p+1+excess(ell,a,r),
```

with `excess(ell,a,r)=min(ell-a,a-p-1)`.  The source-shaped `p=1` corollary
uses Definition 3's selected-width inequality `W_r<=M-1` to prove the
boundary value is strictly above `Htilde'_r` and is not in the
boundary-coordinate interval.  This is still not a displayed-vector
construction, terminal `tilde t=0`, chart sequence, introduced-label theorem,
Lemma 5 order count, normal crossings, or RLCT extraction.

The boundary-coordinate source-selected obstruction for equation `(4)` is now
Lean-proved.  If the strict boundary value belongs to its own
boundary-coordinate interval, the lower edge of the width window gives
`M-p+1<=W_r`; Definition 3's strict selected-width inequality gives
`W_r<=M-1`; hence `2<=p`.  The companion theorem rules out membership when
`p<2`.  This is only a necessary condition and does not assert membership for
`p>=2`, construct the displayed vector, prove terminal `tilde t=0`, chart
sequence, introduced-label status, Lemma 5 order count, normal crossings, or
RLCT extraction.

The converse overclaim is now guarded by a concrete `p=2` constant-width
example.  With `ell=5`, `a=4`, `p=2`, `M=5`, and all six selected widths equal
to `4`, Lean now packages the Definition 3-shaped selected-width sum and
strict inequalities, and the boundary-coordinate width window is satisfied.
Therefore any supplied equation `(4)` certificate with these constants has the
strict boundary value inside its boundary-coordinate interval.  This does not
construct such a certificate or the displayed vector; it only shows that the
previous `2<=p` theorem is a necessary condition, not a uniform
nonmembership statement for `p>=2`.

Equation `(5)` now has its first supplied own-coordinate offset slice in Lean.
The record `AoyagiLemma5Eq5OwnCoordinateBranch` is not a full piecewise
certificate; it stores only the source-facing own-branch value
`T(s)=Htilde'_p-alpha` on block `p`, with `p` equal to Aoyagi's paper `j0`.
Lean proves the source label rewrite `T(s)=k-1` under
`k=Htilde'_p+1-alpha`, membership in the same-coordinate interval under
`alpha<=excess(ell,a,p)`, and the finite offset-value cardinality
`min(excess(ell,a,p),p-1)`.  This moves Eq5 into the same conditional
displayed-family scaffold as Eq3/Eq4 while keeping source-label legality, full
selected-span classification, terminal `tilde t=0`, chart sequence, and Lemma
5 order count open.

Eq5 now has the full supplied selected-span branch certificate too.  The new
record stores Aoyagi's five displayed Eq5 branch rows with paper `j`
translated to Lean block `b=j-1` and paper `j0` translated to Lean coordinate
`p`.  The classifier is only selected-span bookkeeping: it routes selected
blocks to the supplied branches and derives the narrower own-coordinate record
from the post-`p` branch at `b=p`.  It still leaves construction of the
vector, source-label legality, terminal `tilde t=0`, chart sequence, and Lemma
5 order count open.

Eq5 now also has the own-coordinate source-label bridge.  Definition 3's
selected-width inequalities first give `W_i<=M-1`; the same prefix/tail
arithmetic then proves
`1<=Htilde'_p+1-alpha<=W_p` under the supplied Eq5 offset guard
`1<=alpha<=excess(ell,a,p)`.  With explicit actual-width compatibility at
`C.point p-1`, Lean proves `actualWidthLabel`, and the supplied Eq5 piecewise
certificate wrapper combines this with the own-coordinate value `T=k-1`.
This removes the narrow own-coordinate label-legality blocker, but still does
not construct the displayed vector, prove arbitrary-point block label
legality, terminal `tilde t=0`, chart sequence, or Lemma 5 order count.

The Eq5 source-label bridge now also has an arbitrary-own-block wrapper.
Instead of fixing `S=C.point p-1`, the theorem takes a source index `S`, range
data `1<=S<=L`, and explicit width compatibility `n(S+1)=W_p`.  With
`C.block p S` and a supplied Eq5 piecewise certificate, Lean proves both
`T(S)=k-1` and `actualWidthLabel L n S k`.  This is the source-faithful
arbitrary-`s` form of the same conditional bridge; it still does not prove the
width compatibility, construct the displayed vector, prove terminality, or
count Lemma 5 families.

The arbitrary-own-block wrapper now derives its lower source-range hypothesis
from the Eq5 guards.  Since the supplied Eq5 certificate carries
`1<=alpha<p`, the own coordinate satisfies `0<p`; selected-cutpoint positivity
and strictness give `1<=C.point p-1`, and `C.block p S` gives `1<=S`.  The
new source-shaped theorem keeps only `S<=L` and `n(S+1)=W_p` explicit on the
source-range/width side.

Eq5 now has a source-range and width-bound refinement.  The selected-cutpoint
helpers prove that `C.block b S` and last-cutpoint compatibility
`C.point ell<=L+1` imply `S<=L`.  The actual-label theorem now also accepts
the weaker and more source-faithful width hypothesis `W_p<=n(S+1)` instead of
only equality `n(S+1)=W_p`.  The new wrappers
`aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_widthBound` and
`aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthBound`
combine this with the supplied Eq5 own-block value `T(S)=k-1`.  This still
does not prove the width bound from Definition 3, construct the displayed
vector, prove terminal `tilde t=0`, build the chart sequence, or prove Lemma
5 order count.  Reproduction, statement card, and review are saved at
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-source-range-width-bound-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-source-range-width-bound.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-source-range-width-bound-a5.md`.

Eq5 now has a conditional block-width dominance bridge.  From `C.block p S`,
Lean proves the source-layer interval `C.point p<=S+1<C.point(p+1)`.  A
block-local actual-width lower-bound hypothesis therefore supplies
`W_p<=n(S+1)`, and the Eq5 wrappers combine this with the last-cutpoint range
theorem to prove `T(S)=k-1` and `actualWidthLabel L n S k`.  Derived wrappers
also cover a left-endpoint-width-plus-block-minimum interface and an
index-level off-selected-layer dominance interface.  The source review found a
real obstruction to deriving this from Definition 3 alone: Definition 3's
non-selected condition is phrased by width-value membership, so an unselected
layer with a duplicate selected width value is not controlled.  Reproduction,
statement card, and review are saved at
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-block-width-dominance-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-block-width-dominance.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-block-width-dominance-a5.md`.

The duplicate-width obstruction is now Lean-proved as a closed guardrail:
`aoyagiLemma5Eq5_blockWidthBound_not_forced_by_selectedWidthHypotheses_example`
in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The witness uses
cutpoints `1,3,5,7`, selected widths `1,2,2,2`, actual width `n(6)=1`,
`p=2`, and `S=5`.  It satisfies selected cutpoint compatibility, the selected
sum and strict selected-width inequalities, and the value-level non-selected
condition, but fails `W_p<=n(S+1)`.  This records that the Eq5 width bound is
not a Definition 3 consequence unless Definition 3 is strengthened by
position-level/off-selected or block-local dominance data.  Reproduction,
statement card, and review are saved at
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-width-bound-counterexample-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-width-bound-counterexample.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-width-bound-counterexample-a5.md`.

Eq5 now has a finite offset/excess decomposition:
`aoyagiLemma5IntervalExcess_eq_eq5OffsetCard_add_risingIndicator` and
`aoyagiLemma5Eq5_lowerEndpoint_not_mem_offsetValueSet_of_le_min` in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  Pointwise, the Lemma 5
interval excess equals the Eq5 strict-offset value-set cardinality plus one
extra contribution exactly on the rising coordinates
`1<=p`, `p<=a`, `p<=ell-a`; in that rising region, Lean also proves the lower
endpoint is not in the strict-offset set.  This is a count scaffold only: it
does not realise the extra contribution by equations `(3)`/`(4)`, construct
vectors, prove source-label legality, terminality, admissibility, or Lemma 5
order count.  Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-offset-excess-decomposition-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-offset-excess-decomposition.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-offset-excess-decomposition-a5.md`.

Eq3/Eq4 now have own-coordinate actual-label adapter wrappers:
`aoyagiLemma5Eq4_piecewise_ownCoordinate_actualWidthLabel_of_widthCompatibility`
and
`aoyagiLemma5Eq3_piecewise_ownCoordinate_actualWidthLabel_of_sourceSelected_slack`
in `lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  They combine the
existing supplied-piecewise own-coordinate value theorem with the existing
actual-label bridge, giving `T(S)=k-1` and `actualWidthLabel L n S k` in one
API.  The last-cutpoint wrappers
`aoyagiLemma5Eq4_piecewise_ownCoordinate_actualWidthLabel_of_lastPoint` and
`aoyagiLemma5Eq3_piecewise_ownCoordinate_actualWidthLabel_of_lastPoint`
derive the upper source range from `C.point ell<=L+1`.  Eq3 still carries the
explicit one-unit slack, and all wrappers keep actual-width compatibility
explicit.  Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-eq4-own-coordinate-actual-label-adapters-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-eq4-own-coordinate-actual-label-adapters.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq3-eq4-own-coordinate-actual-label-adapters-a5.md`.

Eq5 now has a small interval/introduced-label hardening layer.  Theorems
`aoyagiLemma5Eq5_lowerEndpoint_mem_intervalValueSetNat_of_lt`,
`aoyagiLemma5Eq5_insert_lowerEndpoint_offsetValueSet_card_of_le_min`,
`aoyagiLemma5Eq5_insert_lowerEndpoint_offsetValueSet_subset_intervalValueSetNat_of_le_min`,
and
`aoyagiLemma5Eq5_insertLower_offsetCard_add_one_eq_intervalCard_of_le_min`
record that in the rising region the lower endpoint plus the strict Eq5
offset values form a subset of the same-coordinate interval with cardinality
equal to the excess, one value short of the full interval.  The wrapper
`aoyagiLemma5Eq5_piecewise_ownBlock_intervalValue_introducedLabel_of_lastPoint_widthBound`
combines supplied Eq5 own-block interval membership, `T S=k-1`, and
post-advance `introducedLabel L n S k S k`.  It keeps the actual-width lower
bound explicit and does not construct displayed vectors or prove the Lemma 5
order count.  Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-interval-introduced-label-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-interval-introduced-label.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-interval-introduced-label-a5.md`.

Eq3/Eq4 now also have post-advance introduced-label wrappers:
`aoyagiLemma5Eq4_piecewise_ownCoordinate_introducedLabel_of_lastPoint` and
`aoyagiLemma5Eq3_piecewise_ownCoordinate_introducedLabel_of_lastPoint` in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  These wrap the existing
last-point actual-label adapters, giving `T S=k-1` and
`introducedLabel L n S k S k` for the own coordinate.  Eq3 keeps the explicit
one-unit slack, and all actual-width compatibility remains explicit.  This is
introduced-label API cleanup only, not displayed-vector construction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-eq4-own-coordinate-introduced-label-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-eq4-own-coordinate-introduced-label.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq3-eq4-own-coordinate-introduced-label-a5.md`.

Eq5 now also identifies the inserted lower-plus-strict-offset set exactly as
the same-coordinate interval with the upper endpoint erased.  The proved names
are `aoyagiLemma5Eq5_upperEndpoint_mem_intervalValueSetNat_of_lt`,
`aoyagiLemma5Eq5_upperEndpoint_not_mem_insert_lowerEndpoint_offsets_of_le_min`,
and
`aoyagiLemma5Eq5_insertLower_offsets_eq_interval_erase_upper_of_le_min` in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  In the rising region
`1<=p`, `p<=a`, `p<=ell-a`, Lean proves that the upper endpoint belongs to the
interval but not to the lower-plus-offset inserted set; together with the
previous subset and cardinality bridge, this gives equality with
`erase Htilde'_p`.  This remains count-side scaffolding only: it does not
realise the erased endpoint by equations `(3)`/`(4)`, construct displayed
vectors, prove source-label legality, terminality, admissibility, order count,
normal crossings, or RLCT extraction.  Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-interval-erase-upper-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-interval-erase-upper.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-interval-erase-upper-a5.md`.

The existing Eq3/Eq4/Eq5 introduced-label wrappers now also have finite-domain
membership versions in `lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  The
proved names are
`aoyagiLemma5Eq4_piecewise_ownCoordinate_mem_introducedLabelFinset_of_lastPoint`,
`aoyagiLemma5Eq3_piecewise_ownCoordinate_mem_introducedLabelFinset_of_lastPoint`,
and
`aoyagiLemma5Eq5_ownBlock_intervalValue_mem_introducedLabelFinset_of_lastPoint_widthBound`.
They do not add source content: each calls the corresponding
`introducedLabel` wrapper and applies `mem_introducedLabelFinset.mpr` to put
`Sigma.mk S k` in `introducedLabelFinset L n S k`.  This is the finite-domain
shape needed by later product/sum APIs, not a `LabelExponentCertificate` and
not a terminal-exponent or least-value theorem.  Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-introduced-label-finset-adapters-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-introduced-label-finset-adapters.md`,
and
`threads/05-arithmetic-tail/review-lemma5-introduced-label-finset-adapters-a5.md`.

The three-region interval-size profile displayed in Aoyagi Lemma 5 is now
named directly in `lean/DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean`.
The proved names are `aoyagiLemma5IntervalSize_eq_succ_of_le_min`,
`aoyagiLemma5IntervalSize_eq_min_succ_of_min_le_of_le_max`,
`aoyagiLemma5IntervalSize_eq_falling_of_max_le`, and
`aoyagiLemma5IntervalSize_sourcePiecewise`.  These are pure finite arithmetic
for `1 + min(j,ell-j,a,ell-a)`, matching the PDF's rising, plateau, and
falling cardinality regions.  They do not assert source-vector realisation or
Lemma 5 order count.  Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-interval-size-profile-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-interval-size-profile.md`,
and
`threads/05-arithmetic-tail/review-lemma5-interval-size-profile-a5.md`.

Eq5 now has a strict-offset finite-domain adapter in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`:
`aoyagiLemma5Eq5_ownBlock_offsetValue_mem_introducedLabelFinset_of_lastPoint_widthBound`.
For one supplied Eq5 piecewise certificate and one own-block source index, it
packages `T S` as an Eq5 strict-offset value, a same-coordinate interval value,
the label predecessor `k-1`, and `Sigma.mk S k ∈ introducedLabelFinset L n S k`.
This still works one fixed `alpha` at a time and does not construct the family
of all Eq5 vectors or prove Lemma 5 order count.  Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-offset-finset-adapter-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-offset-finset-adapter.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-offset-finset-adapter-a5.md`.

Eq4 now supplies the lower endpoint in the Eq5 erase-upper finite-set equality.
The new theorem
`aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_eq_interval_erase_upper_of_le_min`
in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean` rewrites
`T(C.point p-1)` to `Htilde_p` using the supplied Eq4 own-coordinate theorem,
then applies the existing Eq5 equality
`insert Htilde_p Eq5OffsetValueSet_p = interval.erase Htilde'_p`.  This is
only a conditional finite-set wrapper; it does not realise the erased upper
endpoint or prove any displayed-vector construction/order-count result.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-lower-endpoint-eq5-erase-upper-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-lower-endpoint-eq5-erase-upper.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq4-lower-endpoint-eq5-erase-upper-a5.md`.

Eq5 strict offsets are now named as the same-coordinate interval with both
endpoints erased.  The new theorem
`aoyagiLemma5Eq5_offsets_eq_interval_erase_endpoints_of_le_min` in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean` erases the lower
endpoint from the existing equality
`insert Htilde_p Eq5OffsetValueSet_p = interval.erase Htilde'_p`, using the
existing proof that `Htilde_p` is not a strict Eq5 offset.  This is only
finite-set normalization; it does not claim endpoint realisation,
displayed-vector construction, or Lemma 5 order count.  Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-offsets-erase-endpoints-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-offsets-erase-endpoints.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-offsets-erase-endpoints-a5.md`.

Eq3 and Eq4 own-coordinate supplied branches now have interval-membership plus
finite-domain introduced-label adapters in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  The new theorem names are
`aoyagiLemma5Eq4_piecewise_ownCoordinate_intervalValue_mem_introducedLabelFinset_of_lastPoint`
and
`aoyagiLemma5Eq3_piecewise_ownCoordinate_intervalValue_mem_introducedLabelFinset_of_lastPoint`.
They package the already-proved endpoint value, endpoint interval membership,
label predecessor, and `introducedLabelFinset` membership facts.  Eq3's
explicit slack and Eq4's repaired guards remain explicit.  This does not
provide terminal exponent or least-value data and does not prove displayed
vector construction or Lemma 5 order count.  Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-eq4-interval-finset-adapters-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-eq4-interval-finset-adapters.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq3-eq4-interval-finset-adapters-a5.md`.

Eq5 now has a one-step introduced-domain insert wrapper in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  The theorem
`aoyagiLemma5Eq5_ownBlock_introducedLabelFinset_succ_eq_insert_of_lastPoint_widthBound`
specializes the generic `introducedLabelFinset_succ_eq_insert` theorem to a
supplied Eq5 branch label `J+1 = Htilde'_p+1-alpha`, using the existing Eq5
actual-width label wrapper.  It is finite-domain bookkeeping only and does not
provide terminal exponent, least-value, or displayed-vector construction data.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-domain-insert-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-domain-insert.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-domain-insert-a5.md`.

Eq5 now also has the corresponding one-step finite-domain cardinality wrapper.
The generic theorem `introducedLabelFinset_card_succ_eq_succ` in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` combines the one-step insert
equality with `not_mem_introducedLabelFinset_case2_new_before`; the Eq5 theorem
`aoyagiLemma5Eq5_ownBlock_introducedLabelFinset_card_succ_eq_succ_of_lastPoint_widthBound`
specializes it to a supplied Eq5 branch label `J+1 = Htilde'_p+1-alpha`.
This is finite-domain cardinality bookkeeping only and does not provide
terminal exponent, least-value, displayed-vector construction data, or the
Lemma 5 order count.  Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-domain-card-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-domain-card.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-domain-card-a5.md`.

Eq5 now also has a one-branch adapter from strict-offset membership to
same-coordinate interval membership with both endpoints erased.  The theorem
`aoyagiLemma5Eq5_ownBlock_eraseEndpoints_mem_introducedLabelFinset_of_lastPoint_widthBound`
in `lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean` combines the existing
strict-offset finite-domain adapter with
`aoyagiLemma5Eq5_offsets_eq_interval_erase_endpoints_of_le_min`.  It keeps the
rising-region guards explicit and still proves only one supplied branch at a
time.  It does not realise the erased endpoints, construct displayed vectors,
or prove the Lemma 5 order count.  Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-interval-erase-endpoints-finset-adapter-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-interval-erase-endpoints-finset-adapter.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-interval-erase-endpoints-finset-adapter-a5.md`.

Eq3/Eq4 now also have one-step introduced-domain insert and cardinality
wrappers for their supplied endpoint branches.  The theorem names are
`aoyagiLemma5Eq4_ownCoordinateFinset_succ_eq_insert_of_lastPoint`,
`aoyagiLemma5Eq4_ownCoordinateFinset_card_succ_eq_succ_of_lastPoint`,
`aoyagiLemma5Eq3_ownCoordinateFinset_succ_eq_insert_of_lastPoint`, and
`aoyagiLemma5Eq3_ownCoordinateFinset_card_succ_eq_succ_of_lastPoint` in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  They apply the existing
Eq3/Eq4 actual-label wrappers to the generic one-step insert and cardinality
theorems.  Eq3's slack and Eq4's repaired guards remain explicit.  These
theorems are finite-domain bookkeeping only, not displayed-vector construction
or Lemma 5 order count.  Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-eq4-domain-insert-card-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-eq4-domain-insert-card.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq3-eq4-domain-insert-card-a5.md`.

Eq5 now has a source-facing Case 2 recurrence-weight update wrapper.  The
theorem
`aoyagiLemma5Eq5_ownBlock_case2_weight_succ_current_eq_newVar_mul_of_lastPoint_widthBound`
in `lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean` combines the existing
Eq5 actual-label wrapper with
`IntroducedLabelRecurrenceState.Case2SuppliedPostData.weight_succ_current_eq_new_mul_of_ge`.
It proves that, for one supplied Eq5 branch and supplied Case 2 post-data,
rows from `J+1` onward have `post.weight i = u * pre.weight i`.  It does not
assert chart production, terminal exponent, least-value data, or Lemma 5 order
count.  Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-case2-weight-update-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-case2-weight-update.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-case2-weight-update-a5.md`.

Eq3/Eq4 now have the analogous source-facing Case 2 recurrence-weight update
wrappers.  The theorem names are
`aoyagiLemma5Eq4_ownCoordinate_case2_weight_succ_current_eq_newVar_mul_of_lastPoint`
and
`aoyagiLemma5Eq3_ownCoordinate_case2_weight_succ_current_eq_newVar_mul_of_lastPoint`
in `lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  They combine the
existing Eq3/Eq4 actual-label wrappers with
`IntroducedLabelRecurrenceState.Case2SuppliedPostData.weight_succ_current_eq_new_mul_of_ge`.
They prove that, for one supplied endpoint branch and supplied Case 2
post-data, rows from `J+1` onward have `post.weight i = u * pre.weight i`.
Eq4's repaired guards, Eq3's explicit slack, actual-width compatibility, and
the supplied post-data package remain explicit.  They do not assert chart
production, terminal exponent, least-value data, or Lemma 5 order count.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-eq4-case2-weight-update-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-eq4-case2-weight-update.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq3-eq4-case2-weight-update-a5.md`.

Eq3/Eq4/Eq5 now have source-facing supplied exponent-domain extension
wrappers.  The theorem names are
`aoyagiLemma5Eq4_ownCoordinate_extendExponentDomain_succ_current_of_lastPoint`,
`aoyagiLemma5Eq3_ownCoordinate_extendExponentDomain_succ_current_of_lastPoint`,
and
`aoyagiLemma5Eq5_ownBlock_extendExponentDomain_succ_current_of_lastPoint_widthBound`
in `lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  They use the existing
source-label wrappers only to supply the new label's introduced-label field at
state `(S,J+1)`.  The new label's terminal-exponent equality and least-value
proof are explicit hypotheses.  The generic one-step exponent-domain theorem
then extends the all-introduced-label exponent-certificate family from
`(S,J)` to `(S,J+1)`.  This is not a terminal-exponent calculation, not a
least-value calculation, and not displayed-vector construction or Lemma 5
order count.  Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-supplied-exponent-domain-extension-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-supplied-exponent-domain-extension.md`,
and
`threads/05-arithmetic-tail/review-lemma5-supplied-exponent-domain-extension-a5.md`.

The first same-coordinate interval now has supplied-shaped finite-set
coverage.  The theorem
`aoyagiLemma5_suppliedEq3Upper_Eq4_firstInterval_insertOwnCoordinates_eq_intervalValueSetNat`
in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean` proves that the
separately supplied Eq3-shaped upper endpoint, supplied Eq4 lower endpoint,
and strict Eq5 offset set equal
`aoyagiHtildeIntervalValueSetNat ell a M m 1`.  The proof uses the existing
Eq4/Eq5 erase-upper equality, the separately supplied Eq3-shaped
own-coordinate upper endpoint, and `Finset.insert_erase`.  The printed
equation `(3)` excludes `(S_2-1,Htilde'_1+1)`, so this is not a claim that the
printed Eq3 branch supplies the first-interval upper endpoint.  This is only
first-interval finite-set bookkeeping for supplied branch certificates; it
does not construct displayed vectors, prove source-label legality, cover all
intervals, package all branches, prove Lemma 5 order count, normal crossings,
or RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-first-interval-supplied-shaped-coverage-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-first-interval-supplied-shaped-coverage.md`,
and
`threads/05-arithmetic-tail/review-lemma5-first-interval-supplied-shaped-coverage-a5.md`.

One-interval coverage now has a p-general supplied-upper finite-set wrapper.
The theorem
`aoyagiLemma5_suppliedUpper_Eq4_insertOwnCoordinate_eq_intervalValueSetNat_of_le_min`
in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean` proves that an
explicitly supplied upper endpoint equality, a supplied Eq4 lower
own-coordinate value, and the strict Eq5 offset set equal
`aoyagiHtildeIntervalValueSetNat ell a M m p`.  This deliberately keeps the
upper endpoint as an input rather than claiming printed Eq3 supplies it.  It is
only one-interval finite-set bookkeeping; it does not construct displayed
vectors, prove source-label legality, cover all intervals, package all
branches, prove Lemma 5 order count, normal crossings, or RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-supplied-upper-eq4-interval-coverage-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-supplied-upper-eq4-interval-coverage.md`,
and
`threads/05-arithmetic-tail/review-lemma5-supplied-upper-eq4-interval-coverage-a5.md`.

The supplied-upper finite-set wrapper now has an Eq3-shaped component
instantiation.  The theorems
`aoyagiLemma5Eq3_piecewise_component_upperEndpoint_of_le_gap` and
`aoyagiLemma5_suppliedEq3UpperComponent_Eq4_interval_insertComponents_eq_intervalValueSetNat`
in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean` prove that a supplied
Eq3-shaped component value is the upper endpoint on block `p`, and that this
component plus the supplied Eq4 lower endpoint and strict Eq5 offsets fills the
one same-coordinate interval.  This is still only component-value and
one-interval finite-set bookkeeping: no source-label legality, introduced-label
status, displayed-vector construction, all-interval/all-branch coverage, Lemma
5 order count, normal crossings, or RLCT extraction is proved.  Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-shaped-component-interval-coverage-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-shaped-component-interval-coverage.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq3-shaped-component-interval-coverage-a5.md`.

The Eq3-shaped p-general component now has supplied-bound source-label
wrappers.  Theorems
`aoyagiLemma5Eq3_component_actualWidthLabel_of_lastPoint_labelBounds`,
`aoyagiLemma5Eq3_component_introducedLabel_of_lastPoint_labelBounds`,
`aoyagiLemma5Eq3_component_mem_introducedLabelFinset_of_lastPoint_labelBounds`,
and
`aoyagiLemma5Eq3_component_intervalValue_mem_introducedLabelFinset_of_lastPoint_labelBounds`
in `lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean` package the component as
an actual source label, introduced label, finite introduced-label member, and
interval value under explicit actual-width compatibility and label-bound
hypotheses.  They do not derive p-general Eq3 label legality from Definition 3
or prove displayed-vector construction, all-interval/all-branch coverage,
Lemma 5 order count, normal crossings, or RLCT extraction.  Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-shaped-component-supplied-label-bounds-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-shaped-component-supplied-label-bounds.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq3-shaped-component-supplied-label-bounds-a5.md`.

The same supplied-bound Eq3 component now feeds the one-step domain,
recurrence, and exponent-certificate APIs.  Theorems
`aoyagiLemma5Eq3_componentFinset_succ_eq_insert_of_lastPoint_labelBounds`,
`aoyagiLemma5Eq3_componentFinset_card_succ_eq_succ_of_lastPoint_labelBounds`,
`aoyagiLemma5Eq3_component_case2_weight_succ_current_eq_newVar_mul_of_lastPoint_labelBounds`,
and
`aoyagiLemma5Eq3_component_extendExponentDomain_succ_current_of_lastPoint_labelBounds`
in `lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean` specialize the existing
generic one-step APIs after the component is supplied as an actual label.  The
terminal-exponent equality and least-value proof in the exponent wrapper remain
explicit hypotheses.  This still does not derive p-general Eq3 label bounds
from Definition 3, construct displayed vectors, prove chart production,
all-interval/all-branch coverage, Lemma 5 order count, normal crossings, or
RLCT extraction.  Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-component-domain-recurrence-exponent-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-component-domain-recurrence-exponent.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq3-component-domain-recurrence-exponent-a5.md`.

The strict equation `(5)` offset set now has a named rising-region cardinality
specialization.  The theorem
`aoyagiLemma5Eq5OffsetValueSet_card_eq_pred_of_le_min` in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean` proves that, under
`1<=p`, `p<=a`, and `p<=ell-a`, the strict-offset set has cardinality `p-1`.
This is only one-coordinate finite count bookkeeping below the all-branch
order-count boundary.  Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-strict-offset-rising-count-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-strict-offset-rising-count.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-strict-offset-rising-count-a5.md`.

Eq4 now has the matching lower-plus-Eq5 offset count wrapper.  The theorem
`aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_card_eq_offsetCard_add_one_of_le_min`
in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean` proves that a
supplied Eq4 lower own-coordinate value increases the strict Eq5 offset-set
cardinality by one in the rising region.  It is still a one-coordinate finite
count theorem: no source-label legality, displayed-vector construction, upper
endpoint realisation, all-coordinate/all-branch coverage, Lemma 5 order count,
normal crossings, or RLCT extraction.  Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-lower-plus-eq5-offset-count-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-lower-plus-eq5-offset-count.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq4-lower-plus-eq5-offset-count-a5.md`.

The supplied Eq3-shaped component plus Eq4 lower endpoint coverage now has
cardinality wrappers.  Theorems
`aoyagiLemma5_suppliedEq3UpperComponent_Eq4_interval_insertComponents_card_eq_intervalSize`
and
`aoyagiLemma5_suppliedEq3Upper_Eq4_insertComponents_card_eq_offsetCard_add_two`
in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean` prove that the
one-coordinate supplied three-piece set has interval-size cardinality, and in
the rising region has strict Eq5 offset-cardinality plus two.  These remain
one-coordinate finite count theorems: no source-label legality,
displayed-vector construction, all-coordinate/all-branch coverage, Lemma 5
order count, normal crossings, or RLCT extraction.  Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-eq4-interval-cardinality-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-eq4-interval-cardinality.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq3-eq4-interval-cardinality-a5.md`.

The remaining source-backed Lemma 5 gap has been re-expressed as a concrete
obligation table in
`threads/05-arithmetic-tail/reproduction-lemma5-source-chart-family-reconstruction-a5.md`.
The table separates the already-proved finite count/supplied one-coordinate
wrappers from the missing source family data: legal labels, vectorwise
`Ttilde<=T<=Ttilde'` bounds, Lemma 4 increment checks, a Case 1(2) chart
sequence, terminal `tilde t=0`, and nonduplication/coverage.  This is not a
Lean theorem yet; it is the source-reproduction gate before any source-backed
Lemma 5 order-count statement.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-source-chart-family-reconstruction-a5.md`.

The equation-by-equation source pass has now found concrete Lemma 4 witness
obstructions in the printed Lemma 5 equations.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-printed-equations-lemma4-obstructions-a5.md`.
Equation `(3)` exceeds `Ttilde'` at its special endpoint and gives an adjacent
`M+1` increment away from the terminal edge.  Equation `(4)`'s special
one-point line gives increment `W_(q+1)-1`, which is at most `M-2` under
Definition 3.  Equation `(5)` needs extra guards beyond the printed ones; Lean
now includes the conditional all-widths-four obstruction
`aoyagiLemma5Eq5_piecewise_belowLowerCounterexample_allWidthsFour` and
`aoyagiLemma5Eq5_piecewise_not_lowerBounded_allWidthsFour` in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  Consequence: do not
state a source-backed Lemma 5 order-count theorem from the printed equations.
The remaining honest routes are corrected-formula reconstruction or a supplied
chart-family boundary.  Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-printed-lower-bound-obstruction.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-printed-equations-lemma4-obstructions-a5.md`.

The finite increment pieces of the printed-equation obstruction are now in
Lean.  Theorems
`aoyagiLemma5Eq3_specialNextIncrement_eq_succ`,
`aoyagiLemma5Eq3_specialNextIncrement_not_twoValue`,
`aoyagiLemma5Eq4_specialIncrement_eq_selectedWidth_sub_one`,
`aoyagiLemma5Eq4_specialIncrement_lt_pred_of_sourceSelected`, and
`aoyagiLemma5Eq4_specialIncrement_not_twoValue_of_sourceSelected` live in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  They are conditional
finite-chain results: Eq `(3)`'s nonterminal printed special boundary gives
next increment `M+1`; Eq `(4)`'s special one-point line gives increment
`W-1`, strictly below `M-1` under Definition 3.  They do not construct source
vectors or corrected formulas.  Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-printed-increment-obstructions.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-printed-increment-obstructions-a5.md`.

The corrected-formula route for Lemma 5 is not recoverable from Aoyagi's PDF
alone.  The next Lean slice therefore lands only a supplied chart-family count
boundary in `lean/DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean`.  The
nonbase supplied family carries a base interval value, injective branch-value
coverage of the interval with that base erased, and cross-coordinate
disjointness for a finite-union count.  Lean proves
`aoyagiLemma5SuppliedNonbaseFamily_branch_card_eq_interval_card_sub_one`,
`aoyagiLemma5SuppliedNonbaseFamily_count`, and
`aoyagiLemma5SuppliedNonbaseFamily_biUnion_count`, giving
`1 + sum_j |branches j| = a*(ell-a)+1` and, under disjointness,
`1 + |union_j branches j| = a*(ell-a)+1`.  The admissible nonbase extension
`AoyagiLemma5SuppliedAdmissibleNonbaseFamily` carries explicit Lemma 4 witness
obligations and proves `branch_twoValueCount` for each supplied branch.  This
is not a construction of the branch family and not a source-backed proof from
printed equations `(3)`, `(4)`, or `(5)`.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-supplied-chart-family-count-boundary-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-supplied-chart-family-count-boundary.md`,
and
`threads/05-arithmetic-tail/review-lemma5-supplied-chart-family-count-boundary-a5.md`.

The supplied chart-family boundary now also has an explicit base-branch
wrapper.  In `lean/DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean`,
`AoyagiLemma5SuppliedNonbaseFamily.fullBranches` is the finite set
`{none} union union_j {some b : b in branches j}`, and
`AoyagiLemma5SuppliedNonbaseFamily.fullBranches_card` proves its cardinality is
`a*(ell-a)+1` under the same supplied nonbase boundary.  The full admissible
structure `AoyagiLemma5SuppliedAdmissibleFamily` adds the base branch's
supplied `H`-chain, lower/upper chain bounds, and two-value increment
hypothesis; `base_twoValueCount` applies the existing Lemma 4 bridge to that
base branch.  This still does not construct the supplied family from Aoyagi's
printed equations.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-full-supplied-family-base-branch-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-full-supplied-family-base-branch.md`,
and
`threads/05-arithmetic-tail/review-lemma5-full-supplied-family-base-branch-a5.md`.

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
