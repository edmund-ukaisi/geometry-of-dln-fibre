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

## VM Rotation Flush - 2026-06-23

Current worktree:
`/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct`.
Current branch: `expedition/aoyagi-rlct`.  Base before this in-progress slice:
`5007a31 Route Definition 3 source data into final boundary`.

In-progress slice: A0 finite exponent-array arithmetic for the
post-Theorem-3 regular-variable count, under the narrow name
`jacobianPriorLossShift`.  This is certificate arithmetic only, not analytic
regular-coordinate additivity.

Lean status before rotation:

- `lean/DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean` was edited.
- Focused check passed:
  `cd lean && lake env lean DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean`.
- No full module build, full library build, sorry scan, xhigh review, commit,
  or push has been done for this slice yet.

New/changed Lean names in `NormalCrossingInterface.lean`:

```text
jacobianPriorLossShift
jacobianPriorLossShift_lossExp
jacobianPriorLossShift_jacobianPriorExp
activePairs_jacobianPriorLossShift
mem_activePairs_jacobianPriorLossShift
ratioAt_jacobianPriorLossShift_of_mem_activePairs
exponentMinimum_jacobianPriorLossShift
coordsInChartAtRatio_jacobianPriorLossShift
countInChartAtRatio_jacobianPriorLossShift
minCoordsInChart_jacobianPriorLossShift
minCountInChart_jacobianPriorLossShift
exponentOrder_jacobianPriorLossShift
```

Mathematical content:

- `jacobianPriorLossShift m` keeps `lossExp = k` unchanged and replaces
  `jacobianPriorExp = h` by `h + m*k`.
- Active pairs are unchanged.
- For active coordinates only,
  `(h + m*k + 1)/(2*k) = (h + 1)/(2*k) + m/2`.
- Therefore the finite exponent minimum shifts by `m/2`.
- The ratio-specific coordinate/count sets satisfy
  shifted count at `q + m/2` equals original count at `q`.
- Consequently `minCoordsInChart`, `minCountInChart`, and `exponentOrder` are
  preserved.

Artifacts already added/updated:

- Added
  `threads/02-analytic-interface/reproduction-normal-crossing-jacobian-prior-loss-shift-a0.md`.
- Added
  `threads/02-analytic-interface/statement-card-a0-normal-crossing-jacobian-prior-loss-shift.md`.
- Updated `threads/02-analytic-interface/thread.md`.
- Updated `threads/03-block-product-reduction/regular-suspension-plan.md`.
- Updated `priorities.md`.

Known remaining memory/docs work after resume:

- Add an xhigh review artifact for the new A0 slice after independent review.
- Update `claims.md` A0 card to include the finite shift slice.
- Update `theorem-ledger.md` A0 row and latest A0 update.
- Update this `synthesis.md` latest A0 section to include the completed slice.
- Possibly update the statement-card verification block after full checks.

Recommended next steps after resume:

1. Re-check status in the Aoyagi worktree:
   `git status --short --branch`.
2. Spawn an xhigh reviewer for the finite scope: audit source boundary, Lean
   names, active-coordinate guard, and nonclaims.
3. Incorporate review notes and add
   `review-normal-crossing-jacobian-prior-loss-shift-a0.md`.
4. Run:
   `cd lean && lake build DLNFibre.DLN.Aoyagi.NormalCrossingInterface`.
5. Run:
   `cd lean && LAKE_JOBS=1 lake build DLNFibre`.
6. Run:
   `cd lean && lake env lean DLNFibre.lean`.
7. Run:
   `cd lean && scripts/sorries`.
8. Run:
   `git diff --check`.
9. Commit and push to `origin expedition/aoyagi-rlct` if clean.

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

## Latest A0 Update

The finite normal-crossing exponent interface has landed in
`lean/DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean`, imported by
`lean/DLNFibre.lean`.  It proves the finite arithmetic layer of Aoyagi's
PDF pp. 5-6 extraction formula:

- `AoyagiNormalCrossingExponentData` records finite chart/coordinate indices,
  natural loss exponents `k`, natural Jacobian/prior exponents `h`, and a
  nonempty active coordinate set;
- `activePairs` filters by `0 < k`, so zero-loss-exponent coordinates do not
  enter a denominator;
- `exponentMinimum` is the finite minimum of `(h+1)/(2*k)` over active pairs;
- `minCoordsInChart` and `exponentOrder` count coordinates attaining the
  global minimum chartwise and then take the maximum over charts;
- `AoyagiNormalCrossingExtractionHypothesis` is the explicit cited-boundary
  assumption equating external `lambda, theta` with these finite values.

Artifacts:
`threads/02-analytic-interface/reproduction-normal-crossing-exponent-interface-a0.md`,
`threads/02-analytic-interface/statement-card-a0-normal-crossing-exponent-interface.md`,
and
`threads/02-analytic-interface/review-normal-crossing-exponent-interface-a0.md`.
This is not an analytic theorem and does not prove chart production, unit
nonvanishing, Aoyagi Lemma 1, regular-coordinate additivity, Theorem 4, pole
order, or RLCT extraction.

Latest A0 finite-certificate update: `NormalCrossingInterface.lean` now also
contains min/max certificate lemmas for the supplied exponent data.  The
minimum can be proved from a candidate active ratio plus a lower bound against
all active ratios, or from an active coordinate realizing the candidate value
plus lower bounds against all active coordinates.  The order can be proved
from a candidate chart count plus an upper bound against all chart counts, or
from a realizing chart plus uniform chart-count upper bound:
`AoyagiNormalCrossingExponentData.exponentMinimum_eq_of_mem_activeRatios_of_forall_le`,
`AoyagiNormalCrossingExponentData.exponentMinimum_eq_of_activePair_ratioAt_eq_of_forall_le`,
`AoyagiNormalCrossingExponentData.exponentOrder_eq_of_mem_chartMinCounts_of_forall_le`,
`AoyagiNormalCrossingExponentData.exponentOrder_eq_of_chart_minCount_eq_of_forall_le`,
and
`AoyagiNormalCrossingExponentData.exponentOrder_eq_of_forall_le_of_exists_chart_minCount_eq`.
This is finite `Finset.min'`/`Finset.max'` bookkeeping only; it does not
construct charts, prove the active-ratio inequalities from the blow-up
recursion, identify chart counts with Lemma 5 terminal labels, prove pole
order without A0, or extract RLCT.
Artifacts:
`threads/02-analytic-interface/reproduction-normal-crossing-finite-certificates-a0.md`
and
`threads/02-analytic-interface/statement-card-a0-normal-crossing-finite-certificates.md`.
Review:
`threads/02-analytic-interface/review-normal-crossing-finite-certificates-a0.md`.

Latest A0 ratio-chart-count update: `NormalCrossingInterface.lean` now exposes
`coordsInChartAtRatio`, `countInChartAtRatio`, and rewrite/order-certificate
lemmas from counts at a candidate ratio to the existing global-minimum chart
counts once `D.exponentMinimum = q` is known.  This is finite definitional
bookkeeping only; it does not construct charts, source-prove chart counts, or
move pole order/RLCT extraction.
Artifacts:
`threads/02-analytic-interface/reproduction-normal-crossing-ratio-chart-counts-a0.md`
and
`threads/02-analytic-interface/statement-card-a0-normal-crossing-ratio-chart-counts.md`.
Review:
`threads/02-analytic-interface/review-normal-crossing-ratio-chart-counts-a0.md`.

Latest A0 Jacobian/prior loss-shift update: `NormalCrossingInterface.lean` now
also exposes `jacobianPriorLossShift`.  The operation keeps loss exponents
`k` fixed and replaces each Jacobian/prior exponent `h` by `h + m*k`.  Lean
proves that, on active coordinates, ratios shift by `m/2`; therefore the finite
exponent minimum shifts by `m/2`.  It also proves that ratio-specific chart
counts shift from `q` to `q + m/2`, and that `minCoordsInChart`,
`minCountInChart`, and `exponentOrder` are preserved.  This is the finite
certificate-arithmetic socket motivated by Aoyagi PDF p. 13's regular-variable
count, not a regular-coordinate chart construction or analytic RLCT additivity
theorem.
Artifacts:
`threads/02-analytic-interface/reproduction-normal-crossing-jacobian-prior-loss-shift-a0.md`
and
`threads/02-analytic-interface/statement-card-a0-normal-crossing-jacobian-prior-loss-shift.md`.
Review:
`threads/02-analytic-interface/review-normal-crossing-jacobian-prior-loss-shift-a0.md`.

## Latest A2 Update

The residual-product endpoint wrapper for Aoyagi Theorem 3 has landed.
Pen-and-paper reproduction:
`threads/03-block-product-reduction/reproduction-a2-residual-product.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-residual-product.md`.
Review:
`threads/03-block-product-reduction/review-a2-residual-product.md`.

Lean names:
`ChartLocalSuffixState.residualProduct`,
`ChartLocalSuffixState.residualProduct_self`,
`ChartLocalSuffixState.residualProduct_castSucc`,
`ChartLocalSuffixState.suffixState_D_eq_residualProduct`,
`ChartLocalSuffixState.suffixState_blockDiagonal_exists_triangularBlockDiagonal_residualProduct`,
`productReduction_chartLocal_suffixChain_triangularBlockDiagonal_residualProduct_indexed`, and
`PaperEndpointFixedBaseProductReductionCertificate.exists_triangularBlockDiagonal_residualProduct`.
The fixed-base endpoint theorem now exposes the lower-right block in the
triangular block-diagonal certificate as the deterministic product of
transformed Schur residual blocks visited by `suffixState`. This extends the
previous triangular-multiplier wrapper, where the right multiplier is still
realized by the proof witness `F2 = -S.B`.

The product is not the raw lower-right edge-block product. The abstract
suffix-chain theorem still carries the stronger all-`Bprev` determinant-chart
hypothesis, although the proof only uses recursively visited `Bprev` values.
Nonclaims remain: no chart coverage from only source rank hypotheses, no
exact-rank openness, no Aoyagi Lemma 1/analytic ideal transport, no
regular-coordinate RLCT additivity, no normal crossings, and no RLCT
consequence.

The fixed-base/source-rank-stratum endpoint wrapper has now landed.  New Lean
names in `ProductReductionBoundary.lean`:
`PaperEndpointFixedBaseTriangularResidualProductSourceRanks` and
`PaperEndpointFixedBaseProductReductionCertificate.exists_triangularBlockDiagonal_residualProduct_sourceRanks`.
It combines the existing triangular residual-product endpoint theorem with the
existing source-stratum residual-rank theorem: on
`paperEndpointFixedBaseSourceRankStratum`, the endpoint block form exposes
`ChartLocalSuffixState.residualProduct`, and each visited residual block has
rank `rEdge p - r`.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-source-rank-stratum-theorem3-boundary.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-source-rank-stratum-theorem3-boundary.md`.
Review:
`threads/03-block-product-reduction/review-a2-source-rank-stratum-theorem3-boundary.md`.

This is still a fixed-base, certificate-relative wrapper.  The source rank
stratum is repo terminology for Aoyagi's fixed layer-rank restrictions; it is
not an ambient open neighborhood, nonemptiness theorem, or source-produced
regular-corner chart theorem.  Do not rewrite the residual product as a raw or
paper-order block product without a separate orientation bridge.

## Latest A5 Update

The Eq5 alpha-indexed branch source-label slice has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  Lean now proves:
`aoyagiLemma5Eq5_alphaIndexedBranch_actualWidthLabel_of_widthBound`,
`aoyagiLemma5Eq5_alphaIndexedBranchLabel_mem_actualWidthLabelFinset_of_widthBound`,
and `aoyagiLemma5Eq5_alphaIndexedBranchLabel_injOn`.

This packages a supplied finite Eq5 strict-offset branch family branchwise:
if each branch alpha lies in the strict Eq5 alpha domain, the supplied Sigma
label's source coordinate is in range, the selected width is bounded by the
actual width at that source coordinate, and the label is
`Htilde'_p+1-alpha`, then the label is an actual-width label and belongs to
`actualWidthLabelFinset`.  If the supplied alpha projection is injective on
the branch family, the supplied Sigma-valued branch-label map is injective.

Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-indexed-branch-source-label-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-alpha-indexed-branch-source-label.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-alpha-indexed-branch-source-label-a5.md`.
This is source-label and finite injection packaging only: no Eq5 branch
construction, no alpha-domain coverage, no selected-span coverage, no
displayed-vector construction, no terminal exactness, no classifier/back-to-
label coverage, no pole order, no normal crossings, and no RLCT extraction.

The Eq5 alpha-indexed branch-label image wrapper has also landed in the same
file.  New Lean names:
`aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_subset_actualWidthLabelFinset_of_widthBound`
and `aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_card_eq_of_alphaInj`.
The first theorem upgrades branchwise actual-width-label membership to the
finite image subset
`branches.image branchLabel ⊆ actualWidthLabelFinset L n`; the second counts
that supplied image under supplied alpha injectivity.  This is image-level
bookkeeping only: no branch construction, alpha-domain coverage, selected-span
coverage, terminal exactness, classifier/back-to-label coverage, pole order,
normal crossings, or RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-indexed-branch-label-image-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-alpha-indexed-branch-label-image.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-alpha-indexed-branch-label-image-a5.md`.

The Eq5 alpha-indexed branch cardinal-bound wrapper has now landed in the same
file.  New Lean names:
`aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_card_le_actualWidthLabelFinset_card`
and `aoyagiLemma5Eq5_alphaIndexedBranch_card_le_actualWidthLabelFinset_card`.
The first theorem converts the branch-label image subset into an image
cardinality bound.  The second combines that bound with supplied alpha
injectivity to bound the supplied branch-family cardinality by
`(actualWidthLabelFinset L n).card`.  This is finite supplied-cardinality
bookkeeping only: no branch construction, alpha-domain coverage,
selected-span coverage, terminal exactness, classifier/back-to-label
coverage, pole order, normal crossings, or RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-indexed-branch-card-bound-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-alpha-indexed-branch-card-bound.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-alpha-indexed-branch-card-bound-a5.md`.

The Eq5 alpha-indexed offset-cardinality bridge has now landed in the same
file.  New Lean name:
`aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_card_eq_offsetValueSet_card`.
Under supplied alpha-domain image coverage and supplied alpha injectivity, the
branch-label image has the same cardinality as the strict Eq5 offset-value
set.  This counts both sides through the strict alpha domain.  It is not a set
equality or explicit bijection between Sigma-valued branch labels and integer
offset values, and it does not prove branch construction, source-label
legality, actual-width coverage, terminal exactness, classifier/back-to-label
coverage, pole order, normal crossings, or RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-indexed-offset-card-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-alpha-indexed-offset-card.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-alpha-indexed-offset-card-a5.md`.

The terminal branch introduced-domain capacity wrapper has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`.  New Lean names:
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_card_le_introducedLabelFinset_card`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches_card_le_introducedLabelFinset_card_of_branchLabel_injOn`,
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.suppliedBranchCount_le_introducedLabelFinset_card_of_branchLabel_injOn`.
The first theorem bounds the supplied branch-label image by the current
introduced-label domain.  The second and third use supplied branch-label
injectivity and the supplied family count to show the introduced domain has
room for the supplied branch count `a*(n+1-a)+1`.  This is a conditional
capacity statement only: no branch-label injectivity proof, no no-extra
terminal-minimum coverage, no terminal-minimum count, pole order, normal
crossings, or RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-branch-introduced-domain-capacity-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-branch-introduced-domain-capacity.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-branch-introduced-domain-capacity-a5.md`.

The terminal-minimum lower-bound wrapper has also landed in
`Lemma5TerminalBridge.lean`.  New Lean names:
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_card_le_terminalMinimumLabels_card`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches_card_le_terminalMinimumLabels_card_of_branchLabel_injOn`,
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.suppliedBranchCount_le_terminalMinimumLabels_card_of_branchLabel_injOn`.
These prove only the easy lower-bound direction: supplied candidates attain
the minimum, so under supplied branch-label injectivity the supplied branch
count `a*(n+1-a)+1` is at most `C.terminalMinimumLabels.card`.  This is not
the no-extra upper bound, exact terminal-minimum cardinality, pole order,
normal crossings, or RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-minimum-lower-bound-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-minimum-lower-bound.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-minimum-lower-bound-a5.md`.

The upper-bound classifier exactness wrappers have also landed in
`Lemma5TerminalBridge.lean`.  New Lean names:
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_eq_branchLabelImage_of_upperBoundClassifier`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_iff_branchLabel_injOn_and_upperBoundClassifier`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_upperBoundClassifier_and_branchLabel_injOn`,
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_bijOn_terminalMinimumLabels_of_upperBoundClassifier`.
These prove that the supplied `UpperBoundClassifier` identifies
`terminalMinimumLabels` with `branchLabelImage`; adding supplied branch-label
injectivity gives the exactness package, bijection, and exact finite count.
This is supplied finite API only: the classifier and injectivity are not
constructed from Aoyagi's source, and no pole order, normal crossings, or RLCT
extraction follows.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-upper-bound-classifier-exactness-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-upper-bound-classifier-exactness.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-upper-bound-classifier-exactness-a5.md`.

The counted-datum classifier cardinal-squeeze wrappers have landed in
`Lemma5TerminalBridge.lean`.  New Lean names:
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_eq_branchLabelImage_of_countDatumClassifier_and_branchLabel_injOn`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_countDatumClassifier_and_branchLabel_injOn`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_countDatumClassifier_and_branchLabel_injOn`,
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_bijOn_terminalMinimumLabels_of_countDatumClassifier_and_branchLabel_injOn`.
These derive terminal-minimum exactness from a supplied counted-datum
classifier and supplied branch-label injectivity by finite cardinality
squeeze.  This avoids an explicit counted-datum back-to-label witness, but the
classifier and injectivity remain supplied and no source construction, pole
order, normal crossings, or RLCT extraction follows.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-classifier-cardinal-squeeze-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-counted-datum-classifier-cardinal-squeeze.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-counted-datum-classifier-cardinal-squeeze-a5.md`.

The Eq5 nonfirst-block explicit-bounds wrapper has landed in
`Lemma5DisplayedVector.lean`.  New Lean names:
`aoyagiLemma5Eq5_nonfirstBlock_bounds_of_alphaDomain_of_postPLowerGuard`
and
`aoyagiLemma5Eq5_nonfirstBlock_bounds_of_alphaDomain_of_terminalRoom`.
These unwrap the existing nonfirst Eq5 interval-membership theorem into the
vectorwise Htilde inequalities `Htilde_b <= T S <= Htilde'_b`, under the same
supplied Eq5 piecewise certificate, strict alpha domain, nonfirst-block
hypothesis, and either the explicit post-`p` lower guard or terminal-room
inequality.  This is only same-coordinate interval bookkeeping: it does not
construct Eq5 vectors, prove source-label legality, produce the post-`p` guard
from source hypotheses, prove terminality, classifier/back-to-label coverage,
pole order, normal crossings, or RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-nonfirst-block-bounds-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-nonfirst-block-bounds.md`.

## Latest A6 Update

The first A6 formula-notation slice has landed in
`lean/DLNFibre/DLN/Aoyagi/FinalFormula.lean`, imported by `lean/DLNFibre.lean`.
It translates Aoyagi Definition 3 and Theorem 2 from PDF pp. 8-9 without using
the quiver paper and without claiming an RLCT theorem.

Lean now has integer reduced widths
`aoyagiReducedWidthInt H r s = (H s : Int) - r`.  The dimension/rank
convention map now adds local bridge lemmas showing that under explicit
`r <= H s`, this integer width is Nat subtraction coerced to `Int` and is
nonnegative; selected reduced widths and the Nat-indexed Lemma 5 selected
width accessor have the corresponding pointwise wrappers.  Lean also has
indexed selected widths through `AoyagiSelectedCutpoints`, the selected
value-set helper `aoyagiSelectedWidthValueSet`, and the supplied Definition 3
package
`AoyagiDefinition3CeilData`.  The package separates Aoyagi's selected object
from the ceiling integer `ceilWidth`, and records `0 < ell`, `0 < aParam`,
`aParam <= ell`, and
`sum selected = ell*(ceilWidth-1)+aParam`.

The displayed Theorem 2 order is named
`AoyagiDefinition3CeilData.theorem2OrderFormula`, not `theta`, because
Aoyagi's `theta` is pole order/multiplicity rather than the repository's
component-count convention.  The three displayed `lambda` forms are named
`aoyagiTheorem2Lambda_average`, `aoyagiTheorem2Lambda_ceil`, and
`aoyagiTheorem2Lambda_expanded`.  Lean proves the finite rewrites
`AoyagiDefinition3CeilData.selectedWidthAverage_eq_ceil`,
`aoyagiTheorem2Lambda_average_eq_fromCeilData`,
`aoyagiTheorem2Lambda_ceil_eq_expanded`, and
`aoyagiTheorem2Lambda_average_eq_expanded_ofCeilData`.

Artifacts:
`threads/06-dln-translation/reproduction-definition3-theorem2-translation-a6.md`,
`threads/06-dln-translation/reproduction-dimension-rank-convention-a6.md`,
`threads/06-dln-translation/statement-card-a6-final-formula-notation.md`, and
`threads/06-dln-translation/statement-card-a6-dimension-rank-convention.md`,
`threads/06-dln-translation/review-final-formula-notation-a6.md`, and
`threads/06-dln-translation/review-dimension-rank-convention-a6.md`.

Nonclaims: no full Definition 3 selection inequalities, no existence or
uniqueness of the selected cutpoints or ceiling datum, no proof of the
rank-width inequalities from a concrete matrix product, no Lemma 4/Lemma 5
exponent-to-formula bridge, no normal crossings, no pole-order
interpretation, and no RLCT extraction.

The Definition 3 bridge slice now also lands in
`lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`.  It consumes
`AoyagiDefinition3CeilData` in the existing Lemma 4/Htilde API, proving
`one_le_ell`, `one_le_aParam`, `terminalEndpoint_eq_zero`, lower/upper chain
terminal zeros, Nat-indexed terminal zeros,
`htildeUpperNat_pred_eq_sub_lastWidth`, and
`Hlast_eq_zero_of_htildeChainBounds`.  It also provides finite count/order
formula handoffs
`intervalSize_excess_sum_Icc_eq_theorem2OrderFormula` and
`htildeIntervalValueSetNat_excess_sum_Icc_eq_theorem2OrderFormula`, terminal
same-coordinate/Eq5 wrappers
`htildeIntervalValueSetNat_terminal_eq_singleton_zero` and
`suppliedTerminalZero_Eq5_offsets_eq_intervalValueSetNat`, and the Lemma 4
count handoff `lemma4_twoValueCount_of_htildeChainBounds` under supplied
chain bounds and supplied two-value increments.  Source-selected-inequality
wrappers now include selected-width upper bounds, equation `(4)` local data,
and equation `(5)` label bounds; equation `(3)` local data remains available
only with the explicit one-unit slack hypothesis.  The strict selected
inequality remains an explicit hypothesis rather than a field of the ceiling
datum.

Artifacts:
`threads/06-dln-translation/reproduction-definition3-lemma4-bridge-a6.md`,
`threads/06-dln-translation/statement-card-a6-definition3-bridge.md`, and
`threads/06-dln-translation/review-definition3-bridge-a6.md`.

Nonclaims for the bridge: no full Definition 3 selection package, no
displayed-vector construction, no Lemma 4 two-value increment proof, no Lemma
5 chart-family coverage, no terminal-minimum classifier, no conversion of the
finite count into Aoyagi's pole-order symbol, no normal crossings, and no RLCT
extraction.

The Definition 3 source-data ceiling slice has also landed in
`Definition3Bridge.lean`.  New Lean names:
`AoyagiDefinition3SourceData`,
`AoyagiDefinition3CeilData.nonempty_of_ell_pos`, and
`AoyagiDefinition3SourceData.exists_ceilData`.  The generic constructor proves
that any integer selected-width family and `0 < ell` determine Definition 3's
`ceilWidth` and `aParam` by Euclidean division, with
`sum selected = ell*(ceilWidth-1)+aParam` and `0 < aParam <= ell`.  The
source-data wrapper records supplied selected cutpoints, value-level selected
dominance, selected strict inequalities, and value-level nonselected
inequalities from Definition 3, then produces the ceiling datum and carries the
strict selected inequality forward.  Reproduction:
`threads/06-dln-translation/reproduction-definition3-source-data-ceil-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-source-data-ceil.md`.
Review:
`threads/06-dln-translation/review-definition3-source-data-ceil-a6.md`.
This removes only the supplied ceiling/residue datum; it does not construct or
prove uniqueness of selected cutpoints or the selected value set.

The Definition 3 source-data local-wrapper slice now also lands in
`Definition3Bridge.lean`.  It projects the strict selected inequality already
stored in `AoyagiDefinition3SourceData` into the existing local Lemma 5
arithmetic wrappers and packages, under an explicit source-range rank-width
hypothesis, the selected reduced widths with their ceiling datum, Nat-width
rewrites, nonnegativity, strict selected inequality, and selected-width upper
bound.  This is source-data aggregation only: selected cutpoints and
rank-width hypotheses remain supplied, and no Lemma 5 coverage/no-extra
exactness, chart production, pole order, or RLCT is proved.

The Definition 3 source-data final-boundary handoff now lands in
`Theorem2FinalAssembly.lean`.  It consumes the source-data provenance
aggregator to existentially produce `m` and `data`, then packages them into
the supplied final-boundary and chart-final-boundary structures when the A0
extraction hypothesis and finite exponent formula hypothesis are supplied for
the produced data.  This reduces bare selected-width provenance at the final
socket, but selected cutpoints, source data, source-range rank-width,
active-ratio/chart-count facts, chart production, pole order, and RLCT remain
outside this theorem.

The conditional A0/A6 finite-exponent bridge has now landed in
`lean/DLNFibre/DLN/Aoyagi/Theorem2FiniteExponentBridge.lean`.  It introduces
`AoyagiTheorem2FiniteExponentFormulaHypothesis`, which supplies exactly the
two finite equalities still owed by a future normal-crossing certificate:

```text
D.exponentMinimum = aoyagiTheorem2Lambda_fromCeilData L ell H r m data,
D.exponentOrder   = data.theorem2OrderFormula.
```

Together with `AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder`,
Lean proves the ceiling-data, average, and expanded displayed `lambda`
formulas, plus the displayed order formula.  New Lean names:
`lambda_eq_theorem2Lambda_fromCeilData_of_extractionHypothesis`,
`lambda_eq_theorem2Lambda_average_of_extractionHypothesis`,
`lambda_eq_theorem2Lambda_expanded_of_extractionHypothesis`,
`poleOrder_eq_theorem2OrderFormula_of_extractionHypothesis`, and
`lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_extractionHypothesis`.
This is a conditional bridge only.  It does not prove source parameter
provenance `m = H(S_j)-r`, Definition 3 selection data, rank-width hypotheses,
chart coverage, unit factors, Jacobian/prior exponent correctness, terminal
minimum exactness, Lemma 5 order count, normal crossings, or analytic
extraction.

Artifacts:
`threads/06-dln-translation/reproduction-theorem2-finite-exponent-bridge-a6.md`,
`threads/06-dln-translation/statement-card-a6-theorem2-finite-exponent-bridge.md`,
and
`threads/06-dln-translation/review-theorem2-finite-exponent-bridge-a6.md`.

## Latest A4 Update

The displayed Case 2 free-`Cprime` continuing branch has landed.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-free-cprime-continuing-branch-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-free-cprime-continuing-branch.md`.
Review:
`threads/04-blow-up-certificate/review-case2-free-cprime-continuing-branch-a4.md`.

Lean names:
`case2DisplayedFreeCprimeTop`,
`case2DisplayedFreeCprimeTail`,
`case2DisplayedFreeCprime_eq_verticalBlock`,
`case2DisplayedPostPivotFreeFollowingFactor`,
`case2DisplayedPaperDppp_mul_freeCprime_postPivot_eq_nextSameStageProduct`,
`Case2DisplayedSuppliedChartFamilyBoundary.postPivotFreeCprimeNextSameStageProduct`,
and
`sourceChartMap_postPivotFreeCprimeNextSameStageProduct_withCorrectedPostData`.
This proves the finite block identity
`blockdiag(1,D-x*y)*[Ctop;Ctail] = [Ctop;(D-x*y)*Ctail]` after reindexing to
the continuing `(S,J+1)` domains, for an arbitrary compatible pivot-first
chart-coordinate matrix `Cprime`.

Nonclaims remain: no source production of `Cprime`, no chart coverage or
arbitrary-pivot coverage, no chart-produced recurrence/exponent data, no
transition invariant, no terminal relabeling, no normal crossings/RLCT, and no
repair of the printed Case 2 vector mismatch.

The next local product package has also landed.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-free-cprime-local-product-package-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-free-cprime-local-product-package.md`.
Review:
`threads/04-blow-up-certificate/review-case2-free-cprime-local-product-package-a4.md`.

Lean name:
`sourceChartMap_constructedSourceFreeCprimeLocalProduct_withCorrectedPostData`.
It pairs the constructed-source `Q/P` theorem for the old following factor
`Q*Cprime` with the separate bare lower-row identity for `D'''*Cprime` and the
corrected post-data projections.  The first product equality is weighted by
the successor row-weight diagonal; the lower-row post-pivot equality is stated
for bare `D'''*Cprime`.  This prevents a false identification of successor row
weights with the post-pivot residual block.

The weighted lower-row projection has also landed.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-weighted-free-cprime-lower-row-projection-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-weighted-free-cprime-lower-row-projection.md`.
Review:
`threads/04-blow-up-certificate/review-case2-weighted-free-cprime-lower-row-projection-a4.md`.

Lean names:
`weightedPivotDiagonal_mul_lowerRows`,
`weightedPivotDiagonal_mul_lowerRows_reindex`,
`case2DisplayedWeightedPaperDppp_mul_freeCprime_postPivot_eq_nextSameStageProduct`,
and
`Case2DisplayedSuppliedChartFamilyBoundary.postPivotWeightedFreeCprimeNextSameStageProduct`.
This fills the weighted projection gap left by the local product package:
lower rows of the weighted right side `diag(b') D''' Cprime` are the lower-row
successor-weight diagonal times the bare post-pivot product.  It still says
nothing about the pivot row, full successor products, chart production, or
analytic/RLCT content.

The source-side weighted lower-row handoff has also landed.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-side-weighted-lower-row-handoff-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-side-weighted-lower-row-handoff.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-side-weighted-lower-row-handoff-a4.md`.

Lean name:
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_constructedSourceFreeCprimeWeightedNextSameStageProduct_withCorrectedPostData`.
It projects the constructed-source weighted `Q/P` equality to lower rows and
then uses the weighted lower-row projection to rewrite the right side as the
successor lower-row diagonal times the bare post-pivot residual-block/free-
following-factor product, carrying the corrected post-data fields.  It keeps
the `P_q = weightedPivotBlockRowOp q` source-side operation explicit.  It is
not a full successor product, chart production, source production of
`Cprime`, transition invariance, terminal relabeling, normal crossings, pole
order, or RLCT content.

The paper-`Cprime` source-following weighted handoff has also landed.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-paper-cprime-source-following-weighted-handoff-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-paper-cprime-source-following-weighted-handoff.md`.
Review:
`threads/04-blow-up-certificate/review-case2-paper-cprime-source-following-weighted-handoff-a4.md`.

Lean names:
`case2DisplayedPostPivotFreeFollowingFactor_paperCprime_eq_sourceFollowingFactor_succ`
and
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_paperCprimeWeightedLowerRows_withCorrectedPostData`.
The theorem specializes the lower-row weighted source-side handoff to
Aoyagi's paper `C' = Q^-1 C` and rewrites only its lower tail as the next
same-stage source following factor.  It keeps the `P_q` row operation and
successor lower-row diagonal explicit and carries the corrected post-data
fields.  It is not a full successor product, chart production, source
production of `C'^(S+1)`, transition invariance, terminal relabeling, normal
crossings, pole order, or RLCT content.

The continuing weighted source-following payload has also landed in
`BlowupArithmetic.lean`.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-continuing-weighted-source-following-payload-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-continuing-weighted-source-following-payload.md`.
Review:
`threads/04-blow-up-certificate/review-case2-continuing-weighted-source-following-payload-a4.md`.

Lean names:
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_continuingWeightedSourceFollowingPayload_withFiniteCenterIdeal`,
`ContinuingWeightedSourceFollowingFrontierPayload`, and
`SourceChartFrontierBoundaryPackages.continuingWeighted`.
This packages the paper-`C'` weighted lower-row handoff with the finite
next-center nonemptiness guard and finite residual-center principalization,
under the explicit continuing hypothesis `J+2 <= prefixMinNat n (S+1)`.  It
keeps the pivot row out of the equality and keeps the successor lower-row
diagonal explicit.  It is not chart production, source production of
`C'^(S+1)`, source-produced post-data, a transition invariant, normal
crossings, pole order, or RLCT content.

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

The full supplied family now also has a single tagged-branch admissibility
wrapper.  `AoyagiLemma5SuppliedNonbaseFamily.some_mem_fullBranches_iff`
characterizes `some b in fullBranches` by existence of an interior coordinate
with `b in branches j`.  `AoyagiLemma5SuppliedAdmissibleFamily.fullH` defines
the branch chain by `fullH none = baseH` and `fullH (some b)=H b`, and
`AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_twoValueCount` proves Lemma
4's finite two-value count for every tagged branch under `a<=ell` and the
selected-width sum.  The proof only dispatches to supplied base or nonbase
fields; it does not reconstruct any branch from equations `(3)`, `(4)`, or
`(5)`.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-full-supplied-family-branchwise-admissibility-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-full-supplied-family-branchwise-admissibility.md`,
and
`threads/05-arithmetic-tail/review-lemma5-full-supplied-family-branchwise-admissibility-a5.md`.

The full supplied family now also has the first branchwise Lemma 3 minimum
consequence.  In `lean/DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean`,
`AoyagiLemma5SuppliedAdmissibleFamily.fullBranches_card_and_fullBranch_twoValueCount`
bundles the supplied family cardinality with the per-branch two-value count,
and
`AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_freeHighCount_lemma3A_eq_min`
proves that, when the total increment length is `n+1`, every tagged supplied
branch attains the isolated Lemma 3 numerator minimum in the free high-count
parameter over the first `n` increments.  This uses the existing Lemma 4
free-count bridge and does not identify the numerator with a terminal exponent
or `lambda`, prove terminal `tilde t=0`, construct source labels or displayed
vectors, prove chart coverage, normal crossings, or RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-full-supplied-family-free-count-minimum-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-full-supplied-family-free-count-minimum.md`,
and
`threads/05-arithmetic-tail/review-lemma5-full-supplied-family-free-count-minimum-a5.md`.

The supplied branch minimum is now connected to the generic terminal-exponent
certificate API in a new bridge file
`lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`.  The file defines the
named free count `aoyagiLemma4FreeHighCount`, restates the supplied branch
minimum as
`AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_freeHighCountMin`, and proves
`IntroducedLabelExponentCertificates.terminalExponent_eq_suppliedLemma5MinNumerator`.
The last theorem assumes a supplied numerator normalisation
`numerator s k = A(n+1,a,b_x)` and then derives
`terminalExponent = a*(n+1)*((n+1)-a)` from the exponent certificate and the
supplied branch minimum.  It does not prove terminal `tilde t=0`, derive the
quadratic rewrite from the PDF, construct source labels or displayed vectors,
identify `lambda`, prove chart coverage, normal crossings, or RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-minimum-numerator-bridge-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-minimum-numerator-bridge.md`,
and
`threads/05-arithmetic-tail/review-lemma5-terminal-minimum-numerator-bridge-a5.md`.

The bridge file now also packages a supplied terminal-candidate family:
`AoyagiLemma5SuppliedTerminalCandidateFamily`.  It attaches every tagged
supplied Lemma 5 branch to supplied source-label maps `branchS`, `branchK`,
an introduced-label proof, terminal least-value-zero data, and a numerator
normalisation to the Lemma 3 free-count expression.  Lean proves the inherited
branch count, branchwise terminal least-value zero, branchwise terminal
exponent equality to the isolated Lemma 3 minimum numerator, and the bundled
`branch_terminalCandidateData`.  This still does not construct source labels
from the printed equations, prove terminal `tilde t=0` from the chart process,
prove label injectivity/no-extra-terminal-minimizer data, identify `lambda`,
prove pole order, normal crossings, or RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-supplied-terminal-candidate-family-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-supplied-terminal-candidate-family.md`,
and
`threads/05-arithmetic-tail/review-lemma5-supplied-terminal-candidate-family-a5.md`.

The terminal bridge now also distinguishes a tagged branch count from a
distinct supplied-label image count.  `branchLabel` maps a tagged branch to its
supplied `Sigma.mk (branchS x) (branchK x)` label, and `branchLabelImage` is
the finite image of that map over `fullBranches`.  Lean proves each branch
label belongs to `introducedLabelFinset` and that the image is contained in
that finite introduced-label set.  Under an explicit `Set.InjOn branchLabel
fullBranches` hypothesis, Lean proves
`branchLabelImage.card = a*(n+1-a)+1`, and every label in that image inherits
the branchwise introduced-label, least-value-zero, and terminal-exponent
minimum data.  This is only a distinct supplied-candidate image count: it does
not prove injectivity from the source, coverage of all terminal minimizers, a
pole order, normal crossings, or RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-branch-label-image-count-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-branch-label-image-count.md`;
review:
`threads/05-arithmetic-tail/review-lemma5-branch-label-image-count-a5.md`.

The bridge now also has a finite exact-minimum label boundary.  It names the
minimum numerator as `aoyagiLemma5MinNumerator n a` and defines
`terminalMinimumLabels` as the introduced labels with `leastValue=0` and
terminal exponent equal to that numerator.  Lean proves the supplied
branch-label image is contained in this finite exact-minimum set.  Under the
explicit no-extra containment `terminalMinimumLabels subset branchLabelImage`
and supplied branch-label injectivity, Lean proves
`terminalMinimumLabels.card = a*(n+1-a)+1`.  This is still not pole order: the
reverse containment is supplied, and normal-crossing/RLCT extraction remains
outside this finite count.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-minimum-label-count-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-minimum-label-count.md`;
review:
`threads/05-arithmetic-tail/review-lemma5-terminal-minimum-label-count-a5.md`.

The terminal bridge now packages the two finite exactness hypotheses as
`TerminalMinimumLabelExactness`: branch-label injectivity on `fullBranches`
and no-extra containment from `terminalMinimumLabels` to `branchLabelImage`.
The wrapper `terminalMinimumLabels_eq_branchLabelImage_of_exactness` derives
the finite equality, and `terminalMinimumLabels_card_of_exactness` derives the
finite count `a*(n+1-a)+1` from this package, `a<=n+1`, and the selected-width
sum.  This is only a reuse package; exactness remains supplied, and no Lean
normal-crossing/RLCT extraction interface has been introduced.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-minimum-label-exactness-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-minimum-label-exactness.md`;
review:
`threads/05-arithmetic-tail/review-lemma5-terminal-minimum-label-exactness-a5.md`.

A source audit now isolates the next A5 frontier.  Aoyagi Lemma 5's
upper-bound paragraph on PDF p. 26 asserts a finite count of lambda-vectors by
interval data and the Case 1(2) statement that `J` increases by one, but this
has not yet been reproduced as a source-backed classifier and does not
discharge Lean's no-extra containment
`terminalMinimumLabels subset branchLabelImage`.  The missing bridges are:
label-to-vector, minimum-to-lambda, interval classifier, Case 1(2)
uniqueness/injection, and back-to-label.  Until those are reproduced or
explicitly supplied, `TerminalMinimumLabelExactness` remains supplied finite
data.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-exactness-source-audit-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-exactness-source-frontier.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-exactness-frontier-and-bijon-a5.md`.

The terminal bridge also now exposes the same supplied finite boundary through
standard bijection language.  The theorem
`branchLabel_bijOn_terminalMinimumLabels_of_exactness` converts packaged
exactness to `Set.BijOn branchLabel fullBranches terminalMinimumLabels`;
`terminalMinimumLabelExactness_of_branchLabel_bijOn` converts a supplied
bijection back to exactness; and
`terminalMinimumLabels_card_of_branchLabel_bijOn` gets the finite count from a
supplied bijection and `a<=n+1`.  This is an API wrapper below the source
frontier, not a source-backed construction of the bijection.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-minimum-label-bijon-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-minimum-label-bijon.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-exactness-frontier-and-bijon-a5.md`.

The terminal bridge now also names the no-extra direction as a supplied
upper-bound classifier.  `UpperBoundClassifier C` says every label in
`C.terminalMinimumLabels` is the supplied label of some branch in
`C.fullBranches`.  Lean proves the containment
`terminalMinimumLabels subset branchLabelImage`, the upper cardinal inequality
`terminalMinimumLabels.card <= a*(n+1-a)+1` without branch-label injectivity,
and a conversion from this classifier plus injectivity to
`TerminalMinimumLabelExactness`.  This is deliberately weaker than a
source-backed Lemma 5 upper-bound proof: the label-to-vector,
minimum-to-lambda, interval classifier, Case 1(2) uniqueness, and
back-to-label bridges remain open.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-upper-bound-classifier-interface-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-upper-bound-classifier-interface.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-upper-bound-classifier-interface-a5.md`.

The source-independent counted-data codomain for the Lemma 5 upper bound is
now Lean-proved in `Lemma5SuppliedFamily.lean`.  The new names are
`AoyagiLemma5CountDatum`, `aoyagiLemma5CountDatumNonbaseSet`,
`aoyagiLemma5CountDatumSet`, `some_mem_aoyagiLemma5CountDatumSet_iff`,
`aoyagiLemma5CountDatumNonbaseSet_card`, and
`aoyagiLemma5CountDatumSet_card`.  Given a supplied base value in every
interior same-coordinate interval, the set with one base datum and all tagged
nonbase interval values has cardinality `a*(ell-a)+1`.  This is only the
counted codomain; it does not classify source vectors, construct branches, or
connect to terminal labels.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-set-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-counted-datum-set.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-counted-datum-set-a5.md`.

The label-free counted-datum codomain now has a source-facing supplied
classifier boundary.  `AoyagiLemma5CountDatumClassifier` takes an abstract
finite candidate set, a classifier into the counted datum set, a maps-to proof,
and injectivity on candidates; `candidates_card_le` proves the upper count
`candidates.card <= a*(ell-a)+1`.  This isolates exactly the missing part of
Aoyagi Lemma 5's upper-bound paragraph: source candidates and an injective
classification into interval data remain supplied, not PDF-derived.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-classifier-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-counted-datum-classifier.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-counted-datum-classifier-a5.md`.

The interval-membership arithmetic now has a prefix-delta landing point.
`aoyagiHtildeChainBounds_of_incrementPrefix_bounds` proves that supplied
bounds
`min(a,j-(ell-a)) <= D_j <= min(j,a)` on
`D_j=P_j-H_j-j*(M-1)` imply `Htilde <= H <= Htilde'`.
`aoyagiHtilde_interval_mem_of_incrementPrefix_bounds` then gives membership
in the same-coordinate interval value set under `a<=ell`.  This does not prove
those prefix-delta bounds from binary increments; it only isolates the
algebraic translation needed by the future source-classifier work.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-prefix-delta-chain-bounds-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-prefix-delta-chain-bounds.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-prefix-delta-chain-bounds-a5.md`.

The supplied prefix-delta bounds are now produced from terminal binary prefix
deltas.  `aoyagiIntegerPrefix_binaryDelta_bounds` proves the elementary
finite statement: if a sequence has binary successive deltas, starts at `0`,
ends at `a`, and `a<=ell`, then
`min(a,j-(ell-a)) <= D_j <= min(j,a)` for every `j<=ell`.
The Aoyagi wrappers
`aoyagiLemma4IncrementPrefix_bounds_of_terminalH_binaryIncrementPrefixDelta`,
`aoyagiHtildeChainBounds_of_terminalH_binaryIncrementPrefixDelta`, and
`aoyagiHtilde_interval_mem_of_terminalH_binaryIncrementPrefixDelta` use
`H_0=m_0`, terminal `H_ell=0`, the selected-width sum, and a supplied
binary-delta hypothesis to derive displayed `Htilde` chain bounds and
same-coordinate interval membership.  This still does not prove binary deltas
from source exponent vectors or the Lemma 5 upper-bound classifier.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-binary-prefix-delta-bounds-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-binary-prefix-delta-bounds.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-binary-prefix-delta-bounds-a5.md`.

Ptolemy's source probe of Aoyagi PDF pp. 25-27 confirms the full Lemma 5
upper-bound/no-extra classifier is still not source-proved.  The interval
count and the sentence that Case 1(2) increases `J` do not themselves supply a
classifier, injection, or back-to-label map.  Field status: label-to-vector is
conditional; minimum-to-lambda is conditional/obstructed from pp. 25-27 alone;
the interval classifier is available only as `mapsTo` under explicit
source-chain hypotheses; Case 1(2) uniqueness/injection and back-to-label are
obstructed as printed.
Artifact:
`threads/05-arithmetic-tail/source-probe-lemma5-classifier-fields-a5.md`.

Lovelace's API probe identifies the next clean Lean slice below the classifier
frontier: construct `AoyagiLemma5SuppliedNonbaseFamily` from coordinate-wise
raw value coverage by filtering out the supplied base value, then bridge such
a supplied family to `AoyagiLemma5CountDatumClassifier` using a supplied branch
coordinate and injectivity of the tagged classifier.  The probe also warns
that existing equation `(3)`/`(4)`/`(5)` value coverage is currently
one-coordinate/rising-region only, so full-coordinate coverage remains supplied
unless plateau/falling-coordinate data are added.
Artifact:
`threads/05-arithmetic-tail/api-probe-lemma5-coordinate-coverage-classifier-a5.md`.

The supplied Lemma 5 admissible-family boundary now has a binary-prefix input
form in `Lemma5SuppliedFamily.lean`.  The new structures
`AoyagiLemma5SuppliedBinaryNonbaseFamily` and
`AoyagiLemma5SuppliedBinaryFamily` keep branch coverage/nonduplication
supplied, but replace explicit per-branch `Htilde` bounds and two-valued
increments by `H_0=m_0`, terminal `H_ell=0`, and binary prefix deltas.
The conversions
`AoyagiLemma5SuppliedBinaryNonbaseFamily.toAdmissibleNonbaseFamily` and
`AoyagiLemma5SuppliedBinaryFamily.toAdmissibleFamily` derive the existing
admissible-family boundary from the binary-prefix arithmetic under `a<=ell`
and the selected-width sum.  The direct binary accessors
`AoyagiLemma5SuppliedBinaryFamily.fullBranches` and `.fullH` support the
wrapper
`AoyagiLemma5SuppliedBinaryFamily.fullBranches_card_and_fullBranch_twoValueCount`.
This is still a supplied-data conversion, not source construction or the
no-extra classifier.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-binary-supplied-family-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-binary-supplied-family.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-binary-supplied-family-a5.md`.

The coordinate-coverage classifier boundary now also exists in
`Lemma5SuppliedFamily.lean`.  `finset_image_filter_value_ne_eq_erase_image`
proves the elementary finite-set identity for filtering one value from an
image.  `AoyagiLemma5SuppliedNonbaseFamily.ofCoordinateValueCoverage` uses it
to build a nonbase family from supplied coordinate-wise raw value coverage,
injectivity, base-value membership, and disjointness.  Finally,
`AoyagiLemma5SuppliedNonbaseFamily.countDatumOfBranchCoord` names the tagged
classifier map, and
`AoyagiLemma5SuppliedNonbaseFamily.countDatumClassifierOfBranchCoord` builds
an `AoyagiLemma5CountDatumClassifier` from a supplied branch-coordinate map
and supplied injectivity of that named classifier.  This proves the `mapsTo`
field only; source coverage and Case 1(2) nonduplication remain supplied.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-coordinate-coverage-classifier-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-coordinate-coverage-classifier.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-coordinate-coverage-classifier-a5.md`.

The counted-datum classifier now has a supplied-family injection proof.
`AoyagiLemma5SuppliedNonbaseFamily.countDatumOfBranchCoord_injOn` proves that
the tagged map `none |-> none`, `some b |-> (branchCoord b, value b)` is
injective on `F.fullBranches` whenever the supplied coordinate map is correct
on each `F.branches j`.  The proof uses the existing supplied
`value_injective` field; it does not derive that field from the source.
`countDatumClassifierOfBranchCoord_of_branchCoord_eq` builds
the classifier without a separate injectivity hypothesis, and the binary full
family now exposes binary-nonbase and full-family
`countDatumOfBranchCoord`/`countDatumClassifierOfBranchCoord` wrappers through
the same underlying nonbase-family proof.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-injection-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-counted-datum-injection.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-counted-datum-injection-a5.md`.

The displayed-vector file now has the non-rising counterpart to the earlier
rising-region Eq5 offset coverage.  The new theorem
`aoyagiLemma5Eq5_offsets_eq_interval_erase_upper_of_excess_le_pred` proves
that if `aoyagiLemma5IntervalExcess ell a p <= p-1`, then the strict Eq5
offset values equal the same-coordinate interval with the upper endpoint
erased.  `aoyagiLemma5_suppliedUpper_Eq5_offsets_eq_intervalValueSetNat_of_excess_le_pred`
then fills the interval from any supplied upper endpoint, and
`aoyagiLemma5_suppliedEq3Upper_Eq5_offsets_eq_intervalValueSetNat_of_plateau`
and its `...Eq3UpperComponent...` alias instantiate this in the plateau
subcase `a<p<=ell-a` from a supplied Eq3-shaped component value.  This is
finite set bookkeeping only; source-label legality and terminal/chart data
remain open.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-nonrising-coverage-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-nonrising-coverage.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-nonrising-coverage-a5.md`.

The Eq5 endpoint-deficit split is now Lean-proved in
`Lemma5DisplayedVector.lean`.  The arithmetic theorem
`aoyagiLemma5IntervalExcess_eq_self_iff_le_min` identifies the rising region
as exactly `p<=a` and `p<=ell-a`, and
`aoyagiLemma5IntervalExcess_le_pred_of_not_le_min` gives the non-rising
complement for `1<=p`.  The cardinal theorem
`aoyagiLemma5Eq5_intervalCard_eq_offsetCard_add_endpointDeficit` states that
the interval size is the Eq5 offset count plus one upper-endpoint deficit, and
plus one additional lower-endpoint deficit precisely in the rising region.  The
set-level theorem `aoyagiLemma5Eq5_offsets_endpointDeficit_split` packages the
two finite-set equalities already proved.  This is an obligation split for
endpoint realisation, not source coverage.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-deficit-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-deficit.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-deficit-a5.md`.

The Eq5 endpoint-deficit split now has a supplied endpoint coverage wrapper.
`aoyagiLemma5_suppliedUpperLower_Eq5_offsets_eq_intervalValueSetNat_of_le_min`
is the generic rising-region theorem: if upper and lower endpoint values are
supplied, then those values plus the strict Eq5 offsets fill the
same-coordinate interval.  `aoyagiLemma5_suppliedEndpointCoverage_Eq5_offsets_split`
packages every positive coordinate as either the non-rising upper-only case or
the rising upper-plus-lower case.  Endpoint realisation remains supplied; this
does not construct Eq3/Eq4/Eq5 source labels or terminal/chart data.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-supplied-endpoint-coverage-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-supplied-endpoint-coverage.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-supplied-endpoint-coverage-a5.md`.

The ordinary Eq3 tail region now supplies one more upper-endpoint
instantiation for Eq5 coverage.  `aoyagiLemma5Eq3_piecewise_tail_upperEndpoint_of_boundary_lt`
reads the supplied Eq3 tail clause at the selected-block left endpoint when
`ell-a+1 < p` and `p < ell`, proving the selected-block component value is
`Htilde'_p`.
`aoyagiLemma5_suppliedEq3TailUpper_Eq5_offsets_eq_intervalValueSetNat_of_boundary_lt`
then combines that upper endpoint with the Eq5 non-rising erase-upper theorem
to fill the same-coordinate interval.  This explicitly excludes the Eq3
special boundary and terminal endpoint and does not prove Eq3 label legality,
introduced-label status, all-coordinate source coverage, or the Lemma 5 order
count.  The source scout separately warned not to read this component-value
fact as an own-source-label or all-endpoint-realisation theorem.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-tail-upper-eq5-coverage-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-tail-upper-eq5-coverage.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq3-tail-upper-eq5-coverage-a5.md`.

The Eq3 upper component inventory is now packaged away from the special
boundary.  `aoyagiLemma5Eq3_piecewise_component_upperEndpoint_of_ne_boundary`
splits on `p<=ell-a`: the ordinary upper clause supplies `Htilde'_p` on the
left side, and the ordinary-tail clause supplies `Htilde'_p` when
`ell-a+1<p<ell`.  The excluded coordinate `p=ell-a+1` is Eq3's special
boundary, where the printed value is `Htilde'_(ell-a+1)+1`; `p=ell` is
terminal and outside the half-open block theorem.  The non-rising wrapper
`aoyagiLemma5_suppliedEq3UpperComponent_Eq5_offsets_eq_intervalValueSetNat_of_nonrising_ne_boundary`
uses this component value as the supplied upper endpoint and Eq5's
erase-upper theorem to fill the same-coordinate interval.  This is still not
source-label legality, own-source-label status, all-coordinate endpoint
realisation, injection, back-to-label coverage, or the Lemma 5 order count.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-upper-away-from-boundary-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-upper-away-from-boundary.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq3-upper-away-from-boundary-a5.md`.

The Eq3 special boundary obstruction is now packaged against Eq5 endpoint
coverage.  `aoyagiLemma5Eq3_boundaryValue_ne_upperEndpoint` records that the
supplied Eq3 boundary value is `Htilde'_(ell-a+1)+1`, not the upper endpoint.
`aoyagiLemma5Eq3_boundaryValue_not_mem_Eq5_offsets` then uses the existing
Eq5 offset-set containment in the same-coordinate interval, and
`aoyagiLemma5Eq3_boundaryValue_insert_Eq5_offsets_ne_intervalValueSetNat`
shows that inserting this boundary value into the Eq5 offsets cannot fill the
interval.  The `..._of_eq_boundary` wrapper restates this for an external
coordinate `p` satisfying `p=ell-a+1`.  This is an obstruction record only:
there is still no endpoint coverage at the special boundary, source-label
legality, own-source-label status, all-coordinate endpoint realisation,
injection, back-to-label coverage, or Lemma 5 order count.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-boundary-eq5-obstruction-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-boundary-eq5-obstruction.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq3-boundary-eq5-obstruction-a5.md`.

The Eq4 rising-boundary gap is now recorded.  `AoyagiLemma5Eq4PiecewiseSourceVector`
has the repaired selected-index guard `p+1<=a`; hence
`aoyagiLemma5Eq4_no_piecewiseSourceVector_of_eq_a` proves that no such Eq4
certificate exists at `p=a`.  The combined theorem
`aoyagiLemma5Eq5_risingBoundary_eq_a_noEq4LowerEndpoint` records that under
`a<=ell`, `1<=a`, and `a<=ell-a`, Eq5 is still in the rising erased-endpoints
case at this same coordinate, while Eq4 cannot supply a lower endpoint through
the current source-shaped certificate.  This is distinct from the existing
`p+1=a` terminal Eq4 obstruction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-rising-boundary-gap-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-rising-boundary-gap.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq4-rising-boundary-gap-a5.md`.

The terminal Eq5 gap is now recorded as finite-set bookkeeping.  Eq5 has no
strict offsets at `p=ell`, because the interval excess contains the factor
`ell-ell=0`.  Under the selected-width sum, both terminal Htilde endpoints are
zero, so the terminal same-coordinate interval is `{0}`.  Lean now proves that
Eq5 offsets alone do not fill this interval, and that a separately supplied
terminal zero fills it:
`aoyagiLemma5Eq5OffsetValueSet_eq_empty_of_terminal`,
`aoyagiHtildeIntervalValueSetNat_terminal_eq_singleton_zero_of_selectedSum`,
`aoyagiLemma5Eq5_terminal_offsets_ne_intervalValueSetNat_of_selectedSum`, and
`aoyagiLemma5_suppliedTerminalZero_Eq5_offsets_eq_intervalValueSetNat`.  The
same supplied coverage is also packaged as
`aoyagiLemma5_suppliedTerminalUpper_Eq5_offsets_eq_intervalValueSetNat`, where
the terminal equality is stated in upper-chain form `T(...)=Htilde'_ell`.
This does not construct the terminal source branch or prove terminal-label
exactness.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-eq5-gap-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-eq5-gap.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-eq5-gap-a5.md`.

The supplied family terminal chain-zero wrapper is now Lean-proved.  In
`lean/DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean`, admissible supplied
branches get terminal chain value zero from the existing `Htilde` chain-bound
squeeze under the selected-width sum:
`AoyagiLemma5SuppliedAdmissibleNonbaseFamily.branch_terminalH_zero`,
`AoyagiLemma5SuppliedAdmissibleFamily.base_terminalH_zero`, and
`AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalH_zero`.  Binary
supplied families expose the same endpoint directly from the explicit
`Hlast`/`baseHlast` fields:
`AoyagiLemma5SuppliedBinaryNonbaseFamily.branch_terminalH_zero`,
`AoyagiLemma5SuppliedBinaryFamily.base_terminalH_zero`, and
`AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalH_zero`.  This is only
chain endpoint bookkeeping.  It deliberately does not feed the base branch
into the terminal Eq5 source-coordinate wrapper; doing that still requires an
explicit source-realisation hypothesis equating `T(C.point ell-1)` with the
terminal chain coordinate.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-supplied-family-terminal-chain-zero-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-supplied-family-terminal-chain-zero.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-supplied-family-terminal-chain-zero-a5.md`.

The Eq4 local lower-endpoint wrapper is now Lean-proved in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The new theorem
`aoyagiLemma5Eq4_piecewise_ownCoordinate_lowerEndpoint_of_le_min` extracts the
lower own-coordinate value `T4(C.point p-1)=Htilde_p` from a supplied Eq4
piecewise certificate using only `1<=p` and `p<=ell-a`; the Eq4 certificate
already carries `p+1<=a` and `a<=ell`.  The finite-set wrappers
`aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_eq_interval_erase_upper_of_piecewise`,
`aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_card_eq_offsetCard_add_one_of_piecewise`,
`aoyagiLemma5_suppliedUpper_Eq4_insertOwnCoordinate_eq_intervalValueSetNat_of_piecewise`,
and
`aoyagiLemma5_Eq3Upper_Eq4_local_insertComponents_eq_intervalValueSetNat`
reuse that local endpoint without the global source-selected label-legality
hypotheses.  This is still finite-set bookkeeping: it does not prove source
label legality, Eq4 existence at `p=a`, terminal-collision compatibility in
the `p+1=a` boundary case, or any all-branch order count.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-local-lower-endpoint-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-local-lower-endpoint.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq4-local-lower-endpoint-a5.md`.

The terminal source-realisation bridge is now Lean-proved in
`lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalSourceBridge.lean`.  The bridge imports
the displayed-vector terminal Eq5 wrapper and the supplied-family terminal
chain-zero wrappers, and proves
`AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalSource_Eq5Coverage`
and
`AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalSource_Eq5Coverage`.
Both theorems require the explicit source-coordinate hypothesis
`T(C.point ell-1)=fullH x (Fin.last ell)`; only then does branch terminal
chain-zero produce the terminal zero needed by
`aoyagiLemma5_suppliedTerminalZero_Eq5_offsets_eq_intervalValueSetNat`.  This
does not construct a terminal source branch or prove terminal-label exactness.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-source-bridge-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-source-bridge.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-source-bridge-a5.md`.

The next classifier-boundary slice has now landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean` and
`lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`.  The single-branch
maps-to theorem
`aoyagiLemma5CountDatumSet_mem_of_terminalH_binaryIncrementPrefixDelta` turns
terminal binary prefix-delta chain data at an interior coordinate into a
nonbase counted datum, assuming the value is not the supplied base value.  The
terminal-minimum wrapper
`AoyagiLemma5SuppliedTerminalCandidateFamily.TerminalMinimumCountDatumClassifier`
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_countDatumClassifier`
separate the source-facing upper classifier from branch-label exactness: a
supplied injective classifier from `terminalMinimumLabels` into the counted
datum set gives the upper count.  These results still do not construct the
classifier from Aoyagi's equations, prove source-label legality, prove
injection/back-to-label coverage from the source, identify terminal labels with
branch labels, count pole order, prove normal crossings, or extract RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-binary-counted-datum-maps-to-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-binary-counted-datum-maps-to.md`,
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-minimum-counted-datum-classifier-a5.md`,
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-minimum-counted-datum-classifier.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-classifier-boundary-a5.md`.

The upper-bound classifier interface has also been hardened in
`lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`: Lean now proves
`AoyagiLemma5SuppliedTerminalCandidateFamily.upperBoundClassifier_of_terminalMinimumLabels_subset_branchLabelImage`
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.upperBoundClassifier_iff_terminalMinimumLabels_subset_branchLabelImage`.
This records that the supplied `UpperBoundClassifier` is exactly the no-extra
inclusion from terminal minimum labels into the supplied branch-label image.
It does not prove that inclusion from Aoyagi's source.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-upper-bound-classifier-interface-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-upper-bound-classifier-interface.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-upper-bound-classifier-equivalence-a5.md`.

The counted-datum back-to-branch-label boundary is now packaged in
`lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`.  New Lean names:
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchCountDatumOfCoord`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.TerminalMinimumCountDatumBackToBranchLabel`,
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.upperBoundClassifier_of_countDatumBackToBranchLabel`.
The supplied bridge matches each terminal-minimum label's classified counted
datum to a supplied branch with the same branch label, and the theorem derives
the existing `UpperBoundClassifier`.  The counted-datum equality is retained
as route data; the finite consequence uses only the branch-label witness.
This does not construct the counted-datum classifier, branch-coordinate map,
back-to-label bridge, source-label legality, injection, pole order, normal
crossings, or RLCT extraction from the source.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-back-to-branch-label-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-counted-datum-back-to-branch-label.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-counted-datum-back-to-branch-label-a5.md`.

The terminal source-label bookkeeping slice is now Lean-proved in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  New Lean names:
`aoyagiLemma5_terminalSourceIndex_pos`,
`aoyagiLemma5_terminal_actualWidthLabel_of_lastPoint`, and
`aoyagiLemma5_terminal_intervalValue_mem_introducedLabelFinset_of_terminalZero`.
Under explicit terminal range and width-positivity hypotheses, the terminal
coordinate `C.point ell-1` carries the legal label `k=1`; if the source value
there is supplied to be zero, Lean places it in the terminal Htilde interval
and in the introduced-label finset at state `(C.point ell-1,1)`.  This still
does not construct the terminal source branch or the source-realisation
equality from a branch chain.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-source-label-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-source-label.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-source-label-a5.md`.

The Eq5 post-`p` lower-bound obstruction has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean` as
`aoyagiLemma5Eq5_postP_belowLower_of_intervalExcess_lt_offset`.  For a supplied
equation `(5)` piecewise certificate, the post-`p` branch value is below the
lower Htilde chain whenever the printed subtraction `alpha+b-p` is larger than
`aoyagiLemma5IntervalExcess ell a b`.  This generalizes the all-widths-four
counterexample into a reusable obstruction criterion.  It is not a corrected
Eq5 construction, a global failure theorem, source-label legality, terminality,
chart coverage, classifier coverage, pole order, normal crossings, or RLCT
extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-postp-lower-obstruction-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-postp-lower-obstruction.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-postp-lower-obstruction-a5.md`.

The Eq4 rising-guard exhaustion slice has landed.  In
`lean/DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean`, Lean now proves
`aoyagiLemma5Eq4_risingGuardFailure_iff_eq_a` and
`aoyagiLemma5Eq4_selectedIndexGuardFailure_iff_eq_a`: under `p<=a`, failure
of the repaired guard `p+1<=a`, equivalently the raw selected-index guard
`p+(ell-a)+2<=ell+1` under `a<=ell`, is exactly `p=a`.  The displayed-vector
wrapper
`aoyagiLemma5Eq4_risingGuardFailure_eq_a_and_no_piecewiseSourceVector` adds
the existing supplied-certificate obstruction.  This is only guard arithmetic
and does not prove the converse nonexistence statement, Eq4 branch
construction, Eq4 lower-endpoint coverage at `p=a`, pole order, normal
crossings, or RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-rising-guard-exhaustion-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-rising-guard-exhaustion.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq4-rising-guard-exhaustion-a5.md`.

The counted-datum back-to-branch-label card-bound wrapper has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean` as
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_countDatumBackToBranchLabel`.
It composes the supplied counted-datum back-to-label bridge with the existing
`UpperBoundClassifier` and numeric upper-bound theorem, giving
`C.terminalMinimumLabels.card <= a * (n+1-a) + 1`.  This is only finite
bookkeeping from supplied classifier/back-to-label data; it does not construct
the classifier, branch-coordinate map, or back-to-label bridge from source and
does not prove exact cardinality, pole order, normal crossings, or RLCT
extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-back-to-branch-label-card-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-counted-datum-back-to-branch-label-card.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-counted-datum-back-to-branch-label-card-a5.md`.

The terminal source-realisation iff zero slice has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalSourceBridge.lean`.  New Lean names:
`AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalSource_realisation_iff_terminalZero`
and
`AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalSource_realisation_iff_terminalZero`.
For a supplied full-family branch, branch-chain terminal zero rewrites the
terminal source-realisation equality `T(C.point ell-1)=fullH x (Fin.last ell)`
as the simpler supplied terminal source-zero equality `T(C.point ell-1)=0`.
This is only a reduction of supplied hypotheses; it does not prove terminal
source zero or construct a terminal source branch.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-source-realisation-iff-zero-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-source-realisation-iff-zero.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-source-realisation-iff-zero-a5.md`.

The counted-datum back-to-branch-label exactness slice has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`.  New Lean names:
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_countDatumBackToBranchLabel`
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_countDatumBackToBranchLabel`.
The first packages a supplied counted-datum back-to-label bridge with supplied
branch-label injectivity to produce `TerminalMinimumLabelExactness`; the second
adds the selected-width sum and obtains exact cardinality
`C.terminalMinimumLabels.card = a * (n+1-a) + 1`.  This remains supplied
finite exactness, not a source construction of the classifier, back-to-label
bridge, or branch-label injectivity, and not pole order/RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-back-to-branch-label-exactness-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-counted-datum-back-to-branch-label-exactness.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-counted-datum-back-to-branch-label-exactness-a5.md`.

The terminal source endpoint payload slice has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalSourceBridge.lean`.  New Lean names:
`aoyagiLemma5TerminalSourceEndpointPayload`,
`AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalSource_terminalEndpointPayload`,
and
`AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalSource_terminalEndpointPayload`.
For a supplied full-family branch, an explicit source-realisation equality
`T(C.point ell-1)=F.fullH x (Fin.last ell)` now yields both terminal Eq5
finite-set coverage and terminal source-label bookkeeping for
`(C.point ell-1,1)`, under explicit terminal source range and width-positivity
hypotheses.  This is not terminal branch construction, not source-realisation
production, not terminal exactness, not classifier/injection/back-to-label
coverage, and not pole order/RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-source-endpoint-payload-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-source-endpoint-payload.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-source-endpoint-payload-a5.md`.

The latest A5 scout pass recommends the next source-facing endpoint target:
formalise the Eq4 rising non-strict split.  Under rising hypotheses, failure
of the strict endpoint case `p+1<a` should split into `p+1=a` and `p=a`, with
the `p+1=a` terminal-collision case kept separate from the existing `p=a`
no-repaired-Eq4-guard gap.  Do not fold this into classifier, injection, or
source-backed Lemma 5 exactness.

That Eq4 rising non-strict endpoint split has now landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean` and
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  New Lean names:
`aoyagiLemma5Eq4_risingNonStrictEndpoint_iff_predBoundary_or_eq_a`,
`aoyagiLemma5Eq4_boundaryIndex_not_lt_ell_iff_predBoundary_or_eq_a`,
`aoyagiLemma5Eq4_risingNonStrictEndpoint_predBoundary_or_no_piecewiseSourceVector`,
`aoyagiLemma5Eq4TerminalCollisionPayload`,
`aoyagiLemma5Eq4GuardFailurePayload`, and
`aoyagiLemma5Eq4_risingNonStrictEndpoint_split`.  This is a dispatcher over
existing boundary facts: terminal collision remains conditional on supplied
Eq4 data, while `p=a` records no repaired Eq4 piecewise shape and the Eq5
erased-endpoints deficit.  It is not source coverage, terminal zero,
classifier/injection/back-to-label coverage, pole order, or RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-rising-nonstrict-endpoint-split-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-rising-nonstrict-endpoint-split.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq4-rising-nonstrict-endpoint-split-a5.md`.

The Eq5 alpha-family value-image API wrapper has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  New Lean name:
`aoyagiLemma5Eq5_alphaFamily_value_image_eq_offsetValueSet`.  It proves by
definition that the image of the strict offset domain
`1<=alpha<=min(excess(ell,a,p),p-1)` under
`alpha |-> Htilde'_p-alpha` is exactly
`aoyagiLemma5Eq5OffsetValueSet ell a p M m`.  This is finite-set API naming
only, not displayed-vector construction, source-label legality, selected-span
coverage, terminal `tilde t=0`, chart sequence, Lemma 5 order count, pole
order, normal crossings, or RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-family-value-image-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-alpha-family-value-image.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-alpha-family-value-image-a5.md`.

The Eq5 alpha-family source-label adapter has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean` and
`lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  New Lean names:
`aoyagiLemma5Eq5_alphaFamily_mem_iff_guards` and
`aoyagiLemma5Eq5_alphaFamily_actualWidthLabel_at_of_widthBound`.  Membership
in the strict alpha domain now rewrites to `1<=alpha`,
`alpha<=excess(ell,a,p)`, and `alpha<p`; the source-label wrapper uses the
first two guards to feed the existing Eq5 actual-label theorem under explicit
source-index bounds, actual-width dominance, selected-width hypotheses, and
the supplied label relation.  This is not Eq5 vector construction, branch
existence, cutoff coverage, selected-span coverage, terminal `tilde t=0`,
chart sequence, classifier/injection/back-to-label coverage, order count, pole
order, normal crossings, or RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-family-source-label-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-alpha-family-source-label.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-alpha-family-source-label-a5.md`.

The Eq5 alpha-indexed branch value-image bridge has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  New Lean names:
`aoyagiLemma5Eq5AlphaDomain` and
`aoyagiLemma5Eq5_alphaIndexedBranch_value_image_eq_offsetValueSet`.  If a
supplied finite branch family has alpha image exactly the strict Eq5 alpha
domain and branchwise values `Htilde'_p-alphaOf b`, Lean proves its value
image is `aoyagiLemma5Eq5OffsetValueSet ell a p M m`.  This is only image
bookkeeping from supplied branch data; it is not branch construction,
source-label legality, selected-span/cutoff coverage, injection,
classifier/back-to-label coverage, order count, pole order, normal crossings,
or RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-indexed-branch-value-image-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-alpha-indexed-branch-value-image.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-alpha-indexed-branch-value-image-a5.md`.

The Eq5 post-`p` lower exact-guard slice has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  New Lean names:
`aoyagiLemma5Eq5PostPLowerGuard`,
`aoyagiLemma5Eq5PostPLowerGuard_of_terminalRoom`,
`aoyagiLemma5Eq5_postP_mem_intervalValueSetNat_iff_offset_le_intervalExcess`,
`aoyagiLemma5Eq5_postP_mem_intervalValueSetNat_of_offset_le_intervalExcess`,
`aoyagiLemma5Eq5_postP_mem_intervalValueSetNat_of_postPLowerGuard`,
`aoyagiLemma5Eq5_alphaDomain_and_postPRange_not_lowerGuard`, and
`aoyagiLemma5Eq5_not_postPLowerGuard_counterexample`.  For a supplied Eq5
post-`p` branch point, Lean proves Htilde interval membership is exactly the
local guard `alpha+b-p <= intervalExcess(ell,a,b)`.  It also proves a
sufficient terminal-room condition and records that the strict alpha domain
plus post-`p` range does not imply the guard.  This is not Eq5 construction,
source-label legality, source-backed guard production, cutoff coverage,
classifier exactness, order count, pole order, normal crossings, or RLCT
extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-postp-lower-exact-guard-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-postp-lower-exact-guard.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-postp-lower-exact-guard-a5.md`.

The Eq5 early/tail interval-guard slice has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  New Lean names:
`aoyagiLemma5Eq5PreAlphaLowerGuard`,
`aoyagiLemma5Eq5AlphaToPLowerGuard`,
`aoyagiLemma5Eq5_preAlpha_mem_intervalValueSetNat_iff_index_le_intervalExcess`,
`aoyagiLemma5Eq5_alphaToP_mem_intervalValueSetNat_iff_predAlpha_le_intervalExcess`,
`aoyagiLemma5Eq5_preAlpha_mem_intervalValueSetNat_of_preAlphaLowerGuard`,
`aoyagiLemma5Eq5_alphaToP_mem_intervalValueSetNat_of_alphaToPLowerGuard`,
`aoyagiLemma5Eq5_tail_mem_intervalValueSetNat`,
`aoyagiLemma5Eq5PreAlphaLowerGuard_of_alphaDomain`, and
`aoyagiLemma5Eq5AlphaToPLowerGuard_of_alphaDomain`.  This proves exact local
Htilde interval guards for the `preAlpha` and `alphaToP` branches and
automatic lower-endpoint membership for the `tail` branch.  Strict alpha-domain
membership supplies the early-branch guards, but not the post-`p` guard.  This
is not Eq5 construction, source-label legality, selected-span exactness,
order count, pole order, normal crossings, or RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-early-tail-interval-guards-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-early-tail-interval-guards.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-early-tail-interval-guards-a5.md`.

The counted-datum back-to-label boundary now has a direct bijection wrapper in
`lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`.  New Lean name:
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_bijOn_terminalMinimumLabels_of_countDatumBackToBranchLabel`.
From a supplied counted-datum classifier, supplied back-to-label bridge, and
supplied branch-label injectivity, Lean derives
`Set.BijOn C.branchLabel C.fullBranches C.terminalMinimumLabels`.  This is a
finite API wrapper over supplied data, not source-backed construction of the
classifier, back-to-label map, or injectivity.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-back-to-label-bijon-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-back-to-label-bijon.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-back-to-label-bijon-a5.md`.

The terminal-minimum exactness boundary now has an explicit bijection
equivalence in `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`.  New Lean
name:
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_iff_branchLabel_bijOn`.
It packages the existing two directions between supplied
`TerminalMinimumLabelExactness` and
`Set.BijOn C.branchLabel C.fullBranches C.terminalMinimumLabels`.  The
selected-width sum and `a<=n+1` remain explicit because the exactness-to-bijon
direction uses them to show supplied branches attain the terminal minimum.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-exactness-bijon-equivalence-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-exactness-bijon-equivalence.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-exactness-bijon-equivalence-a5.md`.

The Case 2 terminal-prefix product now has an explicit transported-row form in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  New Lean name:
`case2DisplayedSourceTerminalProductPrefixCandidate_eq_weight_mul_transportedRowsPrefix_mul`.
It rewrites the stopped terminal-prefix product candidate as terminal-prefix
weight times the explicit transported terminal rows, followed by the supplied
suffix.  The pivot row remains the transported top row of `Q^-1 C`; no
original-row identification is made without actual-width exhaustion.  Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-terminal-prefix-transported-product-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-terminal-prefix-transported-product.md`.
Review:
`threads/04-blow-up-certificate/review-case2-terminal-prefix-transported-product-a4.md`.

The Eq5 nonfirst block admissibility wrapper has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  New Lean name:
`aoyagiLemma5Eq5_nonfirstBlock_mem_intervalValueSetNat_of_alphaDomain_of_postPLowerGuard`.
For a supplied Eq5 piecewise certificate, strict alpha-domain membership and
an explicit post-`p` lower guard imply Htilde interval membership on every
selected block `b` with `1<=b`.  The first branch `b=0` is deliberately
excluded, and the post-`p` lower guard remains supplied.  This is not Eq5
construction, source-label legality, source-backed guard production,
selected-span exactness, order count, pole order, normal crossings, or RLCT
extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-nonfirst-block-admissibility-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-nonfirst-block-admissibility.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-nonfirst-block-admissibility-a5.md`.

The Eq5 post-`p` lower guard now has an exact terminal-room characterization
under the strict Eq5 alpha domain.  New Lean names:
`aoyagiLemma5Eq5PostPLowerGuard_iff_terminalRoom_of_alphaDomain` and
`aoyagiLemma5Eq5_nonfirstBlock_mem_intervalValueSetNat_of_alphaDomain_of_terminalRoom`.
The first theorem proves that the global post-`p` lower guard is equivalent to
the concrete inequality `p+2*a-alpha<=ell`; the second replaces the opaque
post-`p` guard in the nonfirst-block admissibility wrapper by that concrete
inequality.  This is finite arithmetic for supplied Eq5 piecewise data.  It
does not construct Eq5 vectors, prove terminal-room from source hypotheses,
prove source-label legality, selected-span exactness, order count, pole order,
normal crossings, or RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-terminal-room-guard-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-terminal-room-guard.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-terminal-room-guard-a5.md`.

## Latest A4 Update

The displayed Case 2 finite frontier branch slice has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  New Lean names:
`Case2DisplayedStepBranch`,
`case2DisplayedFrontier_next_or_actualWidth_or_rowExhausted_of_cont`,
`case2DisplayedStepBranch_of_cont`, and
`Case2DisplayedSuppliedChartFamilyBoundary.frontierBranch`.  Under displayed
pivot validity `J+1 <= prefixMinNat n (S+1)`, Lean records the overlapping
frontier alternatives: next same-stage continuation, actual next-width
exhaustion, or current-prefix row exhaustion.  This gives later branch
dispatch a precise finite witness without pretending to prove an atlas,
source-produced post-data, transition invariance, terminal source truth,
normal crossings, pole order, or RLCT.

Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-displayed-frontier-branch-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-frontier-branch.md`.
Review:
`threads/04-blow-up-certificate/review-case2-displayed-frontier-branch-a4.md`.

The source-chart frontier package slice has also landed in
`BlowupArithmetic.lean`.  New Lean names:
`Case2DisplayedSuppliedChartFamilyBoundary.ContinuingSourceChartFrontierPayload`,
`Case2DisplayedSuppliedChartFamilyBoundary.ActualWidthSourceChartFrontierPayload`,
`Case2DisplayedSuppliedChartFamilyBoundary.RowExhaustedTerminalLastSourceChartFrontierPayload`,
`Case2DisplayedSuppliedChartFamilyBoundary.SourceChartFrontierBoundaryPackages`,
and
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_frontierBoundaryPackages`.
The package is a fielded implication interface: continuing, actual-width, and
row-exhausted consequences are exposed only under their own explicit branch
hypotheses.  It is not a chosen-branch transition theorem, and it keeps the
actual-width original-row/relabel conclusion separate from the row-exhausted
transported-prefix terminal-last conclusion.

Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-source-chart-frontier-packages-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-source-chart-frontier-packages.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-chart-frontier-packages-a4.md`.

The row-exhausted source-chart frontier now also has a source-suffix
transported-prefix payload.  New Lean names:
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChart_rowExhausted_sourceSuffixTransportedPrefixBoundary_withFiniteCenterIdeal`,
`Case2DisplayedSuppliedChartFamilyBoundary.RowExhaustedSourceSuffixTransportedPrefixPayload`,
and `SourceChartFrontierBoundaryPackages.rowExhaustedSourceSuffix`.  This
packages the existing row-exhausted source-suffix entry-ideal equality with
finite residual-center principalization, keeping `sourceSuffixProduct`
explicit.  It does not require terminal-last, does not replace transported rows
by original rows, and does not assert `(S+1,0)` relabelled level/exponent data.
It remains supplied-boundary assembly: no chart construction, source-produced
post-data, transition invariant, Jacobian, normal crossings, pole order, or
RLCT follows.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-row-exhausted-source-suffix-payload-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-row-exhausted-source-suffix-payload.md`.
Review:
`threads/04-blow-up-certificate/review-case2-row-exhausted-source-suffix-payload-a4.md`.

The continuing source-chart frontier now also has a weighted source-following
payload.  New Lean names:
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_continuingWeightedSourceFollowingPayload_withFiniteCenterIdeal`,
`Case2DisplayedSuppliedChartFamilyBoundary.ContinuingWeightedSourceFollowingFrontierPayload`,
and `SourceChartFrontierBoundaryPackages.continuingWeighted`.  This packages
the existing paper-`C'` weighted lower-row handoff with next residual-center
nonemptiness and finite residual-center principalization under
`J+2 <= prefixMinNat n (S+1)`.  The equality is still lower-row only, with the
successor lower-row diagonal explicit; it is not full chart production,
source-produced `C'^(S+1)`, source-produced post-data, transition invariance,
normal crossings, pole order, or RLCT.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-continuing-weighted-source-following-payload-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-continuing-weighted-source-following-payload.md`.
Review:
`threads/04-blow-up-certificate/review-case2-continuing-weighted-source-following-payload-a4.md`.

The post-pivot lower-right block now also has a source-coordinate residual
representative.  New Lean names:
`case2DisplayedPostPivotSourceResidual`,
`case2SourceResidualBlock_postPivotSourceResidual`, and
`case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_sourceResidualBlock_sourceFollowingFactor`.
The representative is a zero-extension of the already-defined displayed
post-pivot residual block to a total source-pair function.  Restricting it
back to the next same-stage residual domain `(S,J+1)` recovers the displayed
post-pivot block, and the paper-`C'` lower-row product rewrites in
source-residual/source-following notation.  This is not chart production,
source-produced post-data, successor chart-family construction, transition
invariance, normal crossings, pole order, or RLCT.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-post-pivot-source-residual-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-post-pivot-source-residual.md`.
Review:
`threads/04-blow-up-certificate/review-case2-post-pivot-source-residual-a4.md`.

Latest A5 counted-datum maps-to adapter update:
`Lemma5SuppliedFamily.lean` now exposes
`aoyagiLemma5CountDatumSet_mem_of_intervalValueSetNat` and
`aoyagiLemma5CountDatumSet_mem_of_HtildeBounds`.  At an interior coordinate,
same-coordinate interval membership plus a supplied non-base-value inequality
puts `some (j,H)` in the counted-datum set; explicit Htilde bounds imply the
same conclusion after unwrapping the interval-membership theorem.  This is
finite codomain bookkeeping only, not branch construction, classifier
construction, injection, back-to-label coverage, terminal-minimum exactness,
order count, pole order, normal crossings, or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-maps-to-adapters-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-counted-datum-maps-to-adapters.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-counted-datum-maps-to-adapters-a5.md`.

Latest A5 Eq5 counted-datum bridge update:
`Lemma5Eq5CountDatumBridge.lean` now contains
`aoyagiLemma5Eq5_nonfirstBlock_countDatumSet_mem_of_alphaDomain_of_postPLowerGuard`
and
`aoyagiLemma5Eq5_nonfirstBlock_countDatumSet_mem_of_alphaDomain_of_terminalRoom`.
For a supplied Eq5 piecewise vector, strict alpha-domain membership, nonfirst
block data, and a supplied non-base-value inequality, the branch value `T S`
belongs to the counted-datum codomain.  The two variants use either the
explicit post-`p` guard or the terminal-room inequality.  This is maps-to
bookkeeping only, not Eq5 vector construction, nonbase production, classifier
construction, injection, back-to-label coverage, order count, pole order,
normal crossings, or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-counted-datum-bridge-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-counted-datum-bridge.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-counted-datum-bridge-a5.md`.

Latest A5 Eq5 endpoint counted-datum bridge update:
`Lemma5Eq5CountDatumBridge.lean` now contains
`aoyagiLemma5Eq5_endpointChain_countDatumSet_mem_of_terminalRoom` and
`aoyagiLemma5Eq5_endpointValue_countDatumSet_mem_of_terminalRoom`.  For a
supplied Eq5 terminal-room endpoint chain, an interior selected coordinate,
and a supplied nonbase inequality, the chain value `H_j` and the source-facing
endpoint value `T(C.point j - 1)` belong to the counted-datum codomain.  This
uses the Eq5 binary-prefix-delta theorem and the existing terminal-binary
counted-datum maps-to theorem.  It does not construct Eq5 vectors, endpoint
realisation, nonbase status, classifiers, injection, back-to-label coverage,
order count, pole order, normal crossings, or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-counted-datum-bridge-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-counted-datum-bridge.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-counted-datum-bridge-a5.md`.

Latest A5 Lemma 4 prefix-profile computation update:
`HtildeChainArithmetic.lean` now contains
`aoyagiLemma4IncrementPrefix_eq_upperHighCount_add_of_eq_upperNat_sub` and
`aoyagiLemma4IncrementPrefix_eq_lowerHighCount_of_eq_lowerNat`.  These unfold
the Lemma 4 prefix normal form at a single coordinate: an upper Htilde value
minus offset `r` has prefix value `upperHighCount+r`, and a lower Htilde value
has prefix value `lowerHighCount`.  This is generic algebra for a later Eq5
endpoint-profile proof, not binary deltas, two-value increments, Eq5 vector
construction, endpoint realisation, order count, pole order, normal crossings,
or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma4-prefix-profile-computations-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma4-prefix-profile-computations.md`.
Review:
`threads/05-arithmetic-tail/review-lemma4-prefix-profile-computations-a5.md`.

Latest A5 Eq5 endpoint-prefix profile update:
`Lemma5Eq5EndpointProfile.lean` now contains the branchwise endpoint-prefix
profile theorems
`aoyagiLemma5Eq5_endpointChain_incrementPrefix_preAlpha`,
`aoyagiLemma5Eq5_endpointChain_incrementPrefix_alphaToP`,
`aoyagiLemma5Eq5_endpointChain_incrementPrefix_postP`, and
`aoyagiLemma5Eq5_endpointChain_incrementPrefix_tail`.  For a supplied Eq5
piecewise vector and supplied endpoint-chain correspondence, the endpoint
prefix values are respectively `b`, `alpha-1`, `alpha+b-p`, and `a`; the
alpha-to-`p` and post-`p` profiles also assume terminal-room.  This is
branchwise arithmetic only, not adjacent-branch binary deltas, two-value
increments, Eq5 vector construction, endpoint realisation, order count, pole
order, normal crossings, or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-prefix-profile-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-prefix-profile.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-prefix-profile-a5.md`.

Latest A5 Eq5 binary-prefix-delta update:
`Lemma5Eq5EndpointProfile.lean` now contains
`aoyagiLemma5Eq5_endpointChain_incrementPrefix_profile_of_terminalRoom` and
`aoyagiLemma5Eq5_endpointChain_binaryIncrementPrefixDelta_of_terminalRoom`.
For a supplied Eq5 piecewise vector, supplied endpoint-chain correspondence,
source endpoint, terminal endpoint, selected-width sum, and terminal room, the
successive Lemma 4 increment-prefix deltas are all `0` or `1`.  This is the
adjacent endpoint-profile calculation only.  It does not construct Eq5
vectors, prove endpoint realisation, terminality, classifier data, order
count, pole order, normal crossings, or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-binary-prefix-delta-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-binary-prefix-delta.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-binary-prefix-delta-a5.md`.

Latest A5 Eq5 two-value-wrapper update:
`Lemma5Eq5EndpointProfile.lean` now contains
`aoyagiLemma5Eq5_endpointChain_F_twoValue_of_terminalRoom`,
`aoyagiLemma5Eq5_endpointChain_twoValueCount_of_terminalRoom`,
`aoyagiLemma5Eq5_endpointChain_binaryIncrementPrefix_count_eq_of_terminalRoom`,
and
`aoyagiLemma5Eq5_endpointChain_HtildeChainBounds_of_terminalRoom`.  These are
thin adapters from the supplied Eq5 terminal-room binary-prefix deltas to the
existing Lemma 4 two-value, count, and Htilde-bound APIs.  They do not prove
Eq5 vector construction, endpoint realisation, terminality, counted-datum
membership, classifier data, order count, pole order, normal crossings, or
RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-two-value-wrapper-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-two-value-wrapper.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-two-value-wrapper-a5.md`.

Latest A5 Eq5 own-block counted/introduced payload update:
`Lemma5Eq5CountDatumBridge.lean` now contains
`aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_widthBound`.
For one supplied Eq5 own-block branch, the theorem combines source-label
legality and counted-datum membership: under explicit last-point source range,
selected-width bound, label formula, positive coordinate, own-block membership,
and nonbase inequality, it proves both `some (p,T S)` counted-datum membership
and `T S=k-1` with `Sigma.mk S k` in `introducedLabelFinset L n S k`.  This is
a one-branch payload adapter only, not Eq5 vector construction, nonbase
production, classifier construction, injection, back-to-label coverage,
no-extra terminal-minimum coverage, order count, pole order, normal crossings,
or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-ownblock-counted-introduced-payload-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-ownblock-counted-introduced-payload.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-ownblock-counted-introduced-payload-a5.md`.

Latest A5 Eq5 own-block block-width payload update:
`Lemma5Eq5CountDatumBridge.lean` now also contains
`aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_blockWidth`.
It derives the selected-width bound needed by the existing own-block
counted/introduced payload from `C.block p S` and the block-local actual-width
lower-bound hypothesis.  The nonbase inequality remains explicit.  This is a
one-branch adapter only, not Eq5 vector construction, classifier construction,
back-to-label coverage, Lemma 5 order count, pole order, normal crossings, or
RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-ownblock-block-width-payload-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-ownblock-block-width-payload.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-ownblock-block-width-payload-a5.md`.

Latest A5 Eq5 own-block width-source variants update:
`Lemma5Eq5CountDatumBridge.lean` now also contains
`aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_leftEndpointMin`,
`aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_offSelected`,
and
`aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_offSelected_lt`.
These are source-shaped variants of the own-block payload.  They derive the
selected-width bound from the existing left-endpoint/minimum or off-selected
dominance APIs, then delegate to the raw-width own-block payload.  The
selected-width source hypotheses and the nonbase inequality remain explicit.
This is a one-branch adapter only, not Eq5 vector construction, classifier
construction, back-to-label coverage, Lemma 5 order count, pole order, normal
crossings, or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-ownblock-width-source-variants-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-ownblock-width-source-variants.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-ownblock-width-source-variants-a5.md`.

Latest A5 Eq5 own-block counted-datum classifier update:
`Lemma5Eq5CountDatumBridge.lean` now also contains
`aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_widthBound`,
`aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_blockWidth`,
`aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_leftEndpointMin`,
`aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_offSelected`,
and
`aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_offSelected_lt`.
These package a finite supplied set of Eq5 own-block source labels as an
`AoyagiLemma5CountDatumClassifier`.  The classifier sends
`label = (S,k)` to `some (pOf label, T label S)`, proves the `mapsTo` field
from the existing one-branch payload, and keeps classifier injectivity
supplied.  This is not Eq5 branch construction, nonbase production,
source-derived injectivity, terminal introduced-domain lifting,
back-to-label coverage, Lemma 5 order count, pole order, normal crossings, or
RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-ownblock-countdatum-classifier-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-ownblock-countdatum-classifier.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-ownblock-countdatum-classifier-a5.md`.

Latest A5 Eq5 own-block common introduced-domain update:
`BlowupArithmetic.lean` now contains `introducedLabel_mono_state` and
`introducedLabelFinset_subset_of_state_le`.  These record that introduced
labels are monotone under explicit forward state movement
`S<S' or (S=S' and J<=J')`.  `Lemma5Eq5CountDatumBridge.lean` now contains
the matching Eq5 own-block common-domain wrappers
`aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_widthBound`,
`..._blockWidth`, `..._leftEndpointMin`, `..._offSelected`, and
`..._offSelected_lt`.  They lift the local introduced-label membership
`(S,k) in introducedLabelFinset L n S k` to a supplied later/common domain
`introducedLabelFinset L n Sfinal Jfinal`.  The target-state comparison
remains explicit.  This is not terminal-domain construction, Eq5 branch
construction, source-derived classifier data, Lemma 5 order count, pole
order, normal crossings, or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-ownblock-common-introduced-domain-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-ownblock-common-introduced-domain.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-ownblock-common-introduced-domain-a5.md`.

Latest A5 Eq5 terminal counted-datum classifier update:
new module `Lemma5Eq5TerminalClassifier.lean` builds
`TC.TerminalMinimumCountDatumClassifier` from supplied Eq5 own-block
common-domain payload data for every label in `TC.terminalMinimumLabels`.
The classifier sends `label=(S,k)` to `some (pOf label, T label S)`.
Membership in `TC.terminalMinimumLabels` supplies the common-domain state
comparison; the existing Eq5 common-domain payload proves `mapsTo`; and
injectivity remains supplied.  Source-shaped variants derive the selected
width bound from block-width, left-endpoint/minimum, off-selected, or strict
off-selected dominance hypotheses.  This is not Eq5 branch construction,
source-derived injectivity, a back-to-label map, `UpperBoundClassifier`,
exactness, Lemma 5 order count, pole order, normal crossings, or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-terminal-countdatum-classifier-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-terminal-countdatum-classifier.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-terminal-countdatum-classifier-a5.md`.

Latest A5 Eq5 terminal counted-datum cardinal-squeeze update:
`Lemma5Eq5TerminalClassifier.lean` now also contains upper-bound wrappers
`terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_widthBound`,
`..._blockWidth`, `..._leftEndpointMin`, `..._offSelected`, and
`..._offSelected_lt`.  These compose the supplied Eq5 terminal classifier
with the existing counted-datum cardinal theorem to prove
`TC.terminalMinimumLabels.card <= a*(N+1-a)+1`.  The same file also contains
width-bound exactness wrappers
`terminalMinimumLabels_eq_branchLabelImage_of_eq5OwnBlockCommon_widthBound_cardSqueeze`,
`terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_cardSqueeze`,
`terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_cardSqueeze`,
and
`branchLabel_bijOn_terminalMinimumLabels_of_eq5OwnBlockCommon_widthBound_cardSqueeze`.
These use the existing cardinal squeeze after adding supplied branch-label
injectivity.  Counted-datum injectivity and branch-label injectivity remain
separate supplied hypotheses.  This is not Eq5 branch construction,
source-derived classifier data, a counted-datum-preserving back-to-label map,
the printed Lemma 5 order count, pole order, normal crossings, or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-terminal-countdatum-cardinal-squeeze-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-terminal-countdatum-cardinal-squeeze.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-terminal-countdatum-cardinal-squeeze-a5.md`.

Latest A5 Eq5 branch-label injection update:
`Lemma5TerminalBridge.lean` now contains
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_fullBranches_of_some_injOn`.
It lifts supplied nonbase branch-label injectivity to the full `Option`-tagged
terminal branch set under explicit base/nonbase separation.
`Lemma5Eq5TerminalClassifier.lean` now contains
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_eq5AlphaIndexed_nonbase`.
It derives the nonbase injectivity for Eq5 alpha-indexed branches from
coordinatewise alpha injectivity, supplied selected-block membership of source
coordinates, and the displayed Eq5 label formula; selected-cutpoint block
uniqueness supplies cross-coordinate disjointness.  This is still conditional
branch-label injection only.  It does not construct Eq5 branches, prove
alpha-domain coverage, produce terminal payloads, prove counted-datum
injectivity, build back-to-label coverage, construct an upper-bound
classifier, prove no-extra terminal-minimum coverage, order count, pole order,
normal crossings, or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-branch-label-injection-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-branch-label-injection.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-branch-label-injection-a5.md`.

Latest A5 Eq5 alpha-injection cardinal-squeeze update:
`Lemma5Eq5TerminalClassifier.lean` now also contains
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_alphaIndexedBranch_cardSqueeze`
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_alphaIndexedBranch_cardSqueeze`.
These compose the Eq5 terminal counted-datum cardinal squeeze with the
explicit Eq5 alpha-indexed branch-label injection theorem.  They remove the
opaque `hinjBranchLabel` boundary from the width-bound exactness/count
wrappers, but keep counted-datum injectivity, terminal-label Eq5 payloads,
coordinatewise branch alpha injectivity, branch block membership, branch label
formula, and base/nonbase separation explicit.  This is still conditional
finite exactness only: no branch construction, alpha-domain coverage,
source-produced terminal payloads, counted-datum injectivity, back-to-label
coverage, no-extra classifier, order count, pole order, normal crossings, or
RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-terminal-alpha-injection-cardinal-squeeze-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-terminal-alpha-injection-cardinal-squeeze.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-terminal-alpha-injection-cardinal-squeeze-a5.md`.

Latest A5 Eq5 alpha endpoint value-image split update:
`Lemma5DisplayedVector.lean` now contains
`aoyagiLemma5Eq5_alphaIndexedBranch_suppliedEndpointCoverage_value_image_split`.
For one positive interior coordinate, supplied alpha-indexed Eq5 strict-offset
branches with alpha image equal to the strict Eq5 alpha domain have value image
equal to the Eq5 offset set; inserting supplied endpoint branch records fills
the same-coordinate interval, with only the upper endpoint outside the rising
case and both endpoints in the rising case.  This is a one-coordinate
value-image adapter toward supplied coordinate coverage.  It does not
construct branches, prove endpoint source-label legality, value injectivity,
base-value membership, cross-coordinate disjointness, classifier data,
no-extra terminal-minimum coverage, order count, pole order, normal crossings,
or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-endpoint-value-image-split-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-alpha-endpoint-value-image-split.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-alpha-endpoint-value-image-split-a5.md`.

Latest A5 Eq3/Eq4 local interval cardinality update:
`Lemma5DisplayedVector.lean` now contains
`aoyagiLemma5_Eq3Upper_Eq4_local_insertComponents_card_eq_intervalSize`
and
`aoyagiLemma5_Eq3Upper_Eq4_local_insertComponents_card_eq_offsetCard_add_two`.
These are source-legality-free cardinality forms of the existing local
Eq3/Eq4 rising-interval coverage equality.  They count one local insert set
against the same-coordinate interval size and against strict Eq5 offsets plus
two, under local Eq3/Eq4 piecewise certificates.  This is not displayed-vector
construction, source-label legality, classifier coverage, Lemma 5 order count,
pole order, normal crossings, or RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-eq4-local-interval-cardinality-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-eq4-local-interval-cardinality.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq3-eq4-local-interval-cardinality-a5.md`.

Latest source-audit checkpoint:
xhigh source audit of Aoyagi Lemma 5 pp. 25-27 confirmed the existing
classifier frontier.  The interval cardinality formula and the local Case
1(2) `J` increment are source-backed elementary/local facts, but the printed
paragraph does not supply a classifier, injection, back-to-label map, no-extra
terminal-minimum coverage, nonbase status, endpoint-chain realisation, or
terminal source realisation.

Latest xhigh source-frontier audit correction: after the cheap A5 wrapper
above, pivot back to A4 displayed Case 2 source-chart production, but do not
redo the local `C' = Q^-1*C` algebra.  Existing terminal-frontier artifacts
already cover the paper transported factor (`case2DisplayedPaperCprime`), the
top-row correction, unchanged lower tail, the paper-`C'` weighted lower-row
handoff, and `SuppliedTerminalCprimeBridge`.  A broad new reproduction of that
calculation is unnecessary.  The genuinely missing A4 frontier is chart/source
production of the full successor object or successor following-product data
from the displayed chart across the continuing and terminal branches,
including old top rows, transported pivot row, post-pivot tail, and suffix
handling.  Any thin total-source adapter for paper `C'` should be built only
if it directly serves that source-production theorem.  Durable audit:
`threads/04-blow-up-certificate/source-frontier-audit-case2-paper-cprime-a4.md`.

Latest A4 Case 1(2) J-increment payload update:
`BlowupArithmetic.lean` now contains
`Case1DisplayedRowStripJIncrementPayload`,
`Case1DisplayedRowStripSuppliedTransitionBoundary.jIncrementPayload`,
`Case1DisplayedRowStripSelectedOldPullbackBoundary.jIncrementPayload`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.jIncrementPayload`,
and the matching
`post_weight_eq_new_mul_factoredBase_weight_of_ge` projections.  This proves
the narrow source-backed local bridge under the p. 18 guard: landing at
`(S,J+1)`, adding exactly the fresh introduced label `(S,J+1)`, extending the
post exponent domain, and multiplying post recurrence weights by the fresh
variable relative to the factored-old base state.  This is not a Lemma 5
no-extra counting theorem and does not provide classifier, injection, or
back-to-label data.

Latest A4 Case 2 displayed J-increment payload update:
`BlowupArithmetic.lean` now contains `Case2DisplayedJIncrementPayload`,
`Case2DisplayedSuppliedChartFamilyBoundary.jIncrementPayload`, and
`Case2DisplayedSuppliedChartFamilyBoundary.post_weight_eq_new_mul_pre_weight_of_ge`.
This packages the parallel local bridge under Aoyagi PDF p. 21's displayed
Case 2 continuation guard: landing at `(S,J+1)`, adding exactly the fresh
introduced label `(S,J+1)`, extending the post exponent domain with the
corrected Case 2 certificate, projecting corrected new-label numerator
identities, and multiplying post recurrence weights by the fresh variable
relative to the supplied pre-state.  This uses the corrected Case 2 exponent
package already isolated in Lean and does not repair the printed vector
mismatch as a source theorem.  It is not chart production, a transition
invariant, pole order, normal crossings, or RLCT.

Latest A4 Case 2 continuing weighted following-product update:
`BlowupArithmetic.lean` now contains
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_paperCprimeWeightedLowerRows_mul_followingProduct_withCorrectedPostData`.
This right-multiplies the existing paper-`C'` weighted lower-row handoff by an
arbitrary supplied following product `F`, preserving the same row-operation
witness and corrected post-data projections.  The theorem is lower-row only,
keeps the successor lower-row diagonal explicit, and keeps `F` supplied.  It
does not add next-center nonemptiness, source production of `F`, source
production of the full successor `C'^(S+1)`, successor chart-family
construction, transition invariance, Jacobian arithmetic, normal crossings,
pole order, or RLCT.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-continuing-weighted-following-product-a4.md`,
`threads/04-blow-up-certificate/statement-card-a4-case2-continuing-weighted-following-product.md`,
and
`threads/04-blow-up-certificate/review-case2-continuing-weighted-following-product-a4.md`.

Latest A4 Case 2 source successor following-factor update:
`BlowupArithmetic.lean` now contains
`case2DisplayedSourceSuccessorFollowingFactor` and restriction lemmas
`case2DisplayedSourceSuccessorFollowingFactor_pivotRow`,
`case2DisplayedSourceSuccessorFollowingFactor_of_ne`,
`case2DisplayedSourceSuccessorFollowingFactor_oldRow`,
`case2SourceFollowingFactor_successorFollowingFactor_succ`,
`case2DisplayedSourceSuccessorFollowingFactor_eq_original_of_width_next_eq`,
`case2DisplayedSourceTerminalOriginalRows_successorFollowingFactor`, and
`case2DisplayedSourceTerminalCprimeCandidate_eq_originalRows_successorFollowingFactor`.
The object replaces only source row `J+1` of `C` by the top row of
`Q^-1 C`.  The lemmas prove the pivot/off-pivot restrictions, unchanged
post-pivot same-stage following restriction, actual-width collapse to the
original `C`, and the terminal transported-row presentation.  This is
formula-level source-coordinate data only: no chart production,
source-produced recurrence/exponent post-data, old-top/suffix production,
transition invariant, Jacobian arithmetic, normal crossings, pole order, or
RLCT.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-source-successor-following-factor-a4.md`,
`threads/04-blow-up-certificate/statement-card-a4-case2-source-successor-following-factor.md`,
and
`threads/04-blow-up-certificate/review-case2-source-successor-following-factor-a4.md`.

Latest A4 Case 2 successor following weighted handoff update:
`BlowupArithmetic.lean` now contains
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_paperCprimeWeightedLowerRows_withSuccFollowingFactorAndCorrectedData`
and
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_paperCprimeWeightedLowerRows_mul_F_withSuccFollowingFactorAndCorrectedData`.
These rewrite the existing paper-`C'` weighted lower-row handoff through the
formula-level successor following factor `Csucc`; the supplied-`F` variant
keeps the same arbitrary following product.  The proof is only the already
proved restriction equality
`case2SourceFollowingFactor_successorFollowingFactor_succ`.  This does not
add `hnext`/next-center nonemptiness, source production of `F`, old-top rows,
suffix production, full successor `C'^(S+1)`, chart production, transition
invariance, Jacobian arithmetic, normal crossings, pole order, termination, or
RLCT.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-successor-following-weighted-handoff-a4.md`,
`threads/04-blow-up-certificate/statement-card-a4-case2-successor-following-weighted-handoff.md`,
and
`threads/04-blow-up-certificate/review-case2-successor-following-weighted-handoff-a4.md`.

Latest A4 Case 2 successor following frontier payload update:
`BlowupArithmetic.lean` now contains
`ContinuingWeightedSuccFollowingFrontierPayload` and
`sourceChartMap_continuingWeightedSuccFollowingPayload_withFiniteCenterIdeal`.
This pairs the explicit next-continuation guard `J+2 <= prefixMinNat n (S+1)`
with the successor-following lower-row handoff and the existing finite
principalization facts for the current displayed chart center.  Per xhigh
review, this stayed theorem-only: no new `SourceChartFrontierBoundaryPackages`
field was added.  It is still not source/chart production of `Csucc`, a pivot
row product, old-top/suffix production, full successor `C'^(S+1)`, transition
invariance, Jacobian arithmetic, normal crossings, pole order, termination, or
RLCT.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-successor-following-frontier-payload-a4.md`,
`threads/04-blow-up-certificate/statement-card-a4-case2-successor-following-frontier-payload.md`,
and
`threads/04-blow-up-certificate/review-case2-successor-following-frontier-payload-a4.md`.

Latest A4 Case 2 source-residual/successor-following product update:
`BlowupArithmetic.lean` now contains
`case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_sourceResidualBlock_successorFollowingFactor`.
It rewrites the bare lower rows of `D''' * C'` as the source residual block of
`case2DisplayedPostPivotSourceResidual` times the source following factor of
`case2DisplayedSourceSuccessorFollowingFactor`.  This is exactly the missing
source-pair notation for the bare post-pivot product.  Per xhigh review, the
weighted source-chart handoff variant was not added yet to avoid theorem
proliferation; add it only if needed downstream.  This still does not prove
source/chart production, pivot row, old-top/suffix production, full successor
`C'^(S+1)`, transition invariance, normal crossings, pole order, termination,
or RLCT.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-source-residual-successor-following-product-a4.md`,
`threads/04-blow-up-certificate/statement-card-a4-case2-source-residual-successor-following-product.md`,
and
`threads/04-blow-up-certificate/review-case2-source-residual-successor-following-product-a4.md`.

Latest A4 Case 2 actual-width successor terminal-row update:
`BlowupArithmetic.lean` now contains
`sourceChart_actualWidth_terminalOriginalRowsSuccFollowingSuppliedSuffixBoundary`.
This restates the actual-width supplied-following terminal boundary with
terminal rows written as original rows of the formula-level successor
following factor.  It uses the exact actual next-width hypothesis
`n(S+1)=J+1`, under which `case2DisplayedSourceSuccessorFollowingFactor = C`.
Per xhigh review, only the arbitrary supplied-`F` theorem was added; no
source-suffix, identity-following, finite-center, or frontier-package variants
were introduced.  It is not source/chart production of `Csucc`, `F`, source
suffixes, old-top rows, full successor `C'^(S+1)`, transition invariance,
normal crossings, pole order, termination, or RLCT.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-actual-width-successor-terminal-rows-a4.md`,
`threads/04-blow-up-certificate/statement-card-a4-case2-actual-width-successor-terminal-rows.md`,
and
`threads/04-blow-up-certificate/review-case2-actual-width-successor-terminal-rows-a4.md`.

Latest A4 Case 2 row-exhausted successor-prefix update:
`BlowupArithmetic.lean` now contains
`case2DisplayedSourceTerminalCprimePrefixCandidate_eq_originalRows_successorFollowingFactor`
and
`sourceChart_rowExhausted_sourceSuffixSuccFollowingPrefixBoundary_withFiniteCenterIdeal`.
This rewrites the row-exhausted stopped source-suffix boundary so the terminal
prefix rows are written as original rows of the formula-level successor
following factor `Csucc`.  It uses row exhaustion
`prefixMinNat n S = J+1`; it does not assume actual next-width exhaustion
`n(S+1)=J+1`.  Thus row `J+1` is original only as a row of `Csucc`, where
`Csucc` already contains the transported top row of `Q^-1 C`; it is not
identified with row `J+1` of the original `C`.  Per xhigh review, this stayed
theorem-only: no new frontier-package field was added.  This is not
source/chart production of `Csucc`, source-suffix production, actual-width
original-row collapse, `(S+1,0)` relabelled certificates, full successor
`C'^(S+1)`, transition invariance, normal crossings, pole order, termination,
or RLCT.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-row-exhausted-successor-prefix-a4.md`,
`threads/04-blow-up-certificate/statement-card-a4-case2-row-exhausted-successor-prefix.md`,
and
`threads/04-blow-up-certificate/review-case2-row-exhausted-successor-prefix-a4.md`.

Latest A4 Case 2 continuing old-top/source-suffix stack update:
`BlowupArithmetic.lean` now contains
`sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withCorrectedPostData`.
This lifts the supplied paper `Q/P` identity through unchanged old top rows
and multiplies the full pivot-first stack by the raw source suffix
`sourceSuffixProduct`.  Unlike the lower-row arbitrary-`F` wrapper, it keeps
the old top rows and transported pivot row by preserving Aoyagi's paper
factor `C' = Q^-1 C` in pivot-first order.  It still stays below full
source-ordered successor production: no row equivalence to a source-produced
`C'^(S+1)`, suffix production, chart coverage, transition invariant, normal
crossing, pole order, termination, or RLCT is asserted.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-continuing-oldtop-source-suffix-stack-a4.md`,
`threads/04-blow-up-certificate/statement-card-a4-case2-continuing-oldtop-source-suffix-stack.md`,
and
`threads/04-blow-up-certificate/review-case2-continuing-oldtop-source-suffix-stack-a4.md`.

Latest A5 Eq5 structured injection adapter update:
`Lemma5Eq5CountDatumBridge.lean` now contains
`aoyagiLemma5Eq5_ownBlock_countDatum_injOn_of_pAlpha_injOn`, and
`Lemma5Eq5TerminalClassifier.lean` now contains
`terminalMinimumCountDatum_injOn_of_eq5OwnBlock_pAlpha_injOn`,
`branchLabel_none_ne_some_of_terminalEndpointLabel_and_nonbaseBlock`, and
`branchLabel_injOn_of_eq5AlphaIndexed_nonbase_terminalEndpointBase`.  These
adapters reduce two opaque supplied injectivity/separation hypotheses to
structured supplied data: counted-datum injectivity follows from Eq5 own-block
payloads plus `(p, alpha)` injectivity on terminal labels, and base/nonbase
branch-label separation follows from an explicit terminal-endpoint base label
plus nonbase selected-block membership.  They do not source-prove
`(p, alpha)` injectivity, construct Eq5 branches, produce terminal payloads,
prove no-extra terminal-minimum coverage, prove a Lemma 5 order count,
normal crossings, pole order, or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-structured-injection-adapters-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-structured-injection-adapters.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-structured-injection-adapters-a5.md`.

Latest A5 Eq5 endpoint raw-branches update:
`Lemma5Eq5SuppliedCoverage.lean` now contains
`aoyagiLemma5Eq5EndpointRawBranches`,
`aoyagiLemma5Eq5EndpointRawBranches_value_image_eq_intervalValueSetNat`, and
`AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage`.  The
raw branch set inserts the supplied upper endpoint at every interior
coordinate and the supplied lower endpoint exactly when `j<=a` and
`j<=ell-a`.  The value-image theorem proves the raw coordinate image is the
same-coordinate interval from strict Eq5 alpha-domain coverage plus supplied
endpoint values.  The constructor wrapper feeds this proved image into
`ofCoordinateValueCoverage`, while leaving base-value membership, raw
injectivity, and cross-coordinate disjointness supplied.  It does not prove
source-produced endpoint records, source-label legality, no-extra coverage,
normal crossings, pole order, or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-raw-branches-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-raw-branches.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-raw-branches-a5.md`.

Latest A5 Eq5 endpoint branch-coordinate update:
`Lemma5Eq5SuppliedCoverage.lean` now also contains
`aoyagiLemma5Eq5EndpointRawBranches_branchCoord_eq` and
`AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_branchCoord_eq`.
These prove that supplied coordinate facts for strict Eq5 records, the upper
endpoint record, and the explicitly inserted rising lower endpoint record pass
through the conditional raw branch set and then through the base-value filter.
This gives the coordinate-correctness input to the existing generic
counted-datum classifier constructor, but no dedicated Eq5 classifier wrapper
was added.  The result does not prove source-produced branch records,
source-label legality, endpoint distinctness, base-filter survival, raw
injectivity/disjointness, no-extra coverage, normal crossings, pole order, or
RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-branchcoord-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-branchcoord.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-branchcoord-a5.md`.

Latest A5 Eq5 endpoint branch-coordinate disjointness update:
`Lemma5Eq5SuppliedCoverage.lean` now also contains
`aoyagiLemma5Eq5EndpointRawBranches_pairwiseDisjoint_of_branchCoord_eq` and
`AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_branchCoord`.
These prove cross-coordinate disjointness for Eq5 endpoint raw branch sets at
distinct interior coordinates from supplied component coordinate facts, and
use it to remove the separate raw-disjointness hypothesis from the supplied
endpoint constructor.  This still leaves raw value injectivity, base-value
membership, alpha coverage, endpoint values, source-produced branch records,
source-label legality, no-extra coverage, normal crossings, pole order, and
RLCT unproved.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-branchcoord-disjoint-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-branchcoord-disjoint.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-branchcoord-disjoint-a5.md`.

Latest A5 Eq5 endpoint raw value-injectivity update:
`Lemma5Eq5SuppliedCoverage.lean` now also contains
`aoyagiLemma5Eq5EndpointRawBranches_value_injective_of_alpha_injective` and
`AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord`.
These derive one-coordinate raw value injectivity from strict alpha-domain
coverage, strict value formulas, endpoint value formulas, and supplied strict
alpha injectivity.  The result is deliberately interior-coordinate: at `j=0`,
upper and lower endpoint values can coincide.  The wrapper combines this with
coordinate-disjointness to remove only raw value-injectivity and
raw-disjointness inputs from the strictest Eq5 endpoint constructor.  It still
does not construct branch records, prove source-label legality, prove strict
alpha injectivity from source, prove base-filter survival, construct no-extra
coverage, prove normal crossings, pole order, or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-value-injective-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-value-injective.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-value-injective-a5.md`.

Latest A5 Eq5 endpoint counted-datum classifier update:
`Lemma5Eq5SuppliedCoverage.lean` now also contains
`AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord_branchCoord_eq`
and
`AoyagiLemma5SuppliedNonbaseFamily.countDatumClassifierOfEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord`.
The first theorem passes component coordinate correctness through the
base-value-filtered strictest endpoint supplied family; the second applies the
generic supplied-family counted-datum classifier API to that constructed
`fullBranches` set.  This is not a source terminal-minimum classifier and does
not prove source-label legality, base-filter survival, no-extra coverage,
normal crossings, pole order, or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-countdatum-classifier-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-countdatum-classifier.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-countdatum-classifier-a5.md`.

Latest A5 Eq5 terminal pAlpha endpoint cardinal-squeeze update:
`Lemma5Eq5TerminalClassifier.lean` now also contains
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_endpointBase_cardSqueeze`
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_endpointBase_cardSqueeze`.
These combine the existing terminal counted-datum injection adapter from
supplied Eq5 payloads plus terminal `(p, alpha)` injectivity with the
terminal-endpoint-base branch-label injection adapter, then apply the existing
finite cardinal squeeze.  They prove conditional terminal-minimum exactness
and exact cardinality only under supplied hypotheses; they are not
source-backed no-extra coverage, branch construction, pole-order, normal
crossing, or RLCT theorems.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-terminal-palpha-endpoint-cardinal-squeeze-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-terminal-palpha-endpoint-cardinal-squeeze.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-terminal-palpha-endpoint-cardinal-squeeze-a5.md`.

Latest A5 Eq5 endpoint raw-cardinality update:
`Lemma5Eq5SuppliedCoverage.lean` now also contains
`aoyagiLemma5Eq5EndpointRawBranches_card_eq_intervalSize_of_value_injective`
and
`aoyagiLemma5Eq5EndpointRawBranches_card_eq_intervalSize_of_alpha_injective`.
The proof counts the one-coordinate raw endpoint branch set through its
injective value image and the Htilde interval value-set cardinality; the
alpha-injective wrapper derives the needed raw value injectivity from the
previous endpoint theorem.  This is raw finite bookkeeping only, not
base-filter survival, filtered nonbase count, terminal-minimum exactness,
source-backed no-extra coverage, pole order, normal crossings, or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-raw-cardinality-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-raw-cardinality.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-raw-cardinality-a5.md`.

Latest A5 Eq5 endpoint filtered-cardinality update:
`Lemma5Eq5SuppliedCoverage.lean` now also contains
`AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_branch_card_eq_intervalSize_sub_one`,
`AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_fullBranches_card`,
and
`AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord_fullBranches_card`.
These specialize the generic supplied-family cardinality theorems to the Eq5
endpoint constructors.  The one-coordinate theorem counts the filtered
coordinate branch set after erasing the supplied base value; the full-branch
wrappers count the tagged supplied branch family, including the supplied base
branch.  This is not raw branch cardinality, terminal-minimum label
cardinality, source branch construction, source-label legality,
source-backed no-extra coverage, normal crossings, pole order, or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-filtered-cardinality-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-filtered-cardinality.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-filtered-cardinality-a5.md`.

Latest A5 Eq5 value-label branch-injection update:
`Lemma5Eq5TerminalClassifier.lean` now also contains
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_nonbase_valueLabel`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_nonbase_valueLabel_terminalEndpointBase`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze`,
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze`.
The branch-label theorem uses supplied selected-block membership and the
supplied nonbase value-label relation
`TC.family.value b = ((TC.branchLabel (some b)).2 : Z) - 1` to prove
branch-label injectivity; the endpoint wrapper supplies base/nonbase
separation from the terminal-endpoint base label.  The terminal cardinal
squeeze then composes this with the existing terminal `(p, alpha)`
counted-datum injection adapter.  This replaces branch-alpha data with
supplied value-label synchronisation, but it is still conditional on terminal
Eq5 payloads, terminal `(p, alpha)` injectivity, terminal-label nonbase
inequalities, and endpoint-base data.  It is not a source proof of the
value-label relation, branch construction, source-backed no-extra coverage,
normal crossings, pole order, or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-value-label-branch-injection-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-value-label-branch-injection.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-value-label-branch-injection-a5.md`.

Latest A5 Eq5 branch-coordinate/value cardinal-squeeze update:
`Lemma5Eq5TerminalClassifier.lean` now also contains
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchBlock_of_branchCoord_leftEndpoint`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.valueLabel_of_branchK_value`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_branchCoord_leftEndpoint_branchK_value_terminalEndpointBase`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_branchCoordVal_cardSqueeze`,
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_branchCoordVal_cardSqueeze`.
The adapters derive the selected-block and Sigma value-label inputs from
supplied branch-coordinate correctness, supplied left-endpoint `branchS`
labels, and supplied `branchK`/value synchronisation; then the wrappers
compose with the existing value-label branch-injection and terminal pAlpha
cardinal-squeeze route.  This is still conditional terminal-candidate
bookkeeping: terminal Eq5 payloads, terminal `(p, alpha)` injectivity,
terminal-label nonbase inequalities, and endpoint-base data remain supplied.
It is not source construction of branch coordinates or labels, source-backed
no-extra coverage, normal crossings, pole order, or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-branchcoord-value-cardinal-squeeze-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-branchcoord-value-cardinal-squeeze.md`,
and
`threads/05-arithmetic-tail/review-lemma5-eq5-branchcoord-value-cardinal-squeeze-a5.md`.

Latest A5 Eq5 strict endpoint filtered-cardinality update:
`Lemma5Eq5SuppliedCoverage.lean` now also contains
`AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_strict_branch_card_eq_intervalSize_sub_one`.
This closes the endpoint API asymmetry by specializing the one-coordinate
filtered count to the strictest endpoint constructor, discharging raw value
injectivity from supplied strict alpha injectivity and raw disjointness from
supplied component-coordinate facts.  It counts only filtered supplied
coordinate branches, not source records or terminal-minimum labels.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-strict-filtered-cardinality-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-strict-filtered-cardinality.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-strict-filtered-and-terminal-branchcoord-a5.md`.

Latest A5 Eq5 endpoint-to-terminal branch-coordinate update:
`Lemma5Eq5TerminalClassifier.lean` now also contains
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchCoord_of_toNonbase_eq_eq5EndpointCoverage`
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchBlock_of_toNonbase_eq_eq5EndpointCoverage_leftEndpoint`.
These transport endpoint branch-coordinate correctness into a supplied
terminal-candidate family only under an explicit equality between
`TC.family.toAoyagiLemma5SuppliedNonbaseFamily` and the strictest endpoint
constructor.  The selected-block wrapper still requires the supplied
left-endpoint `branchS` formula.  This is interface alignment only: it does
not construct Eq5 branches, prove source labels, identify terminal-minimum
labels with endpoint branches, prove no-extra coverage, or produce any
pole-order/RLCT result.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-to-terminal-branchcoord-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-to-terminal-branchcoord.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-strict-filtered-and-terminal-branchcoord-a5.md`.

Latest A5 Eq5 endpoint-family cardinal-squeeze update:
`Lemma5Eq5TerminalClassifier.lean` now also contains
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5EndpointFamily_branchCoordVal_cardSqueeze`
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5EndpointFamily_branchCoordVal_cardSqueeze`.
These compose the endpoint-to-terminal branch-coordinate transport with the
existing branch-coordinate/value terminal cardinal squeeze.  The explicit
endpoint-family equality supplies only branch-coordinate correctness; terminal
Eq5 payloads, terminal `(p, alpha)` injectivity, `branchS`, `branchK`,
terminal-label nonbase inequalities, and endpoint base label remain supplied.
This is not source construction, source-backed or direct back-to-label
no-extra terminal-minimum coverage, pole order, normal crossings, or RLCT
extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-family-cardinal-squeeze-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-family-cardinal-squeeze.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-family-cardinal-squeeze-a5.md`.

Latest A5 Eq5 endpoint-family block-width cardinal-squeeze update:
`Lemma5Eq5TerminalClassifier.lean` now also contains
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze`
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze`.
These replace the per-label terminal width-bound input of the endpoint-family
cardinal squeeze by the blockwise actual-width hypothesis, using the supplied
terminal label block membership and
`cut.selectedWidthNat_le_actualWidth_of_block`.  This is still only a
conditional handoff wrapper: terminal Eq5 payloads, terminal `(p, alpha)`
injectivity, endpoint-family equality, `branchS`, `branchK`,
terminal-label nonbase inequalities, blockwise actual-width data, and the
endpoint base label remain supplied.  It is not source construction,
source-backed or direct back-to-label no-extra terminal-minimum coverage, pole
order, normal crossings, or RLCT extraction.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-family-blockwidth-cardinal-squeeze-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-family-blockwidth-cardinal-squeeze.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-family-blockwidth-cardinal-squeeze-a5.md`.

Source-audit direction, 2026-06-22: freeze A5 as a supplied downstream
boundary for now.  The Aoyagi-only source audit found that PDF pp. 25-27's
printed Lemma 5 paragraph and Eq3/Eq4/Eq5 families do not by themselves give
a classifier, injection, back-to-label map, or complete Lemma 4 witness.  Do
not spend another slice trying to promote those printed families into a
source-backed no-extra theorem unless a corrected independent construction is
introduced.

Latest A4 Case 2 source-current row reindex update:
`BlowupArithmetic.lean` now contains, inside the
`Case2DisplayedSuppliedChartFamilyBoundary` namespace,
`case2SourceCurrentRowIndex`,
`case2SourceOldTopPaperCprimeRowEquiv`,
`case2SourceCurrentFollowingBlock`, `case2SourceSuccessorFollowingBlock`,
`case2SourceCurrentFollowingBlock_submatrix_oldTopPaperCprimeRowEquiv`, and
`case2SourceSuccessorFollowingBlock_submatrix_oldTopPaperCprimeRowEquiv`.
These identify source rows `1..n(S+1)` with the old-top rows, the displayed
pivot row, and post-pivot rows.  Under that equivalence the old following
block becomes `[oldTop; displayedSourceFollowingFactor]`, while the
formula-level successor following block becomes `[oldTop; paperCprime]`.
This is finite row-reindexing only: no chart production of `Csucc`, source
production of `C'^(S+1)`, suffix production, recurrence/exponent post-data,
transition invariant, Jacobian arithmetic, normal crossings, pole order,
termination, or RLCT is proved.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-source-current-row-reindex-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-source-current-row-reindex.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-current-row-reindex-a4.md`.

Latest A4 update: the Case 2 source-current stack slice has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean name is
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_continuingOldTopSourceSuffixSuccFollowingBlock_withCorrectedPostData`.
It restates the previous continuing old-top/source-suffix stack theorem in
source-current row coordinates, replacing `[oldTop; displayedSourceFollowingFactor]`
and `[oldTop; paperCprime]` by submatrices of
`case2SourceCurrentFollowingBlock` and `case2SourceSuccessorFollowingBlock`
under the finite source-row equivalence.  The theorem preserves next-center
nonemptiness, corrected post exponent data, post level/gap data, and finite
current-center principalization.  It is not chart production of `Csucc`,
source production of `C'^(S+1)`, source-suffix production, transition
invariance, normal crossings, pole order, termination, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-current-stack-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-current-stack.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-current-stack-a4.md`.

Latest A4 reproduction boundary: the Case 2 branchwise successor-production
contract is now recorded in
`threads/04-blow-up-certificate/reproduction-case2-branchwise-successor-production-boundary-a4.md`.
No Lean theorem is introduced.  The boundary says future source production
must distinguish the continuing branch, the actual-width stopped branch, and
the row-exhausted stopped branch, because their domains and row meanings
differ.  The contract keeps the standing displayed-pivot hypotheses explicit,
records the continuing payload as the stronger nonempty-next-center refinement
of Aoyagi's printed non-strict guard, and does not assert stopped-branch
exclusivity.  Existing Lean already covers the finite `Q/P` algebra,
`Q^-1 C` row formulas, lower-row products, source-current stack presentation,
actual-width original-row collapse, row-exhausted transported-prefix
presentations, and current-center principalization.  Still open are source
production of full `C'^(S+1)`, successor chart-family construction, coverage,
transition regularity, suffix/following-product production, coordinate
derivation of corrected post-data, Jacobian arithmetic, normal crossings,
pole order, termination, and RLCT.  Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-branchwise-successor-production-boundary.md`.
Review:
`threads/04-blow-up-certificate/review-case2-branchwise-successor-production-boundary-a4.md`.

Latest A4 interface update: the branchwise Case 2 source-production frontier
is now named in Lean as the supplied `Prop` structure
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation`.
The structure packages the current frontier boundary, the formula equality
for a supplied successor following object `Csucc`, the weighted
successor-following continuing payload, the actual-width stopped payload with
`sourceSuffixProduct`, actual-width original terminal rows and relabelled
`(S+1,0)` certificates, and the row-exhausted transported-prefix payload plus
transported-row terminal equality.  The formerly present supplied next
chart-family field has since been removed as vacuous.  It deliberately has no
constructor from the current displayed chart boundary.  This is not source
production of `C'^(S+1)`, not suffix production, not coverage or transition
invariance, not coordinate derivation of corrected post-data, and not
Jacobian/normal-crossing/pole-order/RLCT content.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-source-production-obligation-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-source-production-obligation.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-production-obligation-a4.md`.

Latest A4 finite handoff update: the continuing weighted source-following
frontier payload now has a successor-notation adapter in Lean:
`continuingWeightedSuccFollowingFrontierPayload_of_sourceFollowing`, plus the
package projection
`SourceChartFrontierBoundaryPackages.continuingWeightedSuccFollowing`.
The proof uses only
`case2SourceFollowingFactor_successorFollowingFactor_succ`: the next
same-stage following-factor restriction at `(S,J+1)` ignores row `J+1`, where
the canonical formula-level successor following factor differs from the old
source following function.  This closes a theorem-only projection; it is not
an arbitrary supplied-`Csucc` theorem without a separate equality to
`case2DisplayedSourceSuccessorFollowingFactor`, and it does not move the open
source-production boundary.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-continuing-successor-following-handoff-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-continuing-successor-following-handoff.md`.
Review:
`threads/04-blow-up-certificate/review-case2-continuing-successor-following-handoff-a4.md`.

Latest A4 projection update: the supplied
`SourceProductionObligation` now exposes the row-exhausted terminal matrix as
original rows of the supplied successor following factor:
`SourceProductionObligation.rowExhausted_Cterm_eq_originalRows_Csucc`.
This is the safe downstream use of the obligation's supplied row-exhausted
terminal-row equality together with `Csucc_eq_formula`: under the supplied
row-exhausted branch hypothesis, `Cterm` is transported-prefix rows of old
`C`, which are already known to be original terminal rows of the canonical
successor factor, and the obligation identifies that factor with supplied
`Csucc`.  This still does not construct the obligation, source-produce
`C'^(S+1)`, produce a suffix, or move the open chart/coverage/post-data
boundary.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-source-production-obligation-row-exhausted-csucc-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-source-production-obligation-row-exhausted-csucc.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-production-obligation-row-exhausted-csucc-a4.md`.

Latest A4 supplied-obligation projection update: `SourceProductionObligation`
now also exposes the continuing tail of supplied `Csucc` and the actual-width
terminal rows:
`SourceProductionObligation.continuing_Csucc_tail_eq_original` and
`SourceProductionObligation.actualWidth_Cterm_eq_originalRows_Csucc`.  The
continuing theorem uses only `Csucc_eq_formula` and the finite fact that the
next same-stage following-factor restriction ignores the replaced row `J+1`.
The actual-width theorem uses `actualWidth_Cterm_eq`, the actual-width
collapse of the canonical successor factor to old `C`, and `Csucc_eq_formula`.
These are consequence theorems for an already supplied obligation; they do
not construct the obligation, source-produce `Csucc` or `C'^(S+1)`, produce a
suffix, or move chart/coverage/post-data boundaries.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-source-production-obligation-csucc-projections-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-source-production-obligation-csucc-projections.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-production-obligation-csucc-projections-a4.md`.

Latest A4 supplied-obligation constructor update:
`SourceProductionObligation.of_formulaSuccessor_transportTerminalRows`
constructs the obligation using canonical formula-level choices
`Csucc = case2DisplayedSourceSuccessorFollowingFactor ... C` and
`Cterm = case2DisplayedSourceTerminalTransportedRows ... C`.  The existing
frontier package supplies continuing/actual-width/row-exhausted payloads;
actual-width terminal original-row equality first uses that transported rows
are original rows of the canonical successor factor and then uses the
actual-width collapse to old `C`; row-exhausted terminal transported-row
equality is reflexive.  This is still supplied-boundary assembly: it does not
construct the continuing next chart-family, source-produce `Csucc` from
coordinates, produce suffixes, coverage,
transition regularity, coordinate post-data, normal crossings, pole order, or
RLCT.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-source-production-obligation-canonical-formula-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-source-production-obligation-canonical-formula.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-production-obligation-canonical-formula-a4.md`.

Latest A4 API-hardening update: the continuing next chart-family existential
inside the canonical formula-level obligation is formally discharged by
trivial predicates.  Lean proves
`SelectedEntryChartFamilyBoundary.exists_trivial`,
`Case2ResidualBlockChartFamilyBoundary.exists_trivial`,
and
`Case2ResidualBlockChartFamilyBoundary.continuingSuccessorBoundary_exists_truePredicates`.
This is a useful precision correction, not progress on source production:
the current `SelectedEntryChartFamilyBoundary` API only asks for implications
into arbitrary predicates, so choosing `True` satisfies it.  Xhigh source scout
`Sartre the 2nd` checked Aoyagi pp. 19-22 and found no source construction of
the next chart family, transition regularity, coverage, full successor
`C'^(S+1)`, or suffix production; the paper only says the induction continues.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-trivial-next-chart-family-boundary-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-trivial-next-chart-family-boundary.md`.
Review:
`threads/04-blow-up-certificate/review-case2-true-predicate-next-boundary-a4.md`.

Latest A4 API-hardening update: the vacuous next-chart-family field has been
removed from `SourceProductionObligation`.  The main canonical formula-level
constructor is now
`SourceProductionObligation.of_formulaSuccessor_transportTerminalRows`; the
old supplied-next-boundary and true-predicate-next-boundary constructor names
were removed from the current Lean API rather than kept as ignored-argument
wrappers.  This removes a misleading field from the obligation but does not
construct a successor atlas, source-produce `Csucc` or
`C'^(S+1)`, produce suffixes, prove meaningful coverage/transition regularity,
derive corrected post-data from coordinates, prove normal crossings, pole
order, termination, or RLCT.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-source-production-obligation-remove-vacuous-next-boundary-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-source-production-obligation-remove-vacuous-next-boundary.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-production-obligation-remove-vacuous-next-boundary-a4.md`.

Latest A4 supplied-obligation consumer update: Lean now names the
row-exhausted source-suffix frontier with its terminal prefix written through
the supplied terminal matrix and projects it from
`SourceProductionObligation`:
`RowExhaustedSourceSuffixSuppliedCtermPrefixPayload` and
`SourceProductionObligation.rowExhausted_frontier_suppliedCtermPrefix`.
Under the supplied row-exhausted branch hypothesis, this consumes the
obligation's existing transported-prefix frontier plus
`Cterm = transportedRows(C)` and rewrites only the terminal prefix factor to
`Cterm.submatrix ...`; the source suffix and finite center facts are
unchanged.  It does not construct the obligation, `Cterm`, `Csucc`,
`C'^(S+1)`, suffixes, successor charts, coverage, transitions, coordinate
post-data, normal crossings, pole order, termination, or RLCT.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-source-production-obligation-row-exhausted-cterm-frontier-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-source-production-obligation-row-exhausted-cterm-frontier.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-production-obligation-row-exhausted-cterm-frontier-a4.md`.

Latest A5 finite-obstruction update: `Lemma5TerminalBridge.lean` now contains
`terminalMinimumLabels_eq_branchLabelImage_of_card_bound_and_branchLabel_injOn`
and
`terminalMinimumLabelExactness_iff_branchLabel_injOn_and_card_bound`.
These say that, after supplied branches attain the terminal minimum, the
remaining terminal exactness obstruction is exactly supplied branch-label
injectivity plus a supplied upper bound
`terminalMinimumLabels.card <= a*(n+1-a)+1`.  This is finite set/cardinality
bookkeeping only; it does not construct the upper bound, branch-label
injectivity, no-extra coverage, pole order, normal crossings, or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-exactness-card-bound-equivalence-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-exactness-card-bound-equivalence.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-exactness-card-bound-equivalence-a5.md`.

Latest A5-to-A6 terminal order handoff: `Lemma5TerminalOrderBridge.lean` now
rewrites the remaining supplied Lemma 5 terminal-exactness obstruction in
Aoyagi Theorem 2 order notation:
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_iff_branchLabel_injOn_and_theorem2OrderFormula_bound`
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_card_bound_and_branchLabel_injOn`.
For Definition 3 ceil data with `ell=n+1`, branch-label injectivity plus the
supplied upper bound
`terminalMinimumLabels.card <= data.theorem2OrderFormula` imply
`terminalMinimumLabels.card = data.theorem2OrderFormula`.  This is finite
bookkeeping only; the upper bound, branch-label injectivity, no-extra
coverage, pole order, normal crossings, and RLCT remain unproved.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-order-formula-bridge-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-order-formula-bridge.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-order-formula-bridge-a5.md`.

Latest A5 counted-datum order-formula handoff:
`Lemma5TerminalOrderBridge.lean` now also routes a supplied
`TerminalMinimumCountDatumClassifier` straight to the Theorem 2 order-formula
bound:
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_theorem2OrderFormula_of_countDatumClassifier`
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_countDatumClassifier_and_branchLabel_injOn`.
This consumes the existing counted-datum upper-bound API and rewrites
`a*(n+1-a)+1` as `data.theorem2OrderFormula`; equality still also requires
supplied branch-label injectivity.  It is a finite handoff wrapper only, not
source construction of the classifier, injectivity, back-to-label coverage,
no-extra terminal-minimum coverage, pole order, normal crossings, or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-countdatum-classifier-order-formula-bridge-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-countdatum-classifier-order-formula-bridge.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-countdatum-classifier-order-formula-bridge-a5.md`.

Latest A5 terminal order classifier-notation handoff:
`Lemma5TerminalOrderBridge.lean` now also exposes the existing
upper-bound-classifier and counted-datum back-to-label routes in Theorem 2
order notation:
`terminalMinimumLabels_card_le_theorem2OrderFormula_of_upperBoundClassifier`,
`terminalMinimumLabels_card_eq_theorem2OrderFormula_of_upperBoundClassifier_and_branchLabel_injOn`,
`terminalMinimumLabels_card_le_theorem2OrderFormula_of_countDatumBackToBranchLabel`,
and
`terminalMinimumLabels_card_eq_theorem2OrderFormula_of_countDatumBackToBranchLabel_and_injOn`.
These are definitional rewrites from `a*(n+1-a)+1` to
`data.theorem2OrderFormula`; the classifiers, back-to-label bridge, and
branch-label injectivity remain supplied.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-order-classifier-notation-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-order-classifier-notation.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-order-classifier-notation-a5.md`.

Latest A6 finite-certificate bridge: `Theorem2FiniteExponentBridge.lean` now
constructs `AoyagiTheorem2FiniteExponentFormulaHypothesis` from the A0 finite
min/order certificate API.  If a supplied active coordinate realizes
`aoyagiTheorem2Lambda_fromCeilData ...`, that displayed value lower-bounds
every active ratio, a supplied chart has
`minCountInChart = data.theorem2OrderFormula`, and every chart count is at
most `data.theorem2OrderFormula`, Lean fills the two finite exponent formula
fields.  With the explicit A0 extraction hypothesis supplied, Lean also
derives the final ceiling-data pair for `lambda` and `poleOrder`.  This still
does not construct exponent data, prove chart production, prove active-ratio
inequalities or chart-count bounds, prove Lemma 5 no-extra coverage, prove
pole order without A0, or extract RLCT.
Artifacts:
`threads/06-dln-translation/reproduction-theorem2-finite-certificate-bridge-a6.md`
and
`threads/06-dln-translation/statement-card-a6-theorem2-finite-certificate-bridge.md`.
Review:
`threads/06-dln-translation/review-theorem2-finite-certificate-bridge-a6.md`.

Latest A6 Case 2 finite-formula wrapper:
`Case2Theorem2FiniteExponentBridge.lean` now contains
`Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_centerCard_eq_fromCeilData`.
It consumes the supplied Case 2/A0 coordinate bridge, an explicit active-ratio
lower bound at `card(case2ResidualBlockPivotEntries n S J)/2`, a supplied
equality from that Case 2 center-cardinality ratio to
`aoyagiTheorem2Lambda_fromCeilData Lthm ell H r m data`, and a supplied order
equality `D.exponentOrder = data.theorem2OrderFormula`.  It fills
`AoyagiTheorem2FiniteExponentFormulaHypothesis D Lthm ell H r m data`.

This is finite bridge composition only.  It does not prove the lower bound,
the Case 2/Theorem 2 lambda equality, the order equality, selected-width
provenance, chart production, analytic extraction, pole order, or RLCT.
Artifacts:
`threads/06-dln-translation/reproduction-case2-theorem2-finite-formula-bridge-a6.md`
and
`threads/06-dln-translation/statement-card-a6-case2-theorem2-finite-formula-bridge.md`.
Review:
`threads/06-dln-translation/review-case2-theorem2-finite-formula-bridge-a6.md`.

Latest A6 Case 2 ratio-count finite-formula wrapper:
`Case2Theorem2FiniteExponentBridge.lean` now also contains
`Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_centerCard_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le`.
It uses the Case 2 supplied minimum theorem to identify the Case 2 ratio with
`D.exponentMinimum`, then converts supplied chart-count data at that ratio
into `D.exponentOrder = data.theorem2OrderFormula` via the A0 finite count
certificate API.  This replaces a raw supplied order equality by explicit
finite chart-count obligations, but it does not prove those obligations from
the source chart family.
Artifacts:
`threads/06-dln-translation/reproduction-case2-theorem2-ratio-count-finite-formula-bridge-a6.md`
and
`threads/06-dln-translation/statement-card-a6-case2-theorem2-ratio-count-finite-formula-bridge.md`.
Review:
`threads/06-dln-translation/review-case2-theorem2-ratio-count-finite-formula-bridge-a6.md`.

Latest A6 Case 2 chart-final wrapper:
`Case2Theorem2ChartFinalBridge.lean` contains
`Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2SuppliedChartFinalBoundary_of_forall_le_of_centerCard_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le`.
It packages selected-width provenance, the supplied chart-level extraction
hypothesis, and the Case 2 ratio-count finite formula bridge into
`AoyagiTheorem2SuppliedChartFinalBoundary`.

This is downstream plumbing only.  It does not construct the chart
certificate, prove chart coverage, prove active-ratio lower bounds, prove
chart-count facts, prove selected-width provenance, prove analytic extraction,
pole order, or RLCT.
Artifacts:
`threads/06-dln-translation/reproduction-case2-theorem2-chart-final-bridge-a6.md`
and
`threads/06-dln-translation/statement-card-a6-case2-theorem2-chart-final-bridge.md`.
Review:
`threads/06-dln-translation/review-case2-theorem2-chart-final-bridge-a6.md`.

Latest A6 terminal-order handoff: `Theorem2TerminalOrderBridge.lean` now
routes the order field of `AoyagiTheorem2FiniteExponentFormulaHypothesis`
through the supplied Lemma 5 terminal-minimum count.  If the exponent-minimum
formula is supplied, if the normal-crossing exponent order is supplied to be
`TC.terminalMinimumLabels.card`, and if the supplied Lemma 5 obstruction gives
branch-label injectivity plus
`TC.terminalMinimumLabels.card <= data.theorem2OrderFormula`, Lean constructs
the finite exponent formula boundary.  With selected-width provenance and A0
extraction also supplied, Lean obtains the final ceiling-data pair
`lambda = aoyagiTheorem2Lambda_fromCeilData ...` and
`poleOrder = data.theorem2OrderFormula`.  This does not prove chart-order
identification, the exponent-minimum formula, source-backed Lemma 5 no-extra
coverage, pole order without A0, normal crossings, or RLCT extraction.
Artifacts:
`threads/06-dln-translation/reproduction-theorem2-terminal-order-bridge-a6.md`
and
`threads/06-dln-translation/statement-card-a6-theorem2-terminal-order-bridge.md`.
Review:
`threads/06-dln-translation/review-theorem2-terminal-order-bridge-a6.md`.

Latest A6 active-ratio terminal-order handoff:
`Theorem2TerminalOrderBridge.lean` now also composes the A0 active-ratio
finite-minimum certificate with the supplied Lemma 5 terminal-order route.
The new wrappers take an active coordinate `p`, its ratio equality with
`aoyagiTheorem2Lambda_fromCeilData ...`, and the lower bound against every
active coordinate; they still take the supplied chart/order equality
`D.exponentOrder = TC.terminalMinimumLabels.card`, supplied branch-label
injectivity, and the supplied terminal upper bound.  With selected-width
provenance and A0 extraction, Lean derives the same final ceiling-data pair.
This does not construct exponent data, prove the active-ratio inequalities,
prove chart/order identification, prove source-backed Lemma 5 no-extra
coverage, prove pole order without A0, prove normal crossings, or extract
RLCT.
Artifacts:
`threads/06-dln-translation/reproduction-theorem2-active-terminal-order-bridge-a6.md`
and
`threads/06-dln-translation/statement-card-a6-theorem2-active-terminal-order-bridge.md`.
Review:
`threads/06-dln-translation/review-theorem2-active-terminal-order-bridge-a6.md`.

Latest A6 active chart-terminal-order handoff:
`Theorem2TerminalOrderBridge.lean` now also composes the A0 finite chart-count
maximum certificate into the same terminal-order route.  The new wrappers take
a supplied chart whose global-minimum coordinate count is
`TC.terminalMinimumLabels.card`, plus an upper bound by that same count for
every chart.  This replaces the raw supplied equality
`D.exponentOrder = TC.terminalMinimumLabels.card`; it does not construct the
chart, prove the chart counts from source, identify chart counts with
terminal labels from source, prove source-backed Lemma 5 no-extra coverage, or
move pole order/RLCT extraction.
Artifacts:
`threads/06-dln-translation/reproduction-theorem2-active-chart-terminal-order-bridge-a6.md`
and
`threads/06-dln-translation/statement-card-a6-theorem2-active-chart-terminal-order-bridge.md`.
Review:
`threads/06-dln-translation/review-theorem2-active-chart-terminal-order-bridge-a6.md`.

Latest A6 displayed-ratio count handoff:
`Theorem2TerminalOrderBridge.lean` now uses the A0 ratio-chart-count rewrite
so chart counts can be supplied at
`aoyagiTheorem2Lambda_fromCeilData ...` rather than at the internal
`D.exponentMinimum`.  The active-ratio certificate first identifies the
displayed value with the finite minimum; then the ratio-count chart witness
and all-chart upper bound certify
`D.exponentOrder = TC.terminalMinimumLabels.card`, after which the A5
terminal-order bridge rewrites to `data.theorem2OrderFormula`.  This still
does not source-prove the ratio inequalities, chart counts, Lemma 5 no-extra
coverage, normal crossings, pole order, or RLCT.
Artifacts:
`threads/06-dln-translation/reproduction-theorem2-ratio-count-terminal-order-bridge-a6.md`
and
`threads/06-dln-translation/statement-card-a6-theorem2-ratio-count-terminal-order-bridge.md`.
Review:
`threads/06-dln-translation/review-theorem2-ratio-count-terminal-order-bridge-a6.md`.

Latest A6 counted-datum terminal-order handoff:
`Theorem2TerminalOrderBridge.lean` now has counted-datum classifier variants
of the terminal-order final sockets.  Each variant keeps the previous
active-ratio/chart-count hypotheses and supplied branch-label injectivity, but
replaces the raw upper-bound input
`TC.terminalMinimumLabels.card <= data.theorem2OrderFormula` by a supplied
`TC.TerminalMinimumCountDatumClassifier`.  The new names use the suffix
`_of_classifier` or `_classifier` to stay within the line-length linter:
`theorem2FiniteExponentFormulaHypothesis_of_terminalMinimumLabels_card_of_classifier`,
`theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card_of_classifier`,
`theorem2FiniteExponentFormulaHypothesis_of_activePair_chartCount_classifier`,
`theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_classifier`,
the corresponding four `theorem2SuppliedFinalBoundary...` wrappers, and the
corresponding four `lambda_and_poleOrder...` pair wrappers.  This is finite
A5-to-A6 handoff only; it does not construct the classifier, branch-label
injectivity, back-to-label data, source chart counts, pole order without A0,
normal crossings, or RLCT.
Artifacts:
`threads/06-dln-translation/reproduction-theorem2-countdatum-terminal-order-bridge-a6.md`
and
`threads/06-dln-translation/statement-card-a6-theorem2-countdatum-terminal-order-bridge.md`.
Review:
`threads/06-dln-translation/review-theorem2-countdatum-terminal-order-bridge-a6.md`.

Latest A4 Case 2 continuing supplied-`Csucc` stack consumer:
`BlowupArithmetic.lean` now contains
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.continuing_Csucc_currentFollowingBlock_eq_formula`
and
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.continuing_sourceCurrentStack_suppliedCsucc`.
Given a supplied `SourceProductionObligation` and the continuing guard
`J+2 <= prefixMinNat n (S+1)`, the existing old-top/source-suffix stack
payload is rewritten with `case2SourceCurrentFollowingBlock n S Csucc` on the
successor side.  This consumes only `Csucc_eq_formula` plus the already proved
source-current stack theorem; it is not construction of `Csucc`, source
suffixes, successor charts, transition regularity, normal crossings, pole
order, termination, or RLCT.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-source-production-obligation-continuing-csucc-stack-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-source-production-obligation-continuing-csucc-stack.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-production-obligation-continuing-csucc-stack-a4.md`.

Latest A4 Case 2 actual-width supplied-`Cterm` frontier consumer:
`BlowupArithmetic.lean` now contains
`Case2DisplayedSuppliedChartFamilyBoundary.ActualWidthSourceSuffixSuppliedCtermPayload`
and
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.actualWidth_frontier_suppliedCterm`.
Given a supplied `SourceProductionObligation` and actual-width exhaustion
`n(S+1)=J+1`, the existing actual-width stopped frontier is restated with the
supplied terminal matrix `Cterm` in the terminal factor.  This consumes only
`actualWidth_frontier` and `actualWidth_Cterm_eq`; the source suffix, finite
center, relabelled level, and relabelled exponent payloads are unchanged.  It
does not construct `Cterm`, `Csucc`, successor source data, suffixes, charts,
coverage, transition regularity, coordinate post-data, normal crossings, pole
order, termination, or RLCT.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-source-production-obligation-actual-width-cterm-frontier-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-source-production-obligation-actual-width-cterm-frontier.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-production-obligation-actual-width-cterm-frontier-a4.md`.

Latest A4 selected-entry center-square/formal-Jacobian microcertificate:
`BlowupArithmetic.lean` now contains `selectedEntryCenterSq`,
`selectedEntryCenterSq_selectedEntryChartMap`,
`selectedEntryPivotFirstJacobian`, `selectedEntryPivotFirstJacobian_det`,
`SelectedEntryChartFamilyData.centerSq_chartMap`,
`case2DisplayedSourceChartMap_centerSq`,
`case2DisplayedSourceChartMap_pivotFirstJacobian_det`, and
`case2DisplayedSourceChartMap_pivotFirstJacobian_exponent_eq_centerCard_sub_one`.
The square-sum theorem proves that the finite selected-entry center square
pulls back as `u^2` times the normalized square-sum.  The determinant theorem
proves the formal pivot-first block determinant `det [1 0; y uI] =
u^(non-pivot count)` and the displayed Case 2 wrapper identifies the exponent
with the residual-block center cardinality minus one.  This is useful
A0-facing local algebra, but it is not an A0 normal-crossing chart
certificate: no analytic unit nonvanishing for the normalized factor, no
actual derivative/Jacobian theorem, no chart coverage, no transition
regularity, no pole order, and no RLCT extraction is proved.  Aoyagi's later
regular `P` and `Q` changes still require their own analytic/unit/Jacobian
treatment before a full chart certificate can use this as volume-form data.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-selected-entry-center-sq-jacobian-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-selected-entry-center-sq-jacobian.md`.
Review:
`threads/04-blow-up-certificate/review-case2-selected-entry-center-sq-jacobian-a4.md`.

Latest A4 selected-entry center unit-factor microcertificate:
`BlowupArithmetic.lean` now contains `selectedEntryCenterSq_nonneg`,
`selectedEntryCenterSqUnitFactor`,
`selectedEntryCenterSqUnitFactor_pos`,
`selectedEntryCenterSqUnitFactor_ne_zero`,
`selectedEntryCenterSqUnitFactor_isUnit`,
`case2DisplayedSourceChartMap_centerSqUnitFactor_pos`,
`case2DisplayedSourceChartMap_centerSqUnitFactor_ne_zero`, and
`case2DisplayedSourceChartMap_centerSqUnitFactor_isUnit`.  These prove that
the normalized finite selected-entry square-sum factor
`1 + selectedEntryCenterSq center value` is positive and nonzero under the
ordered commutative semiring hypotheses used by Mathlib, and is a unit over
an ordered field.  The displayed Case 2 wrappers specialize this to the erased
residual-block center
`(case2ResidualBlockPivotEntries n S J).erase (J+1,J+1)`.

This closes only the pointwise finite unit fact for that selected-entry
square-sum factor.  It is not arbitrary-field or complex-field algebra, not
analytic unit control on a constructed chart neighbourhood, not unit control
for Aoyagi's later regular `P`/`Q` changes, not a total loss unit, not a
Jacobian/volume-form theorem, not an A0 normal-crossing chart certificate, and
not pole order or RLCT extraction.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-selected-entry-center-unit-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-selected-entry-center-unit.md`.
Review:
`threads/04-blow-up-certificate/review-case2-selected-entry-center-unit-a4.md`.

Latest A4 continuing source-chart unit-certificate refinement:
`BlowupArithmetic.lean` now contains
`Case2DisplayedContinuingReindexedSourceChartUnitCertificate` and
`sourceChartMap_continuingReindexedSourceChartUnitCertificate`.  This is an
ordered-field refinement of the displayed continuing Case 2 local
certificate: it carries the existing
`Case2DisplayedContinuingReindexedSourceChartCertificate` and adds
positivity, nonzero, and `IsUnit` witnesses for the normalized selected-entry
center-square factor on the erased residual-block center.

This moves one selected-entry unit witness into the A4-local certificate
layer.  It is still not analytic unit control on a constructed neighbourhood,
not unit control for Aoyagi's later `P`/`Q` changes, not a total loss unit,
not a Jacobian/volume-form theorem, not chart coverage or transition
regularity, not an A0 normal-crossing chart certificate, and not pole order or
RLCT extraction.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-continuing-reindexed-source-chart-unit-certificate-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-continuing-reindexed-source-chart-unit-certificate.md`.
Review:
`threads/04-blow-up-certificate/review-case2-continuing-reindexed-source-chart-unit-certificate-a4.md`.

Latest A4/A0 continuing center-square/formal-Jacobian certificate:
`BlowupArithmetic.lean` now contains `case2DisplayedPaperQ_isUnit`,
`case2DisplayedPaperQ_det_isUnit`, `case2DisplayedPaperQinv_isUnit`,
`case2DisplayedPaperQinv_det_isUnit`,
`Case2DisplayedContinuingReindexedSourceChartCenterSqFormalJacobianCertificate`,
`sourceChartMap_continuingReindexedSourceChartCenterSqFormalJacobianCertificate`,
and
`Case2DisplayedContinuingReindexedSourceChartCertificate.exists_reindexedNextSourceProduct_with_PQ_det_units`.
This packages the displayed continuing Case 2 local certificate together with
the finite center-square factorization, the pointwise ordered-field unit
witness, the formal pivot-first determinant equality
`det [1 0; y uI] = u^(erased-center cardinality)`, the cardinal arithmetic
identifying the formal determinant exponent as center cardinality minus one,
and the finite equality saying the corrected new numerator is that exponent
plus one.  It also exposes determinant-unit witnesses for the displayed
`Q/Q^-1` finite column operations and the supplied `P` row-operation witness.

This is an A4/A0-facing finite step contribution only.  It is not a
differentiable Jacobian theorem, not a volume-form theorem, not analytic unit
control for all chart factors, not a total DLN loss monomial identity, not
chart coverage or transition regularity, not an
`AoyagiNormalCrossingChartCertificate`, and not pole order or RLCT
extraction.  The p. 21 source display with an apparent extra outside `u` is
explicitly not formalised as a literal product identity.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-continuing-center-sq-formal-jacobian-certificate-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-continuing-center-sq-formal-jacobian-certificate.md`.
Review:
`threads/04-blow-up-certificate/review-case2-continuing-center-sq-formal-jacobian-certificate-a4.md`.

Latest A4/A0 Case 2 supplied exponent-coordinate bridge:
`NormalCrossingInterface.lean` now contains the generic finite A0 helpers
`AoyagiNormalCrossingExponentData.mem_activePairs_of_lossExp_eq_one` and
`AoyagiNormalCrossingExponentData.ratioAt_eq_nat_div_two_of_lossExp_eq_one_of_jacobianPriorExp_add_one_eq`.
The new module `Case2FiniteExponentBridge.lean` contains
`Case2DisplayedContinuingA0ExponentCoordinateBridge`,
`Case2DisplayedContinuingA0ExponentCoordinateBridge.activePair_and_ratioAt_eq_centerCard_div_two`,
`Case2DisplayedContinuingA0ExponentCoordinateBridge.activePair`, and
`Case2DisplayedContinuingA0ExponentCoordinateBridge.ratioAt_eq_centerCard_div_two`.

The bridge consumes a supplied A0 exponent datum `D`, a supplied coordinate
`p`, and a displayed continuing Case 2 local certificate.  If the supplied
coordinate has `lossExp = 1` and `jacobianPriorExp` equal to the formal
pivot-first determinant exponent, Lean proves `p in D.activePairs` and
`D.ratioAt p = card(case2ResidualBlockPivotEntries n S J)/2`.  It deliberately
does not construct `D` or `p`, prove a global minimum, prove an exponent-order
count, construct charts, or upgrade the formal determinant to an analytic
Jacobian/volume-form theorem.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-a0-exponent-coordinate-bridge-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-a0-case2-exponent-coordinate-bridge.md`.
Review:
`threads/04-blow-up-certificate/review-case2-a0-exponent-coordinate-bridge-a4.md`.

Latest A4/A0 Case 2 exponent-minimum bridge:
`Case2FiniteExponentBridge.lean` now contains
`Case2DisplayedContinuingA0ExponentCoordinateBridge.exponentMinimum_eq_centerCard_div_two_of_forall_le`.
It consumes the supplied Case 2/A0 exponent-coordinate bridge and an explicit
global lower bound

```text
forall p' in D.activePairs,
  card(case2ResidualBlockPivotEntries n S J)/2 <= D.ratioAt p'
```

to prove

```text
D.exponentMinimum = card(case2ResidualBlockPivotEntries n S J)/2.
```

This is only finite `Finset.min'` bookkeeping.  The lower bound itself is not
proved, and the result does not produce A0 exponent data, chart coverage,
analytic Jacobian/volume-form data, exponent order, pole order, or RLCT
extraction.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-a0-exponent-minimum-bridge-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-a0-case2-exponent-minimum-bridge.md`.
Review:
`threads/04-blow-up-certificate/review-case2-a0-exponent-minimum-bridge-a4.md`.

Latest A4/A0 selected-entry finite normal-crossing microcertificate:
`SelectedEntryNormalCrossing.lean` now contains
`selectedEntryCenterSqFormalJacobianChartCertificate`,
`case2DisplayedCenterSqFormalJacobianChartCertificate`,
`case2DisplayedCenterSqFormalJacobianChartCertificate.lossExp_zero_zero`,
`case2DisplayedCenterSqFormalJacobianChartCertificate.jacobianPriorExp_zero_zero`,
and
`case2DisplayedCenterSqFormalJacobianChartCertificate.localExponentCoordinateBridge`.
The generic certificate packages the selected-entry finite center-square
pullback as a one-chart `AoyagiNormalCrossingChartCertificate`: the single
coordinate has loss exponent `1`, the parameter is the finite-center value
function, the residual coordinates are indexed by `center.erase pivot`, the
loss unit is the normalized square-sum factor, and the `jacobianPrior` field
is the formal pivot-first determinant `u ^ card(center.erase pivot)`.  The
Case 2 specialization uses the displayed pivot `(J+1,J+1)`, and for this
local microcertificate's own exponent data Lean constructs the Case 2/A0
exponent-coordinate bridge by reflexive exponent-array equalities.

This is a local finite normal-crossing microcertificate only.  It is not
chart coverage, source production of successor data, analytic regularity, an
analytic Jacobian/volume-form theorem, a total DLN loss monomial identity, a
global A0 chart family, active-ratio lower bounds, pole order, or RLCT
extraction.
Artifacts:
`threads/04-blow-up-certificate/reproduction-selected-entry-normal-crossing-microcertificate-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-normal-crossing-microcertificate.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-normal-crossing-microcertificate-a4.md`
passed after polish.

Latest A4 selected-entry local finite exponent minimum/order:
`SelectedEntryNormalCrossing.lean` now also proves
`selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_ratioAt_zero_zero`,
`selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_exponentMinimum_eq_centerCard_div_two`,
`selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_minCountInChart_le_one`,
`selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_exponentOrder_eq_one`,
`case2DisplayedCenterSqFormalJacobianChartCertificate.exponentData_ratioAt_zero_zero`,
`case2DisplayedCenterSqFormalJacobianChartCertificate.exponentData_exponentMinimum_eq_centerCard_div_two`,
and
`case2DisplayedCenterSqFormalJacobianChartCertificate.exponentData_exponentOrder_eq_one`.
For the one-coordinate local microcertificate, the finite ratio and finite
minimum are `center.card / 2`, and the finite order is `1`; the Case 2
specialization replaces `center` by `case2ResidualBlockPivotEntries n S J`.
This is only the microcertificate's own finite exponent data.  It does not
prove the global A0 minimum, a global A0 order count, chart production, pole
order, or RLCT extraction.
Artifacts:
`threads/04-blow-up-certificate/reproduction-selected-entry-local-exponent-min-order-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-local-exponent-min-order.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-local-exponent-min-order-a4.md`
passed.

Latest A4 Case 2 direct reindexed next-source product:
`BlowupArithmetic.lean` now contains
`sourceChartMap_reindexedNextSourceProduct_fromCase2SuccCorrectedPostData`.
It proves the displayed source-chart `Q/P` identity reindexed to the next
same-stage source-product shape directly from the low-level finite `Q/P`
identity, the old level/least-value gap, concrete `case2Succ` recurrence
post-data, and corrected selected-label exponent overrides.  The old theorem
`sourceChartMap_reindexedNextSourceProduct_withCorrectedPostData` remains as
a compatibility wrapper and now delegates to the direct theorem, so the finite
product/post-data theorem no longer depends on a supplied
`Case2ResidualBlockChartFamilyBoundary`.

This is a boundary removal for finite Case 2 algebra only.  It does not
source-produce `Csucc`, construct successor chart families or suffixes, prove
coverage/transition regularity, provide analytic Jacobian/volume-form data,
prove normal crossings, pole order, or RLCT extraction.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-reindexed-next-source-product-direct-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-reindexed-next-source-product-direct.md`.
Review:
`threads/04-blow-up-certificate/review-case2-reindexed-next-source-product-direct-a4.md`
passed.

Latest A4 continuing certificate chart-family-free directification:
`BlowupArithmetic.lean` now contains
`sourceChartMap_continuingReindexedSourceChartCertificate_withoutChartFamily`,
`sourceChartMap_continuingReindexedSourceChartUnitCertificate_withoutChartFamily`,
and
`sourceChartMap_continuingCenterSqFormalJacobianCertificate_withoutChartFamily`.
These constructors build the displayed continuing Case 2 local certificate,
its ordered-field unit refinement, and its center-square/formal-Jacobian
refinement from finite selected-entry algebra, concrete `case2Succ`
recurrence data, corrected selected-label exponent data, and the direct
reindexed next-source-product identity.  They take no `ChartRegular`,
`TransitionRegular`, or `Case2ResidualBlockChartFamilyBoundary` arguments.
The older chart-family-bearing constructors remain as compatibility wrappers
that delegate to the direct constructors.

This removes only the vacuous finite chart-family boundary from these local
continuing-certificate constructors.  It is not source production of `Csucc`,
not successor chart-family or suffix construction, not coverage/transition
regularity, not an analytic Jacobian/volume-form theorem, not normal
crossings, not pole order, and not RLCT extraction.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-continuing-certificate-without-chart-family-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-continuing-certificate-without-chart-family.md`.
Review:
`threads/04-blow-up-certificate/review-case2-continuing-certificate-without-chart-family-a4.md`
passed.

Latest A4 old-top/source-suffix paper-`C'` stack chart-family-free
directification:
`BlowupArithmetic.lean` now contains
`sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withoutChartFamily`.
It proves the same finite continuing stack identity as the old
`sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withCorrectedPostData`
theorem, but without `ChartRegular`, `TransitionRegular`, or
`Case2ResidualBlockChartFamilyBoundary` arguments.  The proof uses the
corrected new-label certificate, concrete `case2Succ` recurrence post-data,
corrected exponent post-data, the finite displayed `Q/P` witness,
old-top lifting by `fromBlocks_mul_verticalBlock_eq_of_tail`, and right
multiplication by the supplied raw source suffix.  The older API remains as a
compatibility wrapper that ignores its chart-family argument.

This is finite old-top/source-suffix paper-`C'` stack bookkeeping only.  It is
not source production of `Csucc` or `C'^(S+1)`, not suffix production, not
successor chart-family construction, not coverage/transition regularity, not
an analytic Jacobian/volume-form theorem, not normal crossings, not pole
order, and not RLCT extraction.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-continuing-oldtop-source-suffix-paper-cprime-stack-without-chart-family-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-continuing-oldtop-source-suffix-paper-cprime-stack-without-chart-family.md`.
Review:
`threads/04-blow-up-certificate/review-case2-continuing-oldtop-source-suffix-paper-cprime-stack-without-chart-family-a4.md`
passed.

Latest A4 paper-`C'` lower-row chart-family-free directification:
`BlowupArithmetic.lean` now contains
`sourceChartMap_paperCprimeWeightedLowerRows_withoutChartFamily` and
`sourceChartMap_paperCprimeWeightedLowerRows_mul_followingProduct_withoutChartFamily`.
They prove the same finite lower-row paper-`C'` handoff and arbitrary
right-multiplied supplied-`F` variant as the old chart-family-bearing APIs,
but without `ChartRegular`, `TransitionRegular`, or
`Case2ResidualBlockChartFamilyBoundary` arguments.  The direct proof uses the
corrected new-label certificate, concrete `case2Succ` recurrence post-data,
corrected exponent post-data, the finite displayed source `Q/P` identity,
lower-row projection, the weighted `D''' * C'` lower-row projection, and the
paper-`C'` lower-tail identity.  The older APIs remain compatibility wrappers.

This is finite lower-row paper-`C'` bookkeeping only.  It is not pivot-row
production, source production of `Csucc` or `C'^(S+1)`, suffix production,
successor chart-family construction, coverage/transition regularity, analytic
Jacobian data, normal crossings, pole order, or RLCT extraction.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-paper-cprime-lower-rows-without-chart-family-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-paper-cprime-lower-rows-without-chart-family.md`.
Review:
`threads/04-blow-up-certificate/review-case2-paper-cprime-lower-rows-without-chart-family-a4.md`
passed.

Latest A4 source-current stack chart-family-free directification:
`BlowupArithmetic.lean` now contains
`sourceChartMap_continuingOldTopSourceSuffixSuccFollowingBlock_withoutChartFamily`.
It proves the same finite source-current row stack wrapper as the old
`sourceChartMap_continuingOldTopSourceSuffixSuccFollowingBlock_withCorrectedPostData`
API, but without `ChartRegular`, `TransitionRegular`, or
`Case2ResidualBlockChartFamilyBoundary` arguments.  The proof destructs
`sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withoutChartFamily`,
preserves the next-center, corrected exponent/level/gap, recurrence-gap, and
finite center-principalization payloads, and rewrites only the two
following-factor stacks through the existing source-current row reindex
lemmas.  The older API remains a compatibility wrapper.

This is formula-level source-current row bookkeeping only.  It is not chart
production of the successor following block, not source production of `Csucc`
or `C'^(S+1)`, not suffix production, not successor chart-family construction,
not coverage/transition regularity, not coordinate-derived corrected
post-data, not analytic Jacobian data, not normal crossings, not pole order,
not termination, and not RLCT extraction.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-source-current-stack-without-chart-family-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-source-current-stack-without-chart-family.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-current-stack-without-chart-family-a4.md`
passed.

Latest A4 branchwise source-production re-audit:
`threads/04-blow-up-certificate/audit-case2-branchwise-successor-production-recheck-a4.md`
records the crash-recovered xhigh branch scout round.  Galileo checked the
continuing branch, Wegener checked actual-width stopping, and Epicurus checked
row-exhausted stopping.  The three reports agree that Aoyagi PDF pp. 19-22
support the displayed local `Q/P` algebra, formula-level transported
following rows, and finite supplied-boundary consumers, but not
successor/source production.

Controller decision: freeze A4 Case 2 source production at the supplied
obligation boundary.  The continuing branch keeps the stronger
`J+2 <= prefixMinNat n (S+1)` nonempty-next-center guard; actual-width
stopping collapses to original rows only because `n(S+1)=J+1` empties the
correction sum; row exhaustion alone gives transported rows and not original
old rows in wide-next cases.  No new Lean target should be named as source
production unless it builds an independent selected-entry atlas/transition
construction.

Latest recovery scout round after the VM crash: Franklin checked selected-entry
atlas/coverage, Chandrasekhar checked the A0 chart-certificate spine versus
A4 microcertificates, and Volta checked A2/A3.  All three returned freeze
verdicts for genuine source-moving Lean work: A4 global selected-entry atlas
coverage, A0 total-loss chart certificate production, and A2/A3 boundary
removal are not Lean-ready from the current source/policy state.  The only
small safe target from the round was an A0/A4 projection adapter, now proved
as
`Case2DisplayedContinuingA0ExponentCoordinateBridge.of_chartCertificate_coord_exponents`
with artifacts in
`threads/04-blow-up-certificate/reproduction-case2-chart-certificate-coordinate-adapter-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-chart-certificate-coordinate-adapter.md`.
It rewrites supplied equalities on `Cnc.lossExp` and
`Cnc.jacobianPriorExp` through `Cnc.exponentData`; it does not move the chart,
coverage, source-production, active-ratio lower-bound, chart-count, pole-order,
or RLCT boundary.

Latest A4 Case 2 source-chart frontier package API-hardening:
`BlowupArithmetic.lean` now contains
`sourceChartMap_frontierBoundaryPackages_withoutChartFamily`, together with
`sourceChartMap_postPivotNextSameStageProduct_withSourceFollowingFactorAndCorrectedPostData_withoutChartFamily`,
`sourceChartMap_continuingWeightedSourceFollowingPayload_withFiniteCenterIdeal_withoutChartFamily`,
and
`sourceChartMap_continuingWeightedSuccFollowingPayload_withFiniteCenterIdeal_withoutChartFamily`.
The package constructs the same
`SourceChartFrontierBoundaryPackages` implication bundle without requiring a
caller-supplied `ChartRegular`, `TransitionRegular`, or
`Case2ResidualBlockChartFamilyBoundary`.  Continuing fields are direct finite
displayed-pivot algebra plus corrected post-data and finite center
principalization.  Stopped fields retain the accepted branch-implication
meaning; the proof internally supplies the old abstract chart-family boundary
with `Case2ResidualBlockChartFamilyBoundary.exists_trivial`.
`SourceProductionObligation.of_formulaSuccessor_transportTerminalRows` now
consumes the chart-free package.

This is finite API hardening only.  It does not produce `Csucc` or
`C'^(S+1)`, produce suffixes, build chart coverage or transition regularity,
derive coordinate-produced corrected post-data, identify row-exhausted
transported rows with original rows, prove normal crossings, prove pole
order, prove termination, or extract an RLCT.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-frontier-boundary-packages-without-chart-family-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-frontier-boundary-packages-without-chart-family.md`.
Review:
`threads/04-blow-up-certificate/review-case2-frontier-boundary-packages-without-chart-family-a4.md`
passed.

Latest A6 supplied final assembly update: `Theorem2FinalAssembly.lean` now
contains `AoyagiTheorem2SuppliedFinalBoundary`.  The boundary packages
selected-width provenance `m = aoyagiSelectedReducedWidths H r C`, the A0
extraction hypothesis, and the finite exponent formula hypothesis.  Lean
projects selected-width provenance consequences and the
ceiling-data/average/expanded lambda formulas plus
`poleOrder = data.theorem2OrderFormula`; selected rank-width hypotheses and
the source selected-width inequality remain explicit auxiliary theorem inputs
where used.  This is still a supplied final socket only: it does not prove
selected cutpoint existence, rank-width hypotheses from the matrix problem,
normal-crossing chart production, finite exponent formula equalities, Lemma 5
no-extra coverage/order count, pole order without A0, or analytic extraction.
Artifacts:
`threads/06-dln-translation/reproduction-theorem2-final-assembly-a6.md`
and
`threads/06-dln-translation/statement-card-a6-theorem2-final-assembly.md`.
Review:
`threads/06-dln-translation/review-theorem2-final-assembly-a6.md`.

Latest A6 remaining-obligations boundary map:
`threads/06-dln-translation/boundary-map-theorem2-remaining-source-obligations-a6.md`
now records the exact source obligations still separating the supplied final
socket from a source-backed Theorem 2: selected cutpoint/Definition 3
provenance, normal-crossing certificate production, active-ratio lower bounds,
displayed-ratio chart counts, A4 source/chart production, A2
source-boundary/rank-stratum handling, supplied or corrected A5 terminal-order
data, and A3 avoidance or policy change.  The only planned citation remains
normal-crossing-to-RLCT extraction; do not silently cite Aoyagi Lemma 1,
Aoyagi Theorem 4, regular-coordinate additivity, A2 analytic transport, or
Lemma 5 no-extra coverage.

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
