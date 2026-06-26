# Frontier saturation audit - A2/A4/A5

Date: 2026-06-26.

Status: controller pen-and-paper/source audit with read-only xhigh scout
fan-out after commit `c6f75e14`.  No Lean theorem is proposed from this audit.

## Controller PDF Check

The controller rendered Aoyagi PDF pp. 24-27 from
`paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/aoyagi-2023-neural-networks-preprint.pdf`
and rechecked the Lemma 5 upper-count passage.

The relevant source shape is:

- Lemma 4 is one-way: bounds between the displayed lower and upper vectors,
  plus binary increments, imply that the vector corresponds to lambda.
- Lemma 5 bounds the number of vectors corresponding to lambda by summing the
  possible single-coordinate interval values.
- The sentence that `J` is increased by one in Case 1(2) records progress of
  the blow-up construction.  It is not an injectivity theorem for arbitrary
  Lean terminal-minimum labels.
- The displayed branch families (1)--(5) supply lower-bound examples, but not
  a back-to-label map for every terminal-minimum label and not a no-extra
  theorem.

Thus the printed Lemma 5 paragraph supports the interval-count codomain and
the existing conditional first-nonbase upper-bound theorem.  It does not
construct `TC.TerminalMinimumCountDatumClassifier`, selector injectivity,
`TerminalMinimumCountDatumBackToBranchLabel`, or
`TC.terminalMinimumLabels <= TC.branchLabelImage` at the current Lean-label
level.

## Xhigh Scouts

Three read-only xhigh scouts checked the live frontiers.

- A2 scout `Bacon the 3rd`: Aoyagi pp. 10-13 support the block substitution
  and product-difference algebra already formalised in `ProductReduction*`.
  They do not state a retained-passive multi-step source chart, source-rank
  coverage theorem, source-measure pushforward, or density/Jacobian transport.
- A4 scout `Boole the 3rd`: Aoyagi pp. 14-22 support the recursive product
  statement, selected chart substitutions, `Q/P` algebra, `C' = Q^{-1} C`,
  product identities, and continue/stop branch sentences.  They do not define
  analytic chart domains, chart tokens, open coverage, analytic overlap maps,
  analytic Jacobian/volume compatibility, produced suffix data, or a produced
  full successor.
- A5 scout `Leibniz the 3rd`: Aoyagi pp. 24-27 support the interval-count
  codomain shape.  They do not give a label-to-vector bridge, canonical
  terminal counted-datum selector, selector injectivity, back-to-label
  coverage, or no-extra terminal-minimum coverage.

## Saturated Finite Layers

The following finite layers are useful and should continue to be used as
conditional infrastructure, but they are saturated below the current source
frontier:

- A2 selected-entry residual readout wrappers and p.13 finite algebra
  consumers.  Do not add more variants unless a downstream theorem consumes
  the exact new statement.
- A4 finite selected-entry chart-map, all-pivot finite coverage, affine
  transition, selected-entry principalization/unit facts, and
  `SourceProductionObligation` formula constructors.  These are not analytic
  atlas fields.
- A5 counted-datum codomain, endpoint-family coverage, first-nonbase selector
  upper bound, Eq5 own-block classifier adapters, and branch-label injection
  adapters.  These are not source proofs of terminal-minimum exactness.

## Guardrails

Do not use any of the following as evidence for the named source/analytic
fields:

- `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exists_chartPoint_chartMap_eq_value`
  as analytic/open coverage.
- `SelectedEntryFiniteAffineTransitionRegularFamily` as analytic transition
  regularity.
- `SourceProductionObligation.of_formulaSuccessor_transportTerminalRows` or
  `SourceProductionObligation.of_constructedWithOldTopFromCprime_terminalStack`
  as source production.
- `terminalMinimumLabels_card_le_of_eq5EndpointChain_firstInteriorNonbase` as
  Lemma 5 exactness or no-extra coverage.
- `terminalMinimumLabelExactness_iff_branchLabel_injOn_and_card_bound` as a
  source proof of the card bound or branch-label injectivity.

## Remaining Real Construction Targets

The next progress must remove one of these fields by construction, not by
renaming it.

1. A2 retained-passive p.13 source chart:
   explicit source map, local inverse, source-rank coverage/image theorem,
   source-measure or product-measure pushforward, and density/Jacobian/prior
   accounting.  First Lean payoff: remove `hraw_map` in the raw-density
   consumer or `hcoverage` in the local-source integrability consumer.
2. A4 analytic selected-entry atlas:
   chart domains/tokens, chart maps as analytic or regular maps on those
   domains, source-neighborhood coverage, analytic overlap regularity,
   analytic Jacobian compatibility, produced successor/suffix data, and branch
   termination.  First Lean payoff: fill an actual field of
   `SelectedEntryAnalyticAtlasBoundary`.
3. A5 terminal no-extra/classifier theorem:
   a representation of every `TC.terminalMinimumLabels` label by an Aoyagi
   Lemma 5 vector satisfying the endpoint/binary-increment hypotheses, plus an
   injective counted-datum selector or a back-to-label/no-extra theorem.  First
   Lean payoff: remove `hinjFirst`, `hpAlpha_inj`, or the supplied
   `UpperBoundClassifier`/counted-datum classifier boundary.

## Controller Decision

Do not add another wrapper at A2/A4/A5 unless it eliminates one of the fields
listed above.  If no such construction is available in the next pass, the
right next work is to begin one of the construction packages explicitly, with
source-faithful definitions and a proof plan, rather than pushing the final
socket through more conditional payload records.
