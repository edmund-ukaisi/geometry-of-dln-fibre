# theorem-ledger.md - source to Lean dependency ledger

This table is controller memory. Every source theorem or lemma that can affect
the final statement gets one row. Keep source references page-pinned; avoid
holding PDF line numbers only in context.

| Source item | Local claim | Source ref | Dependencies | Reproduction/status | Lean target/status | Review/status |
|---|---|---|---|---|---|---|
| RLCT definition and normal-crossing extraction | A0 | PDF pp. 5-6 | external analytic theorem | scout report `threads/02-analytic-interface/scout-report.md`; interface draft `threads/02-analytic-interface/interface-draft.md`; A2 repair `threads/02-analytic-interface/interface-repair-a2.md` | extraction-only interface TBD after A4 certificate data; open/Cited | draft reviewed by controller; A2 repair excludes Lemma 1/additivity as separate citations; Lean shape pending |
| Theorem 1, cited three-layer formula | context/special case | PDF pp. 6-7 | prior result [12]; likely derivable from Theorem 2 at `L=2` | pending/optional | no Lean target yet | pending |
| Theorem 2 multi-layer main formula | A6 | PDF pp. 8-9 | A0-A5 | pending | final theorem TBD; open | pending |
| Lemma 2 block elimination | A1 | PDF pp. 10-11 | matrix rank/open block hypotheses | draft + partial check: `threads/03-block-product-reduction/reproduction-draft.md`, `threads/03-block-product-reduction/reproduction-check.md`; algebraic chart identities and rank formula checked | block identities and indexed variants plus `rank_fromBlocks_zero_zero` and `rank_fromBlocks_eq_card_add_rank_schurComplement_of_isUnit_det`; proved in `lean/DLNFibre/DLN/Aoyagi/BlockElimination.lean` | reviewed; statement cards `threads/03-block-product-reduction/statement-card-a1-block-identities.md`, `threads/03-block-product-reduction/statement-card-a1-rank-formula.md` |
| Theorem 3 product reduction | A2 | PDF pp. 11-13 | A1, product/block notation, through-layer open-chart/basis lemma, entry-ideal algebra, regular-suspension certificate | draft + failed full check plus repair reports: `threads/03-block-product-reduction/reproduction-draft.md`, `threads/03-block-product-reduction/reproduction-check.md`, `threads/03-block-product-reduction/reproduction-repair-a2.md`, `threads/03-block-product-reduction/through-layer-basis-reproduction.md`; full theorem not formalisation-ready; chart-local induction step reproduced; through-layer basis repair checked; finite chart-data construction rechecked; paper-order bridge notes `threads/03-block-product-reduction/paper-order-bridge-notes.md`; regular-suspension plan `threads/03-block-product-reduction/regular-suspension-plan.md` | partial sub-artifacts proved: `productReduction_chartLocalInductionStep_fromBlocks`, `productReduction_chartLocalInductionStep_fromBlocks_indexed`, `upperUnitriangular_mul_fromBlocks_one_zero`, `upperUnitriangular_mul_fromBlocks_one_zero_indexed`, `exists_fromBlocks_one_zero_of_upperUnitriangular_mul`, `exists_fromBlocks_one_zero_of_upperUnitriangular_mul_indexed`, `topLeftCorner`, `upperRightBlock`, `lowerRightBlock`, `identityCornerForm`, `identityCornerDetChart`, `identityCornerForm_upperUnitriangular_mul`, `productReduction_blockDiagonal_mul_fromBlocks_one_zero_rightElim_indexed`, `productReduction_blockDiagonal_mul_eq_fromBlocks_one_zero_rightElim_indexed`, `productReduction_blockDiagonal_mul_identityCornerForm_rightElim`, `productReduction_blockDiagonal_mul_identityCornerForm_rightElim_submatrix`, `productReduction_blockDiagonal_mul_unitriangular_identityCornerForm_rightElim`, `upperUnitriangular_neg_mul_upperUnitriangular`, `upperUnitriangular_neg_mul_upperUnitriangular_neg_neg`, `productReduction_identityCorner_suffixStep_rightElim`, and `productReduction_identityCorner_suffixChain_rightElim` in `lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`; matrix-entry ideal transport lemmas in `lean/DLNFibre/DLN/Aoyagi/EntryIdeal.lean`; through-layer subspace theorem `exists_chain_throughSubspaces`, restricted-edge equivalence `throughSubspaceEdgeEquiv`, paper-order composite `paperChainMap`, paper-order split theorem `paperChainMap_zero_last_eq_prefix_comp_suffix`, reversed vertex/edge definitions `reverseVertex` and `reverseEdge`, and reversal theorem `chainMap_reverse_eq_paper` in `lean/DLNFibre/DLN/Aoyagi/ThroughLayerBasis.lean`; per-edge transported quotient-basis theorem `exists_toMatrix_throughSubspaceEdge_eq_fromBlocks_one_zero`, direct-sum theorem `exists_toMatrix_throughSubspaceEdge_basisOfIsCompl_eq_fromBlocks_one_zero`, prefix-basis theorem `exists_toMatrix_throughSubspaceEdge_prefix_basisOfIsCompl_eq_fromBlocks_one_zero`, chart-data theorem `exists_unitriangular_toMatrix_throughSubspaceEdge_chartData_eq_fromBlocks_one_zero`, shared adapted-basis theorem `exists_toMatrix_throughSubspaceEdge_adaptedBasis_eq_fromBlocks_one_zero`, adapted matrix composition/reduction definitions/theorems `throughSubspaceAdaptedChainMapMatrix`, `throughSubspaceAdaptedChainMapMatrix_proof_irrel`, `throughSubspaceAdaptedChainMapMatrix_self`, `throughSubspaceAdaptedEdgeMatrix`, `throughSubspaceAdaptedChainMapMatrix_succ`, `throughSubspaceAdaptedChainMapMatrix_succ_right`, `throughSubspaceAdaptedEdgeProductMatrix`, `throughSubspaceAdaptedEdgeProductMatrix_self`, `throughSubspaceAdaptedEdgeProductMatrix_succ`, `throughSubspaceAdaptedChainMapMatrix_eq_edgeProductMatrix`, `throughSubspaceAdaptedChainMapMatrix_zero_eq_edgeProductMatrix`, `toMatrix_chainMap_zero_last_eq_adaptedEdgeProductMatrix`, `identityCornerForm_throughSubspaceAdaptedEdgeMatrix`, and `productReduction_throughSubspaceAdaptedChainMapMatrix_suffixChain_rightElim`, endpoint total-product theorems `toMatrix_chainMap_zero_last_ker_basisOfIsCompl_eq_fromBlocks_one_zero_zero` and `toMatrix_chainMap_zero_last_chartData_eq_fromBlocks_one_zero_zero_of_maps_complement_to_zero`, finite chart-data definitions `throughSubspaceComplement`, `throughSubspaceComplementIndex`, `throughSubspaceChartDataOfFiniteDimensional`, `throughSubspaceAdaptedBasis`, `throughSubspaceEndpointComplement`, `throughSubspaceEndpointComplementIndex`, and `throughSubspaceEndpointChartDataOfFiniteDimensional`, endpoint-compatible package theorems `toMatrix_chainMap_zero_last_endpointChartData_eq_fromBlocks_one_zero_zero` and `endpointChartData_edge_and_totalProduct_blocks`, nonempty/existence theorems `nonempty_throughSubspaceChartDataOfFiniteDimensional`, `nonempty_throughSubspaceEndpointChartDataOfFiniteDimensional`, `exists_isCompl_ker_throughSubspaceChartDataOfFiniteDimensional`, and `exists_isCompl_ker_throughSubspaceEndpointChartDataOfFiniteDimensional`, concrete finite-basis edge theorem `exists_toMatrix_throughSubspaceEdge_finiteDimensional_eq_fromBlocks_one_zero`, concrete finite-basis unitriangular theorem `exists_unitriangular_toMatrix_throughSubspaceEdge_finiteDimensional_eq_fromBlocks_one_zero`, paper-order disjointness bridge `disjoint_ker_reverse_total_of_disjoint_ker_paperChainMap`, paper-order complement bridge `isCompl_ker_reverse_total_of_isCompl_ker_paperChainMap`, paper-order finite edge theorem `exists_toMatrix_reverseEdge_finiteDimensional_eq_fromBlocks_one_zero`, paper-order finite unitriangular theorem `exists_unitriangular_toMatrix_reverseEdge_finiteDimensional_eq_fromBlocks_one_zero`, paper-order determinant-chart predicates for `paperAdaptedReverseEdgeMatrix` and its unitriangular transform, paper-order one-edge right-elimination theorem `productReduction_paperAdaptedReverseEdgeMatrix_rightElim`, paper-order endpoint theorem `toMatrix_paperChainMap_ker_finiteDimensional_eq_fromBlocks_one_zero_zero`, paper-order endpoint-compatible data theorem `exists_isCompl_ker_paperEndpointChartDataOfFiniteDimensional`, paper-order shared-basis package `paperEndpointChartData_edge_and_totalProduct_blocks`, and concrete finite-basis endpoint theorem `toMatrix_chainMap_zero_last_ker_finiteDimensional_eq_fromBlocks_one_zero_zero` in `lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`; paper-order endpoint reduction wrapper, topological open-neighborhood bridge, full theorem, and RLCT/certificate consequences blocked | xhigh reviews pass for chart-local theorem, entry-ideal lemmas, through-subspace theorem, quotient-basis through-matrix theorem, endpoint total-product theorem, prefix-compatible edge theorem, supplied chart-data bundle, reversed-chain bridge, one-edge right-elimination orientation/scope, endpoint-compatible chart-data shape, and adapted matrix composition/all-layer product orientation; xhigh recommendation incorporated for right-elimination assembly interface; xhigh suffix-chain review passed with source-fidelity warning; through-layer reproduction checked; statement cards `threads/03-block-product-reduction/statement-card-a2-chart-local-induction-step.md`, `threads/03-block-product-reduction/statement-card-a2-entry-ideal.md`, `threads/03-block-product-reduction/statement-card-a2-unitriangular-chart.md`, `threads/03-block-product-reduction/statement-card-a2-through-subspaces.md`, `threads/03-block-product-reduction/statement-card-a2-paper-chain.md`, `threads/03-block-product-reduction/statement-card-a2-paper-matrix-block.md`, `threads/03-block-product-reduction/statement-card-a2-one-edge-right-elim.md`, `threads/03-block-product-reduction/statement-card-a2-suffix-chain-right-elim.md`, `threads/03-block-product-reduction/statement-card-a2-endpoint-compatible-chart-data.md`, `threads/03-block-product-reduction/statement-card-a2-adapted-matrix-composition.md`, `threads/03-block-product-reduction/statement-card-a2-through-matrix-block.md`, `threads/03-block-product-reduction/statement-card-a2-chart-data-existence.md`, `threads/03-block-product-reduction/statement-card-a2-total-product-block.md`; full Theorem 3 review pending |
| Theorem 4 deepest singular point | A3 | PDF p. 14 | A2, analytic/global comparison | scout report: `threads/02-analytic-interface/scout-report.md`; scope conflict under current citation rule | no Lean target until restricted proof/avoidance chosen | pending |
| Blow-up inductive statement | A4 | PDF pp. 14-15 | reduced product coordinates | draft + failed check plus repair: `threads/04-blow-up-certificate/reproduction-draft.md`, `threads/04-blow-up-certificate/reproduction-check.md`, `threads/04-blow-up-certificate/reproduction-repair-a4.md`; source uses actual widths `M^{(s)}` and prefix minima `M(S)` simultaneously; page image also shows the inductive comparability range undercounts labels relative to the Jacobian ranges | actual-width vs prefix-width label API and introduced-label state bookkeeping proved in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`; invariant theorem TBD/blocked | failed check; xhigh source and pen-and-paper rechecks completed; statement cards `threads/04-blow-up-certificate/statement-card-a4-actual-width-labels.md`, `threads/04-blow-up-certificate/statement-card-a4-introduced-labels.md` |
| Blow-up Case 1 | A4 | PDF pp. 15-18 | reduced product coordinates, inductive statement | repair report corrects the row-strip center and exponent increments to use actual active column width `M^{(S+1)}-J`; selected-variable chart and displayed pivot chart are understood only locally; full pivot-chart family or permutation reduction still missing; `P` quotient divisibility reduced to recurrence arithmetic; normalized displayed `Q/P` matrix identities checked; tail-lowering exponent increment checked under explicit flat-tail hypothesis; one-label lower-tail certificate transformer requires old least value `J+J1` and `J<=J+J1`; Case 1 center generator set records chosen old generator plus actual-width row strip but does not encode old-label hypotheses; row-strip containment requires explicit bound `J+J1<=mu_S`; first-jump package now records the strict nonterminal boundary `J+J1<mu_S`, selected introduced label, level gap, and componentwise minimality but not `b` recurrence semantics; same-domain lower-tail update assumes `leastValue=level`, flat-tail, selected post-data, and unchanged non-selected labels; selected-label update-data helpers are total assignment overrides only; level/tail bridge assumes `leastValue=level` for introduced labels and flat-tail only above pivot; selected-old erased-base and concrete level-move recurrence checkpoints are now reproduced | monomial recurrence divisibility, normalized `Q` column-operation identities, normalized `P` row-operation identity, combined local normalized pivot-step identities, Case 1 tail-lowering terminal-exponent increment, lower-tail finite minimum facts, one-label lower-tail certificate transformer, finite Case 1 center generator bookkeeping, row-strip residual-block containment, Case 1 first-jump selected-label hypothesis package, conditional same-domain Case 1 lower-tail certificate update, selected-label update-data helper theorem, conditional level/tail invariant bridge, Case 1 chart-family boundary names, displayed top-left source-order adapter, selected-old erased-base recurrence model, and selected-old concrete level-move state proved in `BlowupArithmetic.lean`; transition lemma TBD/blocked | repair note updated; statement cards `threads/04-blow-up-certificate/statement-card-a4-monomial-recurrence-divisibility.md`, `threads/04-blow-up-certificate/statement-card-a4-normalized-p-row-operation.md`, `threads/04-blow-up-certificate/statement-card-a4-normalized-q-operation.md`, `threads/04-blow-up-certificate/statement-card-a4-normalized-pivot-step.md`, `threads/04-blow-up-certificate/statement-card-a4-case1-tail-exponent-increment.md`, `threads/04-blow-up-certificate/statement-card-a4-case1-center-generators.md`, `threads/04-blow-up-certificate/statement-card-a4-case1-row-strip-containment.md`, `threads/04-blow-up-certificate/statement-card-a4-case1-first-jump-hypotheses.md`, `threads/04-blow-up-certificate/statement-card-a4-case1-same-domain-lower-tail-update.md`, `threads/04-blow-up-certificate/statement-card-a4-selected-label-update-data.md`, `threads/04-blow-up-certificate/statement-card-a4-level-tail-invariant-bridge.md`, `threads/04-blow-up-certificate/statement-card-a4-case1-chart-family-boundary.md`, `threads/04-blow-up-certificate/statement-card-a4-displayed-top-left-source-order-adapter.md`, `threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-erased-base-source-model.md`, `threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-concrete-level-move.md` |
| Blow-up Case 2 | A4 | PDF pp. 19-22 | reduced product coordinates, inductive statement | page image confirms the printed vector `t_{S,J+1}^{(i)}=M^{(i+1)}` for `i<S` and printed increment `(M(S)-J)(M^{(S+1)}-J)`; substituting that printed vector into the terminal formula gives `(M^{(S)}-J)(M^{(S+1)}-J)` unless `M(S)=M^{(S)}`; the prefix-minimum vector repairs the arithmetic but is a corrected certificate, not printed source data; pivot charts, full polynomial-coordinate chart construction, `b'_i`/standalone-`u` bookkeeping, termination, and boundary cases remain unresolved; normalized displayed `Q/P` matrix identities are independent of this mismatch | arithmetic split, monomial recurrence divisibility, normalized `Q/P` identities, combined local normalized pivot-step identity, corrected Case 2 vector minimum certificate, one-label corrected Case 2 new-label certificate, finite exponent-domain bookkeeping, Case 2 residual-block entry set, selected-entry substitution scaffold, displayed pivot-first following-factor package, displayed source-substitution factorisation, transported following-factor name, row-index monomial-recurrence `Q/P` wrapper, source-block tail-lift wrappers, conditional recurrence-gap row-weight bridge, conditional finite label-product gap bridge, conditional introduced-label finite-domain gap bridge, conditional recurrence-state interface, arbitrary selected-pivot recurrence handoff, source-selected pair wrappers, supplied source-selected pivot boundary, displayed concrete-update boundary, selected-entry principalization/unit facts, Case 2 chart-family boundary names, and displayed top-left source-order adapter proved in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`; no source-faithful or corrected transition theorem accepted | xhigh rechecks confirm printed-vector mismatch/source gap, recurrence-divisibility reduction, normalized matrix algebra, one-label certificate scope, exponent-domain bookkeeping scope, residual-block entry bounds, selected-entry substitution scope, displayed source-substitution factor scope, row-index recurrence wrapper scope, source-block tail-lift scope, recurrence-gap row-weight bridge scope, finite label-product gap scope, introduced-label finite-domain bridge scope, recurrence-state interface scope, arbitrary selected recurrence handoff scope, source-selected pair wrapper scope, selected-entry principalization/unit scope, Case 2 chart-family boundary scope, displayed top-left source-order adapter scope, supplied source-selected pivot boundary scope, and displayed concrete-update boundary scope; statement cards `threads/04-blow-up-certificate/statement-card-a4-terminal-exponent-split.md`, `threads/04-blow-up-certificate/statement-card-a4-monomial-recurrence-divisibility.md`, `threads/04-blow-up-certificate/statement-card-a4-normalized-p-row-operation.md`, `threads/04-blow-up-certificate/statement-card-a4-normalized-q-operation.md`, `threads/04-blow-up-certificate/statement-card-a4-normalized-pivot-step.md`, `threads/04-blow-up-certificate/statement-card-a4-corrected-case2-vector-minimum.md`, `threads/04-blow-up-certificate/statement-card-a4-corrected-case2-new-label-certificate.md`, `threads/04-blow-up-certificate/statement-card-a4-finite-exponent-domain-bookkeeping.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-residual-block-entries.md`, `threads/04-blow-up-certificate/statement-card-a4-selected-entry-substitution.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-pivot-first-following-factor.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-source-substitution-factor.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-transported-following-factor-monomial.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-source-block-tail-lift.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-gap-row-weights.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-label-product-gap.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-introduced-label-gap.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-recurrence-state-interface.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-arbitrary-selected-recurrence-handoff.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-source-selected-pair-wrapper.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-supplied-source-selected-pivot-boundary.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-displayed-concrete-update-boundary.md`, `threads/04-blow-up-certificate/statement-card-a4-selected-entry-principalization-unit-facts.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-chart-family-boundary.md`, `threads/04-blow-up-certificate/statement-card-a4-displayed-top-left-source-order-adapter.md`; review artifacts `threads/04-blow-up-certificate/review-case2-supplied-source-selected-pivot-boundary-a4.md`, `threads/04-blow-up-certificate/review-case2-displayed-concrete-update-boundary-a4.md` |
| Terminal normal-crossing exponents | A4 | PDF p. 22 | Case 1/2 induction | page image confirms the terminal diagonal length is `M(L+1)` prefix minimum while the exponent formula uses actual widths `M^{(j)}`; terminal formula cannot be accepted as reproduced until Case 2 is split into printed mismatch and corrected certificate | terminal expression and prefix-step arithmetic proved in `BlowupArithmetic.lean`; full certificate theorem TBD/blocked | xhigh rechecks confirm split; statement card `threads/04-blow-up-certificate/statement-card-a4-terminal-exponent-split.md` |
| Quadratic exponent expression | A5 | PDF pp. 22-24 | terminal exponents | draft reproduction + failed check: promising algebra but candidate minimum must keep `\tilde t=0` restriction and feasibility hypotheses | arithmetic theorem TBD; blocked | failed check |
| Lemma 3 minimisation | A5 | PDF p. 24 | exponent vector definitions | draft reproduction + failed check: interior calculation mostly reproducible; endpoint split for `a=0`/`a=ell` required | endpoint arithmetic lemma TBD; blocked | failed check |
| Lemma 4 pole/order comparison | A5 | PDF p. 25 | Lemma 3 | draft reproduction + failed check: depends on fixed Lemma 3 and explicit `H_0`/`F_1` convention | arithmetic theorem TBD; blocked | failed check |
| Lemma 5 final order count | A5 | PDF pp. 25-27 | Lemmas 3-4 | draft reproduction + failed check: chart-family admissibility, coverage, exclusions, and exact equal-minimum count not reproduced | order-count theorem TBD; blocked | failed check |
| Notation translation to repo DLN dimensions | A6 | Aoyagi PDF pp. 8-9 | source inventory | pending | translation theorem TBD; open | pending |

## Latest A2 update

The A2 table row above was originally written before the endpoint packaging
wrapper landed. As of the current checkpoint,
`productReduction_paperChainMap_endpointChartData_suffixChain_rightElim` is
proved in `lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`; its statement
card is
`threads/03-block-product-reduction/statement-card-a2-paper-endpoint-suffix-chain-right-elim.md`.
Xhigh statement-shape review confirms the reversal orientation and the
pointwise adapted-coordinate scope.
The remaining blocked A2 items are the topological rank/open-neighborhood
bridge, a source-faithful full Theorem 3 statement, and analytic/certificate
transport.

Second latest A2 update: the first rank/open split has landed. Proved Lean
theorems are `rank_toMatrix_eq_finrank_range`,
`rank_schurComplement_eq_sub_rank_fromBlocks`,
`lowerRightBlock_paperAdaptedReverseEdgeMatrix_rank_eq_sub`, and the
`ChartTopology.lean` determinant-chart openness/neighborhood theorems. Statement
cards:
`threads/03-block-product-reduction/statement-card-a2-residual-rank-bridge.md`
and
`threads/03-block-product-reduction/statement-card-a2-determinant-chart-topology.md`.
Remaining blocked A2 items are fixed basepoint chart data for nearby variable
layers, source-faithful exact rank-stratum packaging, the full Theorem 3
statement, and analytic/certificate transport.

Third latest A2 update: the endpoint fixed-chain basepoint certificate has
landed in `lean/DLNFibre/DLN/Aoyagi/BasepointCertificate.lean`. Proved Lean
objects/theorems include `paperTotalMap`, `paperEndpointChartData`,
`paperEndpointAdaptedEdgeMatrix`, `paperEndpointUnitriangularLeft`,
`paperEndpointAdaptedTotalMatrix`,
`lowerRightBlock_throughSubspaceEndpointAdaptedEdgeMatrix_rank_eq_sub`,
`lowerRightBlock_paperEndpointAdaptedEdgeMatrix_rank_eq_sub`,
`paperEndpointAdaptedTotalMatrix_eq_fromBlocks_one_zero_zero`,
`productReduction_paperEndpointAdaptedTotalMatrix_suffixChain_rightElim`,
`PaperEndpointBasepointCertificate`,
`paperEndpointBasepointCertificate_of_isCompl`, and
`exists_paperEndpointBasepointCertificate`. Statement card:
`threads/03-block-product-reduction/statement-card-a2-basepoint-certificate.md`.
Remaining blocked A2 items are fixed coordinate families for variable nearby
chains, source-faithful exact rank-stratum packaging, the full Theorem 3
statement, and analytic/certificate transport.

Fourth latest A2 update: the fixed-basepoint variable-chain layer has landed.
Generic block API in `ProductReduction.lean`: `lowerLeftBlock`,
`fromBlocks_corners`, `schurResidualBlock`, and
`rank_schurResidualBlock_eq_sub_rank_of_identityCornerDetChart`. Fixed-base
paper wrappers in `lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean`:
`paperEndpointFixedBaseBasis`, `paperEndpointFixedBaseChainMapMatrix`,
`paperEndpointFixedBaseEdgeMatrix`, `paperEndpointFixedBaseTotalMatrix`,
`paperEndpointFixedBaseChainMapMatrix_succ_right`,
`paperEndpointFixedBaseTotalMatrix_eq_chainMapMatrix`,
`paperEndpointFixedBaseEdgeMatrix_selfBase`,
`paperEndpointFixedBaseTotalMatrix_selfBase`,
`rank_schurResidualBlock_paperEndpointFixedBaseEdgeMatrix_eq_sub`, and
`paperEndpointFixedBaseTwoEdgeTotalMatrix_eq_edge1_mul_edge0`. Statement card:
`threads/03-block-product-reduction/statement-card-a2-fixed-basepoint-chart.md`.
Remaining blocked A2 items are the iterated chart-local product reduction in
fixed bases, fixed-coordinate determinant-neighborhood packaging for variable
chains, source-faithful exact rank-stratum packaging, the full Theorem 3
statement, and analytic/certificate transport.

Fifth latest A2 update: the first fixed-base variable-chart suffix step has
landed. Generic theorem:
`productReduction_chartLocal_suffixStep_fromBlocks_indexed` in
`ProductReduction.lean`; fixed-base wrapper:
`paperEndpointFixedBase_chartLocal_suffixStep` in
`FixedBasepointChart.lean`; supporting rank bridge:
`rank_paperEndpointFixedBaseEdgeMatrix_eq_finrank_range` and
`rank_schurResidualBlock_paperEndpointFixedBaseEdgeMatrix_eq_range_sub`.
The statement card
`threads/03-block-product-reduction/statement-card-a2-fixed-basepoint-chart.md`
was updated.

Sixth latest A2 update: the all-layer explicit-chart suffix-chain induction has
landed. Generic theorem:
`productReduction_chartLocal_suffixChain_blockDiagonal_indexed` in
`ProductReduction.lean`; fixed-base wrapper:
`productReduction_paperEndpointFixedBaseChainMapMatrix_chartLocal_blockDiagonal`
in `FixedBasepointChart.lean`, supported by
`paperEndpointFixedBaseChainMapMatrix_proof_irrel`. At that checkpoint the next
blocked item was fixed-coordinate determinant-neighborhood packaging for
variable chains, followed by exact rank-stratum packaging, the full Theorem 3
statement, and analytic/certificate transport.

Seventh latest A2 update: the matrix-local transformed determinant-neighborhood
package has landed. Generic topology helpers:
`leftMul_identityCornerDetChart_mem_nhds` and
`fromBlocks_leftMul_identityCornerDetChart_mem_nhds` in `ChartTopology.lean`;
fixed-base wrapper:
`paperEndpointFixedBaseEdgeMatrix_selfBase_mem_nhds_transformed_identityCornerDetChart`
in `FixedBasepointChart.lean`. The theorem is pointwise in a fixed edge `p` and
fixed accumulated block `Bprev`; it does not assert a single neighborhood
working for all `Bprev`. Remaining blocked A2 items are pulling these
matrix-space neighborhoods back along a formal topology/continuity statement
for fixed-coordinate variable chains, source-faithful exact rank-stratum
packaging, the full Theorem 3 statement, and analytic/certificate transport.

Eighth latest A2 update: the single-edge continuous-linear-map pullback has
landed. Generic theorem `continuous_linearMap_toMatrix` in `ChartTopology.lean`
proves continuity of fixed-basis matrix coordinates on `E →L[K] F`; fixed-base
wrapper
`paperEndpointFixedBaseContinuousEdge_selfBase_mem_nhds_transformed_identityCornerDetChart`
in `FixedBasepointChart.lean` pulls the transformed determinant chart back to a
neighborhood of the base edge in the continuous-linear-map topology. Remaining
blocked A2 items are product/chain-neighborhood assembly beyond a fixed
prescribed edge-family chart datum, source-faithful exact rank-stratum
packaging, the full Theorem 3 statement, and analytic/certificate transport.

Ninth latest A2 update: finite product-topology assembly for fixed transformed
edge charts has landed. Fixed-base wrapper
`paperEndpointFixedBaseContinuousEdges_selfBase_mem_nhds_transformed_identityCornerDetChart`
in `FixedBasepointChart.lean` says that, for a prescribed family of accumulated
upper blocks `Bprev p`, all transformed determinant-chart predicates hold on a
neighborhood of the base continuous reversed-edge family. This uses only finite
intersection/Pi-topology assembly from the one-edge theorem. It does not assert
a neighborhood working for all `Bprev`, does not connect to the
induction-produced `Bprev`, does not make exact rank strata open, and does not
prove Aoyagi Theorem 3.

Tenth latest A2 update: the variable-`Bprev` continuity handoff has landed.
Fixed-base wrapper
`paperEndpointFixedBaseContinuousEdges_variableBprev_mem_nhds_transformed_identityCornerDetChart`
in `FixedBasepointChart.lean` says that if a parameterized continuous
reversed-edge family and a parameterized accumulated-upper-block family `Bprev`
are continuous at `x0`, and all transformed determinant charts hold at `x0`,
then they hold in a neighborhood of `x0`. This is not a construction of the
recursive `Bprev`; pen-and-paper reproduction identifies the next algebraic
target as the deterministic update
`Bnext = (topLeftCorner ([I Bprev; 0 I] * E p))⁻¹ *
upperRightBlock ([I Bprev; 0 I] * E p)` under recursive chart hypotheses.

Eleventh latest A2 update: the deterministic one-step suffix state has landed.
`ChartLocalSuffixState` packages the current chart-local suffix data, while
`ChartLocalSuffixState.transformedEdge`, `ChartLocalSuffixState.step`, and
`ChartLocalSuffixState.step_blockDiagonal` in `ProductReduction.lean` formalize
the recurrence that was hidden inside the existential suffix-chain proof. The
step theorem proves preservation of the block-diagonal invariant under the
recursive determinant-chart hypothesis for the transformed edge. It does not
yet define or prove the full recursive suffix-chain state from `j` down to `i`.

Twelfth latest A2 update: the deterministic recursive suffix state has landed.
`ChartLocalSuffixState.terminal`, `ChartLocalSuffixState.suffixState`,
`ChartLocalSuffixState.suffixState_self`,
`ChartLocalSuffixState.terminal_blockDiagonal`,
`ChartLocalSuffixState.suffixState_castSucc`, and
`ChartLocalSuffixState.suffixState_blockDiagonal` now define the state obtained
by iterating the one-step recurrence downward and prove the recursive
block-diagonal invariant under recursive determinant-chart hypotheses. The
older public theorem `productReduction_chartLocal_suffixChain_blockDiagonal_indexed`
is now a wrapper extracting its witnesses from this deterministic state. This
is still algebraic: continuity of the recursive state and source-faithful chart
neighborhoods remain open.

Thirteenth latest A2 update: the recursive `Bprev` topology handoff has landed.
`continuousAt_matrix_inv_of_isUnit_det`,
`continuousAt_chartLocalSuffixState_step_B`, and
`continuousAt_chartLocalSuffixState_suffixState_B` in `ChartTopology.lean`
prove continuity of the accumulated upper block produced by the deterministic
suffix recursion, under recursive basepoint determinant-chart hypotheses. The
fixed-base theorem
`paperEndpointFixedBaseContinuousEdges_recursiveBprev_mem_nhds_transformed_identityCornerDetChart`
in `FixedBasepointChart.lean` feeds that actual recursive `Bprev` family into
the existing variable-`Bprev` chart-neighborhood handoff. This remains a chart
neighborhood theorem under supplied basepoint chart hypotheses; exact-rank
neighborhoods, certificate transport, and the full source Theorem 3 statement
remain open.

Fourteenth latest A2 update: the endpoint block-diagonal neighborhood handoff
has landed. `FixedBasepointChart.lean` now includes fixed-base coordinate
wrappers for arbitrary reversed edge families,
`paperEndpointFixedBaseChainMapMatrixOfReverseEdges`,
`paperEndpointFixedBaseEdgeMatrixOfReverseEdges`, and
`paperEndpointFixedBaseTotalMatrixOfReverseEdges`. The theorem
`paperEndpointFixedBaseChainMapMatrixOfReverseEdges_recursiveChart_blockDiagonal`
applies `ChartLocalSuffixState.suffixState_blockDiagonal` directly at the
endpoint, using only the recursive determinant charts actually visited by the
suffix recursion. The topology wrappers
`paperEndpointFixedBaseContinuousEdgesRecursiveBlockDiagonal`,
`paperEndpointFixedBaseContinuousEdges_recursiveBprev_blockDiagonal_mem_nhds`,
and
`paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_blockDiagonal_mem_nhds`
then say that a continuous reversed-edge family based at `reverseEdge W B` has
a neighborhood on which the endpoint product has the deterministic block form
in endpoint bases fixed from `B`. This still does not prove exact-rank
neighborhoods, certificate transport, or the full source Theorem 3 statement.

Fifteenth latest A2 update: a small residual-rank and `D` recurrence API has
landed. `ChartLocalSuffixState.residualBlock`,
`ChartLocalSuffixState.suffixState_D_self`, and
`ChartLocalSuffixState.suffixState_D_castSucc` in `ProductReduction.lean` name
the Schur residual block actually visited by the recursive suffix state and the
recurrence `D_next = D_tail * residualBlock`; this is an adapted residual
recurrence, not a product of raw edge residuals. In `FixedBasepointChart.lean`,
`rank_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_eq_finrank_range` and the
transformed residual-rank wrappers prove pointwise rank formulas for arbitrary
reversed edge families under explicit determinant-chart and exact-rank
hypotheses. These theorems do not assert that exact-rank conditions hold in a
neighborhood. The follow-on theorem
`paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_blockDiagonal_rankImp_mem_nhds`
packages the honest neighborhood boundary: recursive charts and endpoint block
form hold nearby, and transformed residual-rank conclusions are available
nearby as implications from exact pointwise edge ranks.

Sixteenth latest A2 update: the source-facing elementary product-reduction
boundary has landed in `lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`.
`PaperEndpointFixedBaseProductReductionCertificate` packages the three proved
fixed-base fields: recursive determinant charts, deterministic endpoint block
form, and residual-rank implications. The local certificate
`PaperEndpointFixedBaseProductReductionLocalCertificate` adds the basepoint
certificate and the neighborhood membership, and
`exists_paperEndpointProductReductionLocalCertificate` chooses a total-kernel
complement for a continuous reversed-edge family based at `B`. This remains an
elementary/topological A2 boundary only: no exact-rank openness, no analytic
ideal-germ transport, no regular-suspension/RLCT additivity, and no
normal-crossing extraction is included.

## Latest A4 update

The arbitrary selected-entry center facts have landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
`case2_selectedEntryChartMap_value_mem_of_mem`,
`case2_selectedEntryChartMap_center_dvd_of_mem`,
`case1_selectedEntryChartMap_value_mem_of_mem`, and
`case1_selectedEntryChartMap_center_dvd_of_mem`. They specialize the finite
map `selectedEntryChartMap` to arbitrary selected entries/generators already
known to belong to the Case 2 residual-block center or Case 1 center. The
result is only chart-index bookkeeping: `u` occurs in the finite substitution
value set, witnessed by the selected pivot, and all transformed finite-center
generators are divisible by `u`. It does not prove an affine blow-up atlas,
chart coverage, non-displayed transition formulas, row/column permutation
symmetry, regularity/Jacobian facts, exponent updates, termination,
normal-crossing certificates, or RLCT extraction.

Second latest A4 update: the generic pivot-first `Q/P` algebra bridge has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean names
include `pivotComplement`, `pivotFirstIndexEquiv`, `pivotFirstMatrix`,
`pivotFirstX`, `pivotFirstY`, `pivotFirstD`,
`pivotFirstMatrix_eq_pivotPreQBlock`,
`weightedPivotBlockRowOp_mul_diagonal_mul_pivotFirstMatrix_mul_pivotQ`, and
`weightedPivotBlockRowOp_mul_diagonal_mul_pivotFirstMatrix_mul`. This is not a
source reproduction of arbitrary non-displayed pivot charts. It proves only
that a matrix with selected pivot entry `1` can be put in the existing
normalised top-left block shape and that the existing `Q/P` identities apply
under explicit quotient witnesses `forall i, b i = q i * b0`, with the
following factor and weights already in pivot-first coordinates.

Third latest A4 update: generic pivot-row quotient witnesses have landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean names include
`exists_right_quotients_of_forall_dvd`,
`exists_right_quotients_of_forall_eq`,
`exists_right_quotients_of_forall_eq_or_dvd`,
`monomialRec_tail_eq_right_mul`,
`exists_right_quotients_monomialRec_of_le`,
`exists_right_quotients_monomialRec_of_eq_or_le`,
`exists_right_quotients_pivotMul_monomialRec_of_le`,
`exists_right_quotients_pivotMul_monomialRec_of_eq_or_le`,
`exists_right_quotients_const`, and
`exists_weightedPivotBlockRowOp_mul_diagonal_mul_of_forall_dvd`. These are
generic algebraic witnesses for the `P` matrix quotient hypothesis, not
Aoyagi-specific chart construction or transition data.

Fourth latest A4 update: pivot-first existential `Q/P` wrappers have landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean names include
`exists_pivotFirstQP_mul_pivotQ_of_forall_dvd`,
`exists_pivotFirstQP_mul_pivotQ_of_monomialRec_eq_or_le`,
`exists_pivotFirstQP_mul_pivotQ_of_pivotMul_monomialRec_eq_or_le`,
`exists_pivotFirstQP_mul_of_forall_dvd`,
`exists_pivotFirstQP_mul_of_monomialRec_eq_or_le`,
`exists_pivotFirstQP_mul_of_pivotMul_monomialRec_eq_or_le`,
`Case1FirstJumpHypotheses.displayedPivot_mem_center_of_colBound`,
`Case1FirstJumpHypotheses.displayedPivot_mem_residualBlockPivotEntries_of_colBound`,
and `Case1FirstJumpHypotheses.stripEntry_mem_residualBlockPivotEntries`.
These theorems choose the `q` witnesses needed by the pivot-first `Q/P`
identities from divisibility or recurrence hypotheses. They still assume
normalised pivot-first coordinates and do not prove Aoyagi selected-entry chart
construction, coordinate/weight transport, arbitrary row hypotheses, chart
coverage, exponent updates, or transition invariants. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-pivot-first-existential-q-p.md`.

Fifth latest A4 update: the source-displayed Case 2 top-left pivot `Q/P`
instantiation has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.
Proved Lean names include `Case2ResidualRowIndex`,
`Case2ResidualColIndex`, `case2DisplayedPivotRow`,
`case2DisplayedPivotCol`, `selectedEntryNormalizedMap`,
`selectedEntrySubstitutionMatrix`, `selectedEntryNormalizedMatrix`, and
`exists_case2DisplayedQP_mul_of_flat_weights`. This checkpoint packages the
displayed pivot row/column under the continuation bound, splits the
selected-entry substitution as `u` times a normalised matrix with pivot entry
`1`, and applies the pivot-first product `Q/P` identity under flat displayed
row weights. It does not prove arbitrary selected-entry charts, atlas
coverage, full coordinate/weight transport, exponent updates, or transition
invariants. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-pivot-q-p.md`.

Sixth latest A4 update: pivot-first following-factor transport has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean names are
`pivotFirstFollowingFactor` and
`pivotFirstMatrix_mul_pivotFirstFollowingFactor`. These prove that the
following factor reindexed by `pivotFirstIndexEquiv colPivot` multiplies with
the pivot-first residual block to give the pre-reindexed product reindexed by
`pivotFirstIndexEquiv rowPivot`. This is finite matrix reindexing only; it
does not prove source coordinate construction, regularity, chart coverage,
exponent updates, or transition invariants. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-pivot-first-following-factor.md`.

Seventh latest A4 update: pivot-first diagonal row-weight transport has landed
in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean name is
`weightedPivotDiagonal_eq_pivotFirst_diagonal`. It identifies the split
diagonal matrix used by the pivot-first `P` operation with the original
diagonal row-weight matrix reindexed by `pivotFirstIndexEquiv` on rows and
columns. This is finite matrix reindexing only; it does not prove source
row-weight assignment, recurrence flatness, quotient witnesses, chart coverage,
exponent updates, or transition invariants. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-pivot-first-diagonal-weights.md`.

Eighth latest A4 update: the displayed Case 2 pivot-first following-factor
package has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.
Proved Lean names include `case2DisplayedNormalizedMatrix`,
`case2DisplayedFollowingFactor`,
`case2DisplayedNormalizedMatrix_mul_followingFactor`, and
`exists_case2DisplayedQP_mul_pivotFirstFollowingFactor_of_flat_weights`.
These package the displayed normalised residual block and a residual following
factor supplied before pivot-first reindexing, reindex that factor into
pivot-first column coordinates, and apply the displayed flat-row-weight `Q/P`
theorem. This is local finite algebra only; it does not prove source-coordinate
construction, arbitrary-pivot coverage, regularity, exponent updates, or
transition invariants. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-pivot-first-following-factor.md`.

Ninth latest A4 update: the displayed Case 2 source-substitution factorisation
has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean
names include `diagonal_mul_selectedEntrySubstitutionMatrix`,
`pivotFirst_diagonal_mul_selectedEntrySubstitutionMatrix`,
`case2DisplayedSubstitutionMatrix`,
`case2DisplayedSubstitutionMatrix_eq_mul_normalized`,
`case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst`,
`case2Displayed_diagonal_mul_substitutionMatrix_mul_followingFactor`, and
`exists_case2DisplayedQP_mul_sourceSubstitution_of_flat_weights`. These prove
that, in the displayed selected-entry chart, `diag(weight)` times the
source-substituted residual block equals the normalised residual block with
row weights updated to `u * weight`, including pivot-first and following-factor
forms. This counts the selected variable once; it does not prove the full
source blockdiag identity, chart regularity/Jacobian, arbitrary-pivot coverage,
exponent updates, or transition invariants. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-substitution-factor.md`.

Tenth latest A4 update: the displayed Case 2 transported following-factor and
row-index monomial-recurrence wrapper have landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean names include
`case2ResidualRowLevel`, `case2ResidualRowLevel_ge`,
`case2ResidualRowLevel_displayedPivotRow`,
`case2DisplayedTransportedFollowingFactor`, and
`exists_case2DisplayedQP_mul_transportedFollowingFactor_of_rowIndex_monomialRec`.
These name the displayed `Q^{-1}C` following-factor update and instantiate the
pivot-first `Q/P` identity when updated row weights are
`u * monomialRec step rowLevel`; quotient witnesses come from the residual-row
bound `J+1 <= rowLevel`. This does not prove that Aoyagi's recursive state
produces those row weights, nor chart regularity, arbitrary-pivot coverage,
exponent updates, or transition invariants. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-transported-following-factor-monomial.md`.

Latest A4 update: the displayed Case 2 finite label-product gap bridge has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean names
include `levelProductStep`, `levelProductStep_eq_one_of_forall_ne`,
`levelProductStep_eq_one_of_gap`,
`case2ResidualRow_levelProduct_monomialRec_eq_pivot_of_gap`, and
`exists_case2DisplayedQP_mul_sourceSubstitution_of_labelGap`. These prove that
if the recurrence factor at level `r` is the product over a supplied finite
label set with `level=r`, and no supplied label has level in `J+1..mu_S-1`,
then the recurrence factors in that interval are `1` and the displayed Case 2
source-substitution `Q/P` wrapper applies. This does not prove that the supplied
labels are Aoyagi's actual introduced labels, nor that the recursive invariant
establishes the gap. The residual rows are `J+1..mu_S`, the residual columns are
actual-width `J+1..n_(S+1)`, and the selected variable is counted once in the
updated weights `u*b_i`. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-label-product-gap.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-label-product-gap-a4.md`.

Latest A4 update: the displayed Case 2 introduced-label finite-domain bridge has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean names
include `actualWidthLabelFinset`, `mem_actualWidthLabelFinset`,
`introducedLabelFinset`, `mem_introducedLabelFinset`,
`levelProductStep_introducedLabelFinset_eq_one_of_gap`,
`case2ResidualRow_introducedLabel_monomialRec_eq_pivot_of_gap`, and
`exists_case2DisplayedQP_mul_sourceSubstitution_of_introducedLabelGap`. These
instantiate the finite label-product Case 2 row-weight bridge over Lean's
introduced-label predicate. This removes the arbitrary supplied-label domain,
but still assumes the Nat-valued `level` map is Aoyagi's current `tilde_t`, the
variable map is the source recurrence variable assignment, the introduced-label
gap holds, and row weights are generated by this recurrence. It does not prove
the recursive invariant, the source's Case 2 comparability sentence,
arbitrary-pivot chart coverage, chart regularity/Jacobian facts, exponent
updates, transition invariants, termination, normal crossings, RLCT extraction,
or the printed Case 2 vector repair. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-introduced-label-gap.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-introduced-label-gap-a4.md`.

Latest A4 update: the displayed Case 2 recurrence-state interface has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean names include
`IntroducedLabelRecurrenceState`, `IntroducedLabelLevelInvariants`,
`case2IntroducedLabelLeastValueGap`,
`IntroducedLabelRecurrenceState.case2Gap`,
`IntroducedLabelRecurrenceState.case2Gap_of_leastValueGap`,
`IntroducedLabelRecurrenceState.step`, `IntroducedLabelRecurrenceState.weight`,
`IntroducedLabelRecurrenceState.case2ResidualRowWeight`,
`IntroducedLabelRecurrenceState.step_eq_one_of_case2Gap`,
`IntroducedLabelRecurrenceState.case2ResidualRow_weight_eq_pivot_of_case2Gap`,
`IntroducedLabelRecurrenceState.case2ResidualRowWeight_eq_pivot_of_case2Gap`,
`IntroducedLabelRecurrenceState.case2ResidualRowWeight_eq_displayedPivot_of_case2Gap`,
and `exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap`.
This packages the introduced-label recurrence data while keeping `step` and
row weights derived from `level`, `var`, and `introducedLabelFinset`. It bridges
integer least-value gaps to Nat-level recurrence gaps through the equality-only
`IntroducedLabelLevelInvariants`. This is not a transition invariant and
does not prove the Case 2 gap, source comparability, arbitrary-pivot chart
coverage, chart regularity/Jacobian facts, exponent updates, termination,
normal crossings, RLCT extraction, or the printed Case 2 vector repair.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-recurrence-state-interface.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-recurrence-state-interface-a4.md`.

Latest A4 update: the conditional Case 2 recurrence-weight update has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean names include
`introducedLabelFinset_succ_eq_insert`,
`not_mem_introducedLabelFinset_case2_new_before`,
`IntroducedLabelRecurrenceState.case2Succ`,
`IntroducedLabelRecurrenceState.case2Succ_case2Gap`,
`IntroducedLabelRecurrenceState.case2IntroducedLabelLeastValueGap_succ`,
`IntroducedLabelRecurrenceState.case2Succ_levelInvariants`,
`IntroducedLabelRecurrenceState.case2Succ_case2Gap_of_leastValueGap`,
`monomialRec_eq_of_step_eq_on_lt`,
`monomialRec_eq_mul_of_step_eq_mul_at`,
`levelProductStep_insert_eq_mul_of_new`,
`levelProductStep_insert_eq_of_ne`,
`IntroducedLabelRecurrenceState.step_succ_current_eq_new_mul`,
`IntroducedLabelRecurrenceState.step_succ_current_eq_of_ne`,
`IntroducedLabelRecurrenceState.weight_succ_current_eq_of_le`,
`IntroducedLabelRecurrenceState.weight_succ_current_eq_new_mul_of_ge`,
`CorrectedCase2NewLabelCertificate.case2_weight_succ_current_eq_newVar_mul`,
and
`CorrectedCase2NewLabelCertificate.case2_weight_succ_current_residual_flat_of_preGap`.
This proves that if a supplied successor recurrence state keeps old
introduced-label levels and variables and assigns the new label `(S,J+1)` level
`J` and variable `u`, then every post weight from `J+1` onward is `u` times the
old weight. Under the old Case 2 gap, the displayed residual-row weights remain
flat after this common multiplication. This is not a chart-production theorem,
does not repair the printed Case 2 vector mismatch, and does not prove source
comparability, exponent updates, transition invariants, normal crossings, or
RLCT extraction. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-recurrence-weight-update.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-recurrence-weight-update-a4.md`.

Latest A4 update: the displayed Case 2 successor source-substitution handoff
has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean
names are
`CorrectedCase2NewLabelCertificate.case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst_succWeights`
and
`CorrectedCase2NewLabelCertificate.exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights`.
These theorems combine the previous displayed selected-entry substitution
factorisation with the conditional recurrence-weight update, rewriting the
right-side diagonal in the displayed pivot-first and `Q/P` identities with a
supplied successor state's weights. The left side remains the old-weighted
source substitution. This is still conditional post-state bookkeeping, not a
proof of chart production, arbitrary-pivot chart coverage, coordinate
regularity/Jacobian, exponent updates, transition invariants, normal crossings,
RLCT extraction, source comparability, or the printed Case 2 vector repair.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-successor-source-substitution.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-successor-source-substitution-a4.md`.

Latest A4 update: the Case 2 supplied recurrence post-data package has landed
in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean names include
`IntroducedLabelRecurrenceState.Case2SuppliedPostData`,
`IntroducedLabelRecurrenceState.case2Succ_case2SuppliedPostData`,
`IntroducedLabelRecurrenceState.Case2SuppliedPostData.weight_succ_current_eq_new_mul_of_ge`,
`CorrectedCase2NewLabelCertificate.case2_weight_succ_current_eq_newVar_mul_of_postData`,
`IntroducedLabelRecurrenceState.Case2SuppliedPostData.weight_succ_current_residual_flat_of_preGap`,
`CorrectedCase2NewLabelCertificate.case2_weight_succ_current_residual_flat_of_preGap_of_postData`,
`CorrectedCase2NewLabelCertificate.case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst_succWeights_of_postData`,
and
`CorrectedCase2NewLabelCertificate.exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights_of_postData`.
The package is recurrence-local: it records old-label agreement and the new
label's level/variable assignment, while keeping source validity, the old gap,
and displayed pivot bounds separate. It is not chart production, chart
coverage, coordinate regularity/Jacobian, exponent update, transition
invariant, normal crossing, RLCT extraction, source comparability, or the
printed Case 2 vector repair. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-supplied-post-data.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-supplied-post-data-a4.md`.

Latest A4 update: the corrected Case 2 exponent update-data wrapper has landed
in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean name is
`IntroducedLabelExponentCertificates.extendDomain_correctedCase2NewLabel_updateData_of_prefixBound`.
It applies the existing corrected Case 2 new-label domain-extension theorem to
concrete selected-label update functions for `t`, `numerator`, and
`leastValue`, changing only `(S,J+1)`. This is exponent-domain bookkeeping
only: recurrence post-data does not imply these exponent assignments, and the
theorem does not prove chart production, exponent transition invariance,
source comparability, arbitrary-pivot transport, normal crossings, RLCT
extraction, or that the corrected vector is the PDF's printed vector.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-exponent-update-data.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-exponent-update-data-a4.md`.

Latest A4 update: the corrected Case 2 exponent post-data package has landed
in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`Case2CorrectedExponentPostData`,
`IntroducedLabelExponentCertificates.extendDomain_correctedCase2NewLabel_of_postData`,
`Case2CorrectedExponentPostData.updateSelected`,
`IntroducedLabelRecurrenceState.Case2SuppliedPostData.levelInvariants_of_correctedExponentPostData`,
and
`IntroducedLabelRecurrenceState.Case2SuppliedPostData.case2Gap_of_leastValueGap_of_correctedExponentPostData`.
The package records explicit old/new corrected exponent-map fields, the
concrete selected-label update wrapper factors through it, and supplied
recurrence post-data can now use supplied corrected exponent least-value data
to advance the recurrence-level Case 2 gap. This is corrected invariant
bookkeeping only: it does not prove chart production, an exponent transition
invariant, arbitrary-pivot transport, source comparability, normal crossings,
RLCT extraction, or that the corrected vector is the PDF's printed Case 2
vector. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-corrected-exponent-post-data.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-corrected-exponent-post-data-a4.md`.

Latest A4 update: arbitrary selected-entry Case 2 source-substitution transport
has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean
names include `case2ResidualBlockPivotRowOfMem`,
`case2ResidualBlockPivotColOfMem`, `case2ResidualBlockPivotOfMem_pair`,
`case2SelectedNormalizedMatrix`,
`case2SelectedSubstitutionMatrix`,
`case2Selected_diagonal_mul_substitutionMatrix_pivotFirst`,
`case2SelectedFollowingFactor`, `case2SelectedTransportedFollowingFactor`,
`case2Selected_diagonal_mul_substitutionMatrix_mul_followingFactor`,
`exists_case2SelectedQP_mul_sourceSubstitution_of_forall_dvd`, and
`exists_case2SelectedQP_mul_sourceSubstitution_of_flat_weights`. The theorem
family is finite algebra for a supplied residual-block pivot: it reindexes the
selected substitution and following factor into pivot-first coordinates and
applies `Q/P` only under explicit row-weight divisibility or flatness. It does
not prove arbitrary-pivot chart coverage, chart regularity/Jacobian facts,
recurrence post-state production, exponent updates, source comparability,
normal crossings, or RLCT extraction. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-arbitrary-selected-source-substitution.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-arbitrary-selected-source-substitution-a4.md`.

Latest A4 update: arbitrary selected-entry Case 2 recurrence handoff has landed
in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`exists_case2SelectedQP_mul_sourceSubstitution_of_recurrenceStateGap`,
`CorrectedCase2NewLabelCertificate.case2Selected_diagonal_mul_substitutionMatrix_pivotFirst_succWeights`,
`CorrectedCase2NewLabelCertificate.case2Selected_diagonal_mul_substitutionMatrix_pivotFirst_succWeights_of_postData`,
`CorrectedCase2NewLabelCertificate.exists_case2SelectedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights`,
and
`CorrectedCase2NewLabelCertificate.exists_case2SelectedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights_of_postData`.
The theorem family lifts the arbitrary selected finite-algebra wrapper to
packaged old recurrence states and supplied successor post-data, while keeping
the selected pivot and post-state supplied. It does not prove chart production,
arbitrary-pivot chart coverage, regularity/Jacobian, exponent updates, source
comparability, normal crossings, or RLCT extraction. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-arbitrary-selected-recurrence-handoff.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-arbitrary-selected-recurrence-handoff-a4.md`.

Latest A4 update: the Case 2 source-selected pair wrapper has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`case2SourceResidualBlock`, `case2SourceFollowingFactor`,
`case2SourceSelectedNormalizedMatrixOfMem`,
`case2SourceSelectedSubstitutionMatrixOfMem`,
`case2SourceSelectedFollowingFactorOfMem`,
`case2SourceSelectedTransportedFollowingFactorOfMem`,
`case2SourceSelectedNormalizedMatrixOfMem_pivot`,
`case2SourceSelectedSubstitutionMatrixOfMem_pivot`,
`exists_case2SourceSelectedQP_mul_sourceSubstitution_of_recurrenceStateGap`,
`CorrectedCase2NewLabelCertificate.case2SourceSelected_diagonal_mul_substitutionMatrix_pivotFirst_succWeights_of_postData`,
and
`CorrectedCase2NewLabelCertificate.exists_case2SourceSelectedQP_of_recurrenceStateGap_succWeights_of_postData`.
The theorem family restricts source-coordinate residual/following data to the
residual row/column subtypes and instantiates arbitrary selected-pivot
recurrence/post-data wrappers from a supplied source pivot pair in
`case2ResidualBlockPivotEntries`. It does not prove chart coverage,
source-order transition formulas for non-displayed pivots, chart-produced
post-data, regularity/Jacobian, exponent updates, normal crossings, or RLCT
extraction. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-selected-pair-wrapper.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-source-selected-pair-wrapper-a4.md`.

Latest A4 update: selected-entry principalization and finite operation unit
facts have landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The
proved Lean names are `weightedPivotBlockRowOp_isUnit`,
`weightedPivotBlockRowOp_det_isUnit`, `pivotQ_isUnit`, `pivotQ_det_isUnit`,
`pivotQinv_isUnit`, `pivotQinv_det_isUnit`,
`selectedEntryChartMap_centerIdeal_eq_span_singleton`,
`case2_selectedEntryChartMap_centerIdeal_eq_span_singleton_of_mem`, and
`case1_selectedEntryChartMap_centerIdeal_eq_span_singleton_of_mem`. The theorem
family proves that the finite `P/Q` operation matrices are units and that a
supplied selected-entry chart pulls the finite center ideal back to the
principal ideal `(u)`. It does not prove affine blow-up atlas coverage,
polynomial-coordinate Jacobian formulas, source-order transition formulas,
chart-produced recurrence/exponent post-data, normal crossings, or RLCT
extraction. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-principalization-unit-facts.md`.
Review artifact:
`threads/04-blow-up-certificate/review-selected-entry-principalization-unit-facts-a4.md`.

Latest A4 update: the Case 2 chart-family boundary has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`SelectedEntryChartFamilyBoundary`, `Case2ResidualBlockChartFamilyBoundary`,
`case2ResidualBlockPivotEntries_nonempty_of_cont`,
`Case2ResidualBlockChartFamilyBoundary.chart_regular_of_mem`,
`Case2ResidualBlockChartFamilyBoundary.transition_regular_of_mem`, and
`Case2ResidualBlockChartFamilyBoundary.chart_regular_displayedPivot_of_cont`.
This checkpoint names chart regularity and transition regularity as supplied
predicates over the finite Case 2 residual-block center, while proving only
that the displayed pivot makes that finite center nonempty under continuation.
It does not prove chart regularity, transition regularity, affine blow-up atlas
coverage, source-order transition formulas, chart-produced post-data,
Jacobians, normal crossings, or RLCT extraction. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-chart-family-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-chart-family-boundary-a4.md`.

Latest A4 update: the Case 1 chart-family boundary has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`case1CenterGenerators_nonempty`, `case1StripEntries_nonempty_of_bounds`,
`mem_case1CenterGenerators_inr_iff`, `Case1CenterChartFamilyBoundary`,
`Case1CenterChartFamilyBoundary.chart_regular_of_mem`,
`Case1CenterChartFamilyBoundary.transition_regular_of_mem`,
`Case1CenterChartFamilyBoundary.chart_regular_selectedOld`,
`Case1CenterChartFamilyBoundary.chart_regular_displayedPivot_of_bounds`, and
`Case1CenterChartFamilyBoundary.chart_regular_displayedPivot_of_firstJump_colBound`.
This checkpoint specializes the generic selected-entry chart-family boundary
to the Case 1 finite center: one `Unit` old-exceptional generator plus the
actual-width row strip. It proves only finite center nonemptiness, row-strip
nonemptiness under displayed bounds, right-branch membership, and supplied
regularity projections. It does not prove chart coverage, chart regularity,
transition regularity, the source validity of the hidden old label, arbitrary
row-strip pivot source-order transitions, chart-produced post-data, Jacobians,
normal crossings, or RLCT extraction. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-chart-family-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-chart-family-boundary-a4.md`.

Latest A4 update: the displayed top-left source-order adapter has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`Case1FirstJumpHypotheses.continuationBound_of_colBound`,
`WeightedPivotFirstSubstitutionData`,
`WeightedPivotFirstSubstitutionData.sourceOrder_identity`, and
`exists_weightedPivotFirstSubstitution_sourceOrder_identity_of_forall_dvd`.
This checkpoint packages the common finite `Q/P` handoff after a selected
chart has already produced a weighted, pivot-first source block. It proves
only finite width bookkeeping and the supplied source-order product identity;
it does not construct the selected chart, prove Case 1 full residual-block
substitution, produce recurrence/exponent post-data, decide continuation vs
advance, or prove chart coverage/regularity/Jacobians. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-displayed-top-left-source-order-adapter.md`.
Review artifact:
`threads/04-blow-up-certificate/review-displayed-top-left-source-order-adapter-a4.md`.

Latest A4 update: the displayed Case 1(2) local handoff has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`IntroducedLabelRecurrenceState.Case2SuppliedPostData.exists_case1DisplayedRowStrip_sourceOrder_identity_sourceWeights_succWeights_of_postData`,
`Case1DisplayedRowStripSuppliedTransitionBoundary`,
`Case1DisplayedRowStripSuppliedTransitionBoundary.stage_pos`,
`Case1DisplayedRowStripSuppliedTransitionBoundary.continuationBound`,
`Case1DisplayedRowStripSuppliedTransitionBoundary.newLabelActualWidth`,
`Case1DisplayedRowStripSuppliedTransitionBoundary.sourceOrder_identity_sourceWeights`,
and `Case1DisplayedRowStripSuppliedTransitionBoundary.extendExponentDomain`.
This checkpoint packages first-jump data, actual source bounds, a supplied
factored-base recurrence post-state, supplied pre-state exponent certificates,
level-tail invariants, and supplied Case 1 exponent post-data. It proves the
displayed top-left source-order identity with original source recurrence
weights on the left and supplied post-state weights on the right, and extends
the exponent certificate domain to `(S,J+1)`. It does not construct the
factored-base recurrence from the original pre-state, prove hidden old-label
source validity, prove chart-produced post-data, chart coverage, regularity,
Jacobians, normal crossings, or RLCT extraction. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-displayed-row-strip-local-handoff.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-displayed-row-strip-local-handoff-a4.md`.

Latest A4 update: the selected-old source substitution boundary has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`levelProductStep_updateVar_eq_mul_of_mem`,
`levelProductStep_updateVar_eq_of_ne`,
`levelProductStep_eq_mulStepAt_of_updateSelected`,
`IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData`,
`IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData.step_selectedLevel_eq_mul`,
`IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData.step_eq_of_ne_selectedLevel`,
`IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData.step_eq_mulStepAt_selectedLevel`,
`IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData.step_eq_mulStepAt_of_firstJump`,
and
`case1ResidualRowStripOldWeight_eq_sourceWeight_of_selectedOldFactoredBase`.
This checkpoint proves the finite-product recurrence effect of replacing the
selected old variable by `u*old'` in the pulled-back source recurrence:
`source.step = mulStepAt factoredBase.step u (J+J1)`, under supplied
same-domain factorisation data. It does not construct the selected-old chart,
identify the hidden old label behind the `Unit` center generator, construct the
factored-base state, produce post-data, prove coverage/regularity/Jacobians,
or prove normal crossings/RLCT. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-source-substitution.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-source-substitution-a4.md`.

Latest A4 update: the Case 1 source-substituted local handoff has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean name is
`Case1DisplayedRowStripSuppliedTransitionBoundary.sourceOrder_identity_substitutedSourceWeights`.
It combines the supplied displayed row-strip local handoff with the supplied
selected-old source substitution boundary, rewriting the left diagonal from
`monomialRec (mulStepAt factoredBase.step u (J+J1))` to
`source.weight (case2ResidualRowLevel n S J i)`. The theorem requires the
explicit level identification `level = factoredBase.level`; this is the bridge
needed to use the first-jump selected level with the recurrence-state data. It
does not construct the source pullback, selected-old chart, hidden old-label
source validity, factored-base or post states, chart-produced post-data,
coverage/regularity/Jacobians, normal crossings, or RLCT extraction. Statement
card:
`threads/04-blow-up-certificate/statement-card-a4-case1-source-substituted-local-handoff.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-source-substituted-local-handoff-a4.md`.

Latest A4 update: the Case 1 selected-old pullback boundary has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`Case1DisplayedRowStripSelectedOldPullbackBoundary`,
`Case1DisplayedRowStripSelectedOldPullbackBoundary.factoredBaseFirstJump`,
`Case1DisplayedRowStripSelectedOldPullbackBoundary.selectedOld_mem_center`,
`Case1DisplayedRowStripSelectedOldPullbackBoundary.sourcePullback_selectedIntroduced`,
`Case1DisplayedRowStripSelectedOldPullbackBoundary.selectedLevel`,
`Case1DisplayedRowStripSelectedOldPullbackBoundary.source_step_eq_mulStepAt`,
`Case1DisplayedRowStripSelectedOldPullbackBoundary.residualRowStripOldWeight_eq_sourceWeight`,
`Case1DisplayedRowStripSelectedOldPullbackBoundary.sourceOrder_identity`, and
`Case1DisplayedRowStripSelectedOldPullbackBoundary.extendExponentDomain`. This
checkpoint bundles the supplied selected-old source pullback with the supplied
displayed row-strip local handoff specialized to `factoredBase.level`, so the
source-facing handoff no longer needs a separate
`level = factoredBase.level` argument. It does not construct the selected-old
chart, prove that the `Unit` center token determines `(s0,k0)`, construct the
raw-coordinate source pullback, prove chart-produced post-data,
coverage/regularity/Jacobians, normal crossings, or RLCT extraction. Statement
card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-pullback-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-pullback-boundary-a4.md`.

Latest A4 update: the Case 1 selected-old supplied chart-family boundary has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean
names are
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.sourcePullback_selectedIntroduced`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.selectedLevel`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.selectedOld_mem_center`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.displayedPivot_mem_center`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.chart_regular_selectedOld`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.chart_regular_displayedPivot`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.transition_regular_selectedOld_displayedPivot`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.transition_regular_displayedPivot_selectedOld`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.source_step_eq_mulStepAt`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.sourceOrder_identity`,
and
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.extendExponentDomain`.
This checkpoint combines the selected-old pullback/local handoff boundary with
a supplied `Case1CenterChartFamilyBoundary`, exposing regularity and
transition-regularity projections for the selected old token and displayed
top-left row-strip pivot. It does not construct charts, prove coverage, derive
the old source label from `Unit`, construct the raw source pullback, compute
Jacobians, prove normal crossings, or extract RLCT. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-supplied-chart-family-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-supplied-chart-family-boundary-a4.md`.

Latest A4 update: the Case 1 selected-old source-coordinate wrapper has landed
in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.displayedPivot_selectedEntryChartMap_value_mem`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.displayedPivot_center_dvd`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.displayedPivot_centerIdeal_eq_span_singleton`,
`case2DisplayedSourceFollowingFactor`, and
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.sourceOrder_identity_sourceCoordinates`.
This checkpoint adapts the existing displayed Case 1(2) source-order
identity from source-coordinate residual/following-factor functions under
`residual (J+1,J+1)=1`, and projects finite selected-entry principalization
facts for the displayed top-left chart token. It does not
construct the selected-old chart, prove atlas coverage, derive `(s0,k0)` from
`Unit`, project selected-old `Unit` principalization with the displayed pivot
variable, construct the source pullback, produce chart post-data, compute
Jacobians, prove normal crossings, extract RLCT, or prove a transition
invariant. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-source-coordinate-wrapper.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-source-coordinate-wrapper-a4.md`.

Latest A4 update: the Case 1(1) selected-old chart source-coordinate identity
has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean
names are `case1SelectedOldPostWeight`,
`case1SelectedOld_diagonal_mul_sourceMatrix`, and
`case1SelectedOld_diagonal_mul_sourceMatrix_sourceCoordinates`. This checkpoint
proves the row-wise identity for the selected-old chart denominator:
`diag(baseWeight) * sourceRowStripMatrix = diag(postWeight) * dividedMatrix`,
where the post weight absorbs the selected old factor exactly on the Case 1
row strip. It is independent of the displayed Case 1(2) pivot
`u_(S,J+1)`, introduces no `(S,J+1)` label, and asserts no `Q/P` transition,
chart construction, coverage/regularity/Jacobians, normal crossings, RLCT, or
transition invariant. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-chart-source-coordinates.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-chart-source-coordinates-a4.md`.

Latest A4 update: the Case 1(1) selected-old same-domain boundary has landed
in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`Case1SelectedOldLowerTailExponentPostData`,
`IntroducedLabelExponentCertificates.case1_selectedLowerTail_of_postData`,
`IntroducedLabelExponentCertificates.case1_selectedLowerTail_of_levelTailInvariants_postData`,
`Case1SelectedOldSuppliedSameDomainBoundary`,
`Case1SelectedOldSuppliedSameDomainBoundary.selectedIntroduced`,
`Case1SelectedOldSuppliedSameDomainBoundary.selectedLevel`,
`Case1SelectedOldSuppliedSameDomainBoundary.sourceMatrix_identity`,
`Case1SelectedOldSuppliedSameDomainBoundary.sourceCoordinates_identity`, and
`Case1SelectedOldSuppliedSameDomainBoundary.updateExponentCertificates`.
This checkpoint packages supplied Case 1(1) exponent post-data with the
already proved row-strip identity and lower-tail update. It stays at `(S,J)`,
uses the actual-width numerator increment, and does not introduce `(S,J+1)`,
use the displayed Case 1(2) pivot, assert `Q/P`, construct charts, prove
coverage/regularity/Jacobians, prove normal crossings/RLCT, or prove a
transition invariant. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-same-domain-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-same-domain-boundary-a4.md`.

Latest A4 update: the Case 1(1) selected-old recurrence post-weight
calculation has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.
The proved Lean names are
`monomialRec_mulStepAt_case1_selectedOld_postWeight`,
`case1SelectedOldPostWeight_eq_monomialRec_loweredLevel`,
`case1SelectedOld_diagonal_mul_sourceMatrix_loweredLevel`, and
`case1SelectedOld_diagonal_mul_sourceMatrix_sourceCoordinates_loweredLevel`.
This checkpoint proves, from a supplied base recurrence, that moving the
selected old factor from level `J+J1` down to level `J` gives exactly the
Case 1(1) piecewise strip post weights on active residual rows. It does not
construct the selected-old chart, derive the base recurrence from source data,
prove recurrence-state post-data, introduce `(S,J+1)`, use the displayed
Case 1(2) pivot, assert `Q/P`, construct charts, prove
coverage/regularity/Jacobians, prove normal crossings/RLCT, or prove a
transition invariant. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-recurrence-postweight.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-recurrence-postweight-a4.md`.

Latest A4 update: the Case 1(1) selected-old lowered-recurrence boundary has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean
names are `Case1SelectedOldLoweredRecurrenceBoundary`,
`Case1SelectedOldLoweredRecurrenceBoundary.selectedIntroduced`,
`Case1SelectedOldLoweredRecurrenceBoundary.selectedLevel`,
`Case1SelectedOldLoweredRecurrenceBoundary.selectedOldPostWeight_eq_postWeight`,
`Case1SelectedOldLoweredRecurrenceBoundary.sourceMatrix_identity_postWeights`,
`Case1SelectedOldLoweredRecurrenceBoundary.sourceCoordinates_identity_postWeights`,
and `Case1SelectedOldLoweredRecurrenceBoundary.updateExponentCertificates`.
This checkpoint packages the pure recurrence post-weight calculation with
supplied pre/post recurrence states and same-domain exponent data. It assumes
the base-step equalities and does not derive them from a chart or source
coordinates. It stays at `(S,J)`, does not introduce `(S,J+1)`, does not use
the displayed Case 1(2) pivot, and does not assert `Q/P`, chart construction,
coverage/regularity/Jacobians, normal crossings/RLCT, or a transition
invariant. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-lowered-recurrence-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-lowered-recurrence-boundary-a4.md`.

Latest A4 update: the Case 1(1) selected-old `Unit` chart-family boundary has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean
names are `Case1SelectedOldUnitSuppliedChartFamilyBoundary`,
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.selectedIntroduced`,
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.selectedLevel`,
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.selectedOld_mem_center`,
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.chart_regular_selectedOld`,
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.transition_regular_selectedOld_of_mem`,
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.transition_regular_of_mem_selectedOld`,
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.selectedOld_selectedEntryChartMap_value_mem`,
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.selectedOld_center_dvd`,
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.selectedOld_centerIdeal_eq_span_singleton`,
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.sourceMatrix_identity_postWeights`,
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.sourceCoordinates_identity_postWeights`,
and `Case1SelectedOldUnitSuppliedChartFamilyBoundary.updateExponentCertificates`.
This checkpoint combines the supplied lowered recurrence boundary with the
supplied finite Case 1 chart-family boundary. It projects finite
selected-entry principalization for the selected-old `Sum.inl ()` token and
keeps the recurrence and exponent projections over `(S,J)`. It does not
identify the hidden old source label from the `Unit` token, construct the
selected-old chart, derive source recurrence states, introduce `(S,J+1)`, use
the displayed Case 1(2) pivot, assert `Q/P`, prove
coverage/regularity/Jacobians, prove normal crossings/RLCT, or prove a
transition invariant. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-unit-chart-family-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-unit-chart-family-boundary-a4.md`.

Latest A4 update: the Case 1(1) selected-old erased-base source model has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean
names are `levelProductStep_eq_mulStepAt_erase`,
`levelProductStep_erase_eq_of_eq_on_erase`,
`IntroducedLabelRecurrenceState.erasedStep`,
`IntroducedLabelRecurrenceState.step_eq_mulStepAt_erasedStep`,
`IntroducedLabelRecurrenceState.Case1SelectedOldLevelMoveData`,
`IntroducedLabelRecurrenceState.Case1SelectedOldLevelMoveData.post_erasedStep_eq_pre_erasedStep`,
`IntroducedLabelRecurrenceState.Case1SelectedOldLevelMoveData.pre_step_eq_mulStepAt`,
`IntroducedLabelRecurrenceState.Case1SelectedOldLevelMoveData.post_step_eq_mulStepAt`,
and `Case1SelectedOldLoweredRecurrenceBoundary.of_levelMoveData`. This
checkpoint defines the base recurrence as the introduced-label product with
the selected old label erased, proves pre/post `mulStepAt` equalities from a
supplied same-domain level move, and instantiates the existing lowered
boundary with that erased base. It does not construct the selected-old chart,
infer `(s0,k0)` from the `Unit` token, produce chart data, introduce
`(S,J+1)`, use Case 1(2), assert `Q/P`, prove coverage/regularity/Jacobians,
prove normal crossings/RLCT, or prove a transition invariant. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-erased-base-source-model.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-erased-base-source-model-a4.md`.

Latest A4 update: the Case 1(1) selected-old concrete level move has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`IntroducedLabelRecurrenceState.case1SelectedOldLevelMove`,
`IntroducedLabelRecurrenceState.case1SelectedOldLevelMove_level_selected`,
`IntroducedLabelRecurrenceState.case1SelectedOldLevelMove_level_of_ne`,
`IntroducedLabelRecurrenceState.case1SelectedOldLevelMove_var`,
`IntroducedLabelRecurrenceState.case1SelectedOldLevelMove_levelMoveData`, and
`Case1SelectedOldLoweredRecurrenceBoundary.of_sameDomain_case1SelectedOldLevelMove`.
This checkpoint gives a canonical same-domain post-state for Case 1(1): only
the selected old label's recurrence level is lowered to `J`; recurrence-label
variables and non-selected levels are unchanged. It instantiates the
erased-base lowered boundary from a same-domain package over `pre.level`.
This does not construct the selected-old chart, prove raw source-coordinate
post-state production, infer `(s0,k0)` from `Unit`, introduce `(S,J+1)`, use
Case 1(2), assert `Q/P`, prove coverage/regularity/Jacobians, prove normal
crossings/RLCT, or prove a transition invariant. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-concrete-level-move.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-concrete-level-move-a4.md`.

Latest A4 update: the Case 1(1) selected-old Unit boundary from the concrete
level move has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.
The proved Lean name is
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.of_sameDomain_case1SelectedOldLevelMove`.
This checkpoint packages the concrete lowered recurrence boundary with a
supplied finite Case 1 chart-family boundary, yielding a Unit chart-family
boundary with `post = pre.case1SelectedOldLevelMove s0 k0`,
`u = pre.var s0 k0`, and `baseStep = pre.erasedStep s0 k0`. It does not
construct chart regularity, transitions, coverage, Jacobians, normal
crossings/RLCT, Case 1(2), `Q/P`, or a transition invariant. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-unit-concrete-level-move.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-unit-concrete-level-move-a4.md`.

Latest A4 update: the Case 2 printed mismatch boundary has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`terminalExponent_printedCase2Vector_sub_prefixFormula`,
`terminalExponent_printedCase2Vector_eq_prefixFormula_iff`, and
`terminalExponent_case2Printed_ne_corrected_of_prefixDrop_of_cont`.
This checkpoint isolates the exact arithmetic boundary between the PDF's
printed actual-width Case 2 vector and the prefix-minimum numerator increment:
the difference is `(M^(S)-M(S))*(M^(S+1)-J)`, equality occurs only in the
equal-row-width or zero-column-factor cases, and under the continuation bound
`J+1<=M(S+1)` a genuine prefix-width drop `M(S)<M^(S)` gives unequal printed
and corrected terminal exponents. It does not prove a Case 2 transition
theorem, erratum, reachable-state
equal-width invariant, chart coverage, Jacobians, normal crossings/RLCT, or
termination. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-printed-mismatch-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-printed-mismatch-boundary-a4.md`.

Latest A4 update: the displayed Case 1(2) paper `Q/P` adapter has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`case1DisplayedPaperDchart`, `case1DisplayedPaperDchart_pivot`,
`case1DisplayedPaperSourceBlock`, `case1DisplayedPaperQ`,
`case1DisplayedPaperQinv`, `case1DisplayedPaperDpp`,
`case1DisplayedPaperCprime`, `case1DisplayedPaperDppp`,
`case1DisplayedPaperDpp_eq_pivotPostQBlock`,
`case1DisplayedPaperDpp_mul_Cprime`, and
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.sourceOrder_identity_sourceCoordinates_paperQP`.
This checkpoint exposes Aoyagi's printed `Q`, `Q^-1`, `D''`, `C'`, and `D'''`
notation over the already supplied displayed source-order identity. It proves
the `D''` post-`Q` block identification and the orientation
`D'' * C' = D_chart^pivot * C`, but remains a local adapter: normalized chart
data, recurrence/exponent post-data, quotient witnesses, regularity, and
transition data are still supplied. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-displayed-paper-qp-adapter.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-displayed-paper-qp-adapter-a4.md`.

Latest A4 update: the Case 2 supplied source-selected pivot boundary has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean
names are `Case2SourceSelectedSuppliedChartFamilyBoundary`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.correctedNewLabel`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.preCase2Gap`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.extendExponentDomain`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.postLevelInvariants`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.successorLeastValueGap`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.postCase2Gap`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.chart_regular_selectedPivot`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.chart_regular_of_mem`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.transition_regular_selectedPivot_of_mem`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.selectedPivot_centerIdeal_eq_span_singleton`,
and `Case2SourceSelectedSuppliedChartFamilyBoundary.sourceSelectedQP`. This
checkpoint packages a supplied residual-block pivot with corrected exponent
post-data, recurrence post-data, supplied chart-family predicates, finite
principalization, and source-selected arbitrary-pivot `Q/P` transport; it does
not prove atlas coverage, source-displayed non-top-left charts, chart-produced
post-data, Jacobians, normal crossings/RLCT, termination, or a transition
invariant. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-supplied-source-selected-pivot-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-supplied-source-selected-pivot-boundary-a4.md`.

Latest A4 update: the Case 2 displayed concrete-update boundary has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`Case2SourceSelectedSuppliedChartFamilyBoundary.displayedPivot_mem`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.chart_regular_displayedPivot`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.transition_regular_selectedPivot_displayedPivot`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.of_case2Succ_updateSelected`,
`Case2DisplayedSuppliedChartFamilyBoundary`,
`Case2DisplayedSuppliedChartFamilyBoundary.displayedPivot_mem`,
`Case2DisplayedSuppliedChartFamilyBoundary.sourceSelectedBoundary`,
`Case2DisplayedSuppliedChartFamilyBoundary.correctedNewLabel`,
`Case2DisplayedSuppliedChartFamilyBoundary.preCase2Gap`,
`Case2DisplayedSuppliedChartFamilyBoundary.extendExponentDomain`,
`Case2DisplayedSuppliedChartFamilyBoundary.chart_regular_displayedPivot`,
`Case2DisplayedSuppliedChartFamilyBoundary.displayedPivot_centerIdeal_eq_span_singleton`,
`Case2DisplayedSuppliedChartFamilyBoundary.of_case2Succ_updateSelected`, and
`Case2DisplayedSuppliedChartFamilyBoundary.sourceDisplayedQP_sourceCoordinates`.
This checkpoint specializes the supplied source-selected boundary to Aoyagi's
displayed top-left pivot and chooses concrete recurrence/exponent assignment
functions `pre.case2Succ u` and `Case2CorrectedExponentPostData.updateSelected`;
it does not prove those assignments are chart-produced, nor coverage,
coordinate regularity, Jacobians, normal crossings/RLCT, termination, or a
transition invariant. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-concrete-update-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-displayed-concrete-update-boundary-a4.md`.

## Ledger rules

- `Source ref` must eventually include PDF page numbers or stable local source
  anchors.
- `Lean target/status` records names only after the statement exists. Do not
  reserve impressive names before the statement is precise.
- `Reproduction/status` records the pen-and-paper derivation and independent
  check. A substantial calculation with this field pending is not
  formalisation-ready.
- `Review/status` is independent from build status. A theorem can be green and
  still fail fidelity or bedrock.
- Cited and deferred boundaries must appear in this table and in the matching
  claim card.
- Source references come from Aoyagi's PDF for this expedition. Do not fill
  ledger gaps from the quiver paper.
