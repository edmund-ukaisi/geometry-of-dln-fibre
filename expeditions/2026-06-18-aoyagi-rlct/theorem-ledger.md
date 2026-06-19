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
| Blow-up Case 1 | A4 | PDF pp. 15-18 | reduced product coordinates, inductive statement | repair report corrects the row-strip center and exponent increments to use actual active column width `M^{(S+1)}-J`; selected-variable chart and displayed pivot chart are understood only locally; full pivot-chart family or permutation reduction still missing; `P` quotient divisibility reduced to recurrence arithmetic; normalized displayed `Q/P` matrix identities checked; tail-lowering exponent increment checked under explicit flat-tail hypothesis; one-label lower-tail certificate transformer requires old least value `J+J1` and `J<=J+J1`; Case 1 center generator set records chosen old generator plus actual-width row strip but does not encode old-label hypotheses; row-strip containment requires explicit bound `J+J1<=mu_S`; first-jump package now records the strict nonterminal boundary `J+J1<mu_S`, selected introduced label, level gap, and componentwise minimality but not `b` recurrence semantics; same-domain lower-tail update assumes `leastValue=level`, flat-tail, selected post-data, and unchanged non-selected labels; selected-label update-data helpers are total assignment overrides only; level/tail bridge assumes `leastValue=level` for introduced labels and flat-tail only above pivot | monomial recurrence divisibility, normalized `Q` column-operation identities, normalized `P` row-operation identity, combined local normalized pivot-step identities, Case 1 tail-lowering terminal-exponent increment, lower-tail finite minimum facts, one-label lower-tail certificate transformer, finite Case 1 center generator bookkeeping, row-strip residual-block containment, Case 1 first-jump selected-label hypothesis package, conditional same-domain Case 1 lower-tail certificate update, selected-label update-data helper theorem, and conditional level/tail invariant bridge proved in `BlowupArithmetic.lean`; transition lemma TBD/blocked | repair note updated; statement cards `threads/04-blow-up-certificate/statement-card-a4-monomial-recurrence-divisibility.md`, `threads/04-blow-up-certificate/statement-card-a4-normalized-p-row-operation.md`, `threads/04-blow-up-certificate/statement-card-a4-normalized-q-operation.md`, `threads/04-blow-up-certificate/statement-card-a4-normalized-pivot-step.md`, `threads/04-blow-up-certificate/statement-card-a4-case1-tail-exponent-increment.md`, `threads/04-blow-up-certificate/statement-card-a4-case1-center-generators.md`, `threads/04-blow-up-certificate/statement-card-a4-case1-row-strip-containment.md`, `threads/04-blow-up-certificate/statement-card-a4-case1-first-jump-hypotheses.md`, `threads/04-blow-up-certificate/statement-card-a4-case1-same-domain-lower-tail-update.md`, `threads/04-blow-up-certificate/statement-card-a4-selected-label-update-data.md`, `threads/04-blow-up-certificate/statement-card-a4-level-tail-invariant-bridge.md` |
| Blow-up Case 2 | A4 | PDF pp. 19-22 | reduced product coordinates, inductive statement | page image confirms the printed vector `t_{S,J+1}^{(i)}=M^{(i+1)}` for `i<S` and printed increment `(M(S)-J)(M^{(S+1)}-J)`; substituting that printed vector into the terminal formula gives `(M^{(S)}-J)(M^{(S+1)}-J)` unless `M(S)=M^{(S)}`; the prefix-minimum vector repairs the arithmetic but is a corrected certificate, not printed source data; pivot charts, full polynomial-coordinate chart construction, `b'_i`/standalone-`u` bookkeeping, termination, and boundary cases remain unresolved; normalized displayed `Q/P` matrix identities are independent of this mismatch | arithmetic split, monomial recurrence divisibility, normalized `Q/P` identities, combined local normalized pivot-step identity, corrected Case 2 vector minimum certificate, one-label corrected Case 2 new-label certificate, finite exponent-domain bookkeeping, Case 2 residual-block entry set, and selected-entry substitution scaffold proved in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`; no source-faithful or corrected transition theorem accepted | xhigh rechecks confirm printed-vector mismatch/source gap, recurrence-divisibility reduction, normalized matrix algebra, one-label certificate scope, exponent-domain bookkeeping scope, residual-block entry bounds, and selected-entry substitution scope; statement cards `threads/04-blow-up-certificate/statement-card-a4-terminal-exponent-split.md`, `threads/04-blow-up-certificate/statement-card-a4-monomial-recurrence-divisibility.md`, `threads/04-blow-up-certificate/statement-card-a4-normalized-p-row-operation.md`, `threads/04-blow-up-certificate/statement-card-a4-normalized-q-operation.md`, `threads/04-blow-up-certificate/statement-card-a4-normalized-pivot-step.md`, `threads/04-blow-up-certificate/statement-card-a4-corrected-case2-vector-minimum.md`, `threads/04-blow-up-certificate/statement-card-a4-corrected-case2-new-label-certificate.md`, `threads/04-blow-up-certificate/statement-card-a4-finite-exponent-domain-bookkeeping.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-residual-block-entries.md`, `threads/04-blow-up-certificate/statement-card-a4-selected-entry-substitution.md` |
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
