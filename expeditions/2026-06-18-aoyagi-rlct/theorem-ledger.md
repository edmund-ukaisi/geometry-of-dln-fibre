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
| Blow-up inductive statement | A4 | PDF pp. 14-15 | reduced product coordinates | draft reproduction + failed check: `threads/04-blow-up-certificate/reproduction-draft.md`, `threads/04-blow-up-certificate/reproduction-check.md`; width notation and invariant gaps block | invariant theorem TBD; blocked | failed check |
| Blow-up Case 1 | A4 | PDF pp. 15-18 | reduced product coordinates, inductive statement | draft reproduction + failed check: actual width `M^{(S+1)}` vs prefix minimum `M(S+1)` must be repaired; missing pivot charts unresolved | transition lemma TBD; blocked | failed check |
| Blow-up Case 2 | A4 | PDF pp. 19-22 | reduced product coordinates, inductive statement | draft reproduction + failed check: actual widths, pivot charts, regularity/divisibility, and boundary cases unresolved | transition lemma TBD; blocked | failed check |
| Terminal normal-crossing exponents | A4 | PDF p. 22 | Case 1/2 induction | draft reproduction + failed check: terminal exponent formula cannot be accepted until corrected transition system and termination proof exist | certificate theorem TBD; blocked | failed check |
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
