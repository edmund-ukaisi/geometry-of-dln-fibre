# claims.md - Aoyagi claim ledger

Each claim is a working card. Source inventory must replace all `TBD` entries
with page-pinned source references before formalisation depends on them.

For every substantial Aoyagi-specific calculation, add:

- **Pen-and-paper reproduction.** path/status.
- **Reproduction check.** checker/path/verdict.

No such claim is formalisation-ready until both fields are filled.

## Claim A0 - cited normal-crossing extraction interface

- **Statement.** A suitable normal-crossing presentation of the transformed
  square loss determines the RLCT and pole order by the standard exponent
  minimum/order formula.
- **Tier.** Established analytic background.
- **Status.** open; intended Cited as extraction-only. A2 interface repair
  decision saved at `threads/02-analytic-interface/interface-repair-a2.md`.
- **Kill-condition.** Aoyagi's final extraction uses an analytic hypothesis not
  captured by the interface we state, or the interface computes a different
  invariant.
- **Evidence/source.** Aoyagi Definition 1, Lemma 1, Definition 2, and
  Hironaka/normal-crossing extraction discussion, PDF pp. 5-6.
- **Pen-and-paper reproduction.** Cite-interface check pending.
- **Reproduction check.** analytic scout report at
  `threads/02-analytic-interface/scout-report.md`; controller interface draft
  at `threads/02-analytic-interface/interface-draft.md`.
- **Lean target.** A named hypothesis/interface for concrete
  normal-crossing-certificate extraction, not a theorem pretending to prove the
  analytic extraction or general ideal-generator invariance.
- **Proved.** none by us.
- **Assumed.** the exact normal-crossing hypotheses once specified: finite
  charts, nonvanishing units, loss/Jacobian-prior exponents, prior hypotheses,
  and zero-loss-exponent convention.
- **Cited.** normal-crossing-to-RLCT extraction theorem.
- **Deferred.** formal proof of the analytic theorem.
- **Controller caution.** Aoyagi Lemma 1 on PDF p. 5 is analytic ideal-generator
  background. The expedition must not cite it as an additional Lean axiom unless
  the operator explicitly expands the cited boundary; prove/avoid it or include
  only certificate-level elementary transport before the single
  normal-crossing extraction interface. Regular-coordinate additivity is not a
  separate citation; the preferred route is a full regular-suspension
  certificate.

## Claim A1 - block elimination

- **Statement.** Aoyagi's full-rank block reduction rewrites a block matrix on
  an explicit full-rank chart into a block diagonal form by triangular
  invertible matrices; broader ideal/loss-germ consequences are separate.
- **Tier.** Established in Aoyagi; to be proved in Lean if elementary.
- **Status.** algebraic core formalised: Schur-complement block identities and
  rank formula are proved and reviewed in Lean; analytic/local-germ
  consequences remain out of scope.
- **Kill-condition.** The transformation requires an analytic/local inverse or
  rank-open chart hypothesis not represented in the Lean statement.
- **Evidence/source.** Aoyagi Lemma 2, PDF pp. 10-11.
- **Pen-and-paper reproduction.** draft at
  `threads/03-block-product-reduction/reproduction-draft.md`.
- **Reproduction check.** partial pass at
  `threads/03-block-product-reduction/reproduction-check.md`.
- **Lean target.** `DLNFibre.DLN.Aoyagi.schurComplement_leftBlockElim_fromBlocks`
  and `DLNFibre.DLN.Aoyagi.schurComplement_blockElim_fromBlocks`,
  plus indexed variants
  `DLNFibre.DLN.Aoyagi.schurComplement_leftBlockElim_fromBlocks_indexed` and
  `DLNFibre.DLN.Aoyagi.schurComplement_blockElim_fromBlocks_indexed`,
  plus `DLNFibre.DLN.Aoyagi.rank_fromBlocks_zero_zero` and
  `DLNFibre.DLN.Aoyagi.rank_fromBlocks_eq_card_add_rank_schurComplement_of_isUnit_det`,
  in `lean/DLNFibre/DLN/Aoyagi/BlockElimination.lean`.
- **Proved.** two algebraic block identities over a commutative ring, with
  indexed variants for arbitrary finite block index types, and over a field
  the block-diagonal rank additivity theorem and Schur-complement rank formula
  under explicit determinant-unit chart hypothesis `IsUnit A1.det`.
- **Assumed.** determinant-unit chart for the top-left block.
- **Cited.** none planned.
- **Deferred.** RLCT/local-germ invariance consequences until analytic boundary
  is resolved; product-level basis/open-chart induction remains A2.

## Claim A2 - product reduction

- **Statement.** The DLN product near a rank-r target splits into regular square
  factors and a reduced singular product, with RLCT computation reducible to the
  reduced problem plus regular variables.
- **Tier.** Established in Aoyagi; to be proved except for analytic extraction.
- **Status.** partial algebraic Lean artifacts landed and reviewed: the
  chart-local induction-step block identity, elementary matrix-entry ideal
  transport lemmas, through-subspace transport theorem, and per-edge
  transported-basis matrix block forms are proved; prefix-transported through
  bases, the endpoint total-product block form, and the local unitriangular
  chart-form preservation corollary are also proved. A supplied chart-data
  bundle now packages local complements and complement bases across the chain,
  and finite-dimensional Lean chains now supply finite-indexed chart data,
  including a version where the initial through-subspace is complementary to
  the total kernel. Concrete finite-basis edge, unitriangular, and endpoint
  block corollaries are also proved. The Aoyagi-order descending product
  `paperChainMap` and its prefix/suffix split laws are proved, and the
  reversed source-to-target `chainMap` is related to `paperChainMap`. Finite
  paper-order edge block, unitriangular, and endpoint wrappers are proved. The
  algebraic determinant-chart predicate layer for adapted paper edge matrices
  is proved. A one-edge right-elimination corollary for identity-corner adapted
  edges is proved. Endpoint-compatible shared adapted bases, finite chart data,
  and paper-order one-edge/total-product block packaging are proved. One-step,
  suffix, and all-layer adapted edge-product composition laws are proved.
  Deterministic block-projection right-elimination wrappers and abstract/supplied
  suffix-chain right-elimination theorems are proved. The paper-order endpoint
  suffix-chain wrapper is also proved. The first rank/open split is proved:
  adapted-basis matrix rank equals map range finrank, Schur residual rank is
  the source rank minus the through-rank, and the selected determinant chart is
  open. The endpoint-compatible fixed-chain basepoint certificate is also
  proved, bundling the endpoint chart data, edge determinant neighborhoods,
  endpoint residual-rank bridge, total-product block form, and suffix-chain
  right elimination. Fixed-basepoint variable-chain matrices are now defined:
  a variable chain `C` is represented in bases fixed from `B`, with
  composition laws and Schur-residual rank under explicit determinant-chart
  and exact-rank hypotheses. The first chart-local suffix step in these fixed
  bases is now proved with a supplied transformed edge, and the all-layer
  explicit-chart block-diagonal induction is proved. Matrix-space
  neighborhoods for transformed fixed-base edge determinant charts at `C = B`
  are now also proved, pointwise in the fixed accumulated upper block, and this
  has been pulled back to a single continuous-linear edge parameter and then
  assembled over a fixed finite family of accumulated upper blocks in the
  edge-family product topology. A variable-parameter continuity handoff for
  continuous edge and `Bprev` families is also proved. The deterministic
  one-step suffix-state update and the full recursive suffix-state
  block-diagonal invariant are now also proved at the abstract chart-local
  algebra level. The recursively produced `Bprev` block is proved continuous
  under recursive basepoint chart hypotheses, and the fixed-base chart
  neighborhood wrapper now uses that actual recursive `Bprev` family. A
  fixed-base endpoint block-diagonal neighborhood theorem is also proved for
  continuous reversed-edge families: near the base chain, the deterministic
  suffix state block-diagonalizes the endpoint product in the endpoint bases
  fixed from `B`. A pointwise rank bridge for transformed fixed-base reversed
  edges is proved under explicit exact-rank hypotheses, and the deterministic
  `D` field now has a named recurrence as a product by the visited Schur
  residual block. A neighborhood theorem now combines recursive charts,
  endpoint block form, and residual-rank implications from exact pointwise
  edge-rank hypotheses, without asserting exact-rank openness. The currently
  proved elementary/topological product-reduction boundary is now named in
  `ProductReductionBoundary.lean`, including a fixed-base certificate, a local
  fixed-base certificate carrying the basepoint certificate plus neighborhood
  membership, and an existential local certificate choosing a total-kernel
  complement. The full source Theorem 3 claim remains blocked.
- **Kill-condition.** The reduction silently uses the cited normal-crossing/RLCT
  theorem or another analytic equivalence not represented as a hypothesis.
- **Evidence/source.** Aoyagi Theorem 3 and following regular-variable
  contribution, PDF pp. 11-13.
- **Pen-and-paper reproduction.** draft at
  `threads/03-block-product-reduction/reproduction-draft.md`; through-layer
  basis repair at
  `threads/03-block-product-reduction/through-layer-basis-reproduction.md`.
- **Reproduction check.** findings at
  `threads/03-block-product-reduction/reproduction-check.md`; not
  formalisation-ready as stated. Repair report at
  `threads/03-block-product-reduction/reproduction-repair-a2.md`. Through-layer
  basis repair checked by xhigh checker `Hooke`; finite chart-data construction
  rechecked by xhigh explorer `Arendt`; paper-order bridge inventory at
  `threads/03-block-product-reduction/paper-order-bridge-notes.md`.
- **Lean target.**
  `DLNFibre.DLN.Aoyagi.productReduction_chartLocalInductionStep_fromBlocks` in
  `lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`; indexed variant
  `DLNFibre.DLN.Aoyagi.productReduction_chartLocalInductionStep_fromBlocks_indexed` in
  `lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`; local chart-stability
  theorem `DLNFibre.DLN.Aoyagi.upperUnitriangular_mul_fromBlocks_one_zero` in
  the same file; chart-form preservation corollary
  `DLNFibre.DLN.Aoyagi.exists_fromBlocks_one_zero_of_upperUnitriangular_mul` in
  the same file; determinant-chart predicates
  `DLNFibre.DLN.Aoyagi.topLeftCorner`,
  `DLNFibre.DLN.Aoyagi.upperRightBlock`,
  `DLNFibre.DLN.Aoyagi.lowerRightBlock`,
  `DLNFibre.DLN.Aoyagi.identityCornerForm`,
  `DLNFibre.DLN.Aoyagi.identityCornerDetChart`,
  `DLNFibre.DLN.Aoyagi.identityCornerDetChart_of_identityCornerForm`, and
  `DLNFibre.DLN.Aoyagi.identityCornerForm_upperUnitriangular_mul`, plus
  one-edge elimination theorems
  `DLNFibre.DLN.Aoyagi.productReduction_blockDiagonal_mul_fromBlocks_one_zero_rightElim_indexed`,
  `DLNFibre.DLN.Aoyagi.productReduction_blockDiagonal_mul_eq_fromBlocks_one_zero_rightElim_indexed`, and
  `DLNFibre.DLN.Aoyagi.productReduction_blockDiagonal_mul_identityCornerForm_rightElim`,
  `DLNFibre.DLN.Aoyagi.productReduction_blockDiagonal_mul_identityCornerForm_rightElim_submatrix`,
  and
  `DLNFibre.DLN.Aoyagi.productReduction_blockDiagonal_mul_unitriangular_identityCornerForm_rightElim`,
  `DLNFibre.DLN.Aoyagi.upperUnitriangular_neg_mul_upperUnitriangular`,
  `DLNFibre.DLN.Aoyagi.upperUnitriangular_neg_mul_upperUnitriangular_neg_neg`,
  `DLNFibre.DLN.Aoyagi.productReduction_identityCorner_suffixStep_rightElim`,
  `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState`,
  `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.BlockDiagonal`,
  `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.transformedEdge`,
  `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.step`,
  `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.terminal`,
  `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState`,
  `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_self`,
  `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.terminal_blockDiagonal`,
  `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_castSucc`,
  `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.step_blockDiagonal`,
  `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_blockDiagonal`, and
  `DLNFibre.DLN.Aoyagi.productReduction_identityCorner_suffixChain_rightElim`
  in the same file; topology lemmas
  `DLNFibre.DLN.Aoyagi.continuousAt_matrix_inv_of_isUnit_det`,
  `DLNFibre.DLN.Aoyagi.continuousAt_chartLocalSuffixState_step_B`, and
  `DLNFibre.DLN.Aoyagi.continuousAt_chartLocalSuffixState_suffixState_B` in
  `lean/DLNFibre/DLN/Aoyagi/ChartTopology.lean`; rank bridge theorems
  `DLNFibre.DLN.Aoyagi.rank_toMatrix_eq_finrank_range` and
  `DLNFibre.DLN.Aoyagi.rank_schurComplement_eq_sub_rank_fromBlocks` in
  `lean/DLNFibre/DLN/Aoyagi/BlockElimination.lean`; entry-ideal transport lemmas in
  `lean/DLNFibre/DLN/Aoyagi/EntryIdeal.lean`; through-layer subspace theorem
  `DLNFibre.DLN.Aoyagi.exists_chain_throughSubspaces` in
  `lean/DLNFibre/DLN/Aoyagi/ThroughLayerBasis.lean`; paper-order composite
  `DLNFibre.DLN.Aoyagi.paperChainMap` and lemmas
  `DLNFibre.DLN.Aoyagi.paperChainMap_self`,
  `DLNFibre.DLN.Aoyagi.paperChainMap_succ`,
  `DLNFibre.DLN.Aoyagi.paperChainMap_edge`,
  `DLNFibre.DLN.Aoyagi.paperChainMap_trans`, and
  `DLNFibre.DLN.Aoyagi.paperChainMap_zero_last_eq_prefix_comp_suffix`, plus
  `DLNFibre.DLN.Aoyagi.reverseVertex`,
  `DLNFibre.DLN.Aoyagi.reverseEdge`,
  `DLNFibre.DLN.Aoyagi.reverseEdge_eq_paperChainMap`, and
  `DLNFibre.DLN.Aoyagi.chainMap_reverse_eq_paper` in the same file; per-edge transported
  quotient-basis matrix theorem
  `DLNFibre.DLN.Aoyagi.exists_toMatrix_throughSubspaceEdge_eq_fromBlocks_one_zero`
  and direct-sum adapted-basis matrix theorem
  `DLNFibre.DLN.Aoyagi.exists_toMatrix_throughSubspaceEdge_basisOfIsCompl_eq_fromBlocks_one_zero`
  and prefix-basis matrix theorem
  `DLNFibre.DLN.Aoyagi.exists_toMatrix_throughSubspaceEdge_prefix_basisOfIsCompl_eq_fromBlocks_one_zero`
  and bundled chart-data theorem
  `DLNFibre.DLN.Aoyagi.exists_unitriangular_toMatrix_throughSubspaceEdge_chartData_eq_fromBlocks_one_zero`
  plus shared adapted-basis theorem
  `DLNFibre.DLN.Aoyagi.exists_toMatrix_throughSubspaceEdge_adaptedBasis_eq_fromBlocks_one_zero`
  plus endpoint total-product theorem
  `DLNFibre.DLN.Aoyagi.toMatrix_chainMap_zero_last_ker_basisOfIsCompl_eq_fromBlocks_one_zero_zero`
  and shared-basis endpoint theorem
  `DLNFibre.DLN.Aoyagi.toMatrix_chainMap_zero_last_chartData_eq_fromBlocks_one_zero_zero_of_maps_complement_to_zero`
  and finite-dimensional endpoint theorem
  `DLNFibre.DLN.Aoyagi.toMatrix_chainMap_zero_last_ker_finiteDimensional_eq_fromBlocks_one_zero_zero`
  plus finite chart-data existence theorems
  `DLNFibre.DLN.Aoyagi.throughSubspaceChartDataOfFiniteDimensional`,
  `DLNFibre.DLN.Aoyagi.throughSubspaceAdaptedBasis`,
  `DLNFibre.DLN.Aoyagi.throughSubspaceEndpointComplement`,
  `DLNFibre.DLN.Aoyagi.throughSubspaceEndpointComplementIndex`,
  `DLNFibre.DLN.Aoyagi.throughSubspaceEndpointChartDataOfFiniteDimensional`,
  `DLNFibre.DLN.Aoyagi.throughSubspaceAdaptedChainMapMatrix`,
  `DLNFibre.DLN.Aoyagi.throughSubspaceAdaptedChainMapMatrix_proof_irrel`,
  `DLNFibre.DLN.Aoyagi.throughSubspaceAdaptedChainMapMatrix_self`,
  `DLNFibre.DLN.Aoyagi.throughSubspaceAdaptedEdgeMatrix`,
  `DLNFibre.DLN.Aoyagi.throughSubspaceAdaptedChainMapMatrix_succ`,
  `DLNFibre.DLN.Aoyagi.throughSubspaceAdaptedChainMapMatrix_succ_right`,
  `DLNFibre.DLN.Aoyagi.throughSubspaceAdaptedEdgeProductMatrix`,
  `DLNFibre.DLN.Aoyagi.throughSubspaceAdaptedEdgeProductMatrix_self`,
  `DLNFibre.DLN.Aoyagi.throughSubspaceAdaptedEdgeProductMatrix_succ`,
  `DLNFibre.DLN.Aoyagi.throughSubspaceAdaptedChainMapMatrix_eq_edgeProductMatrix`,
  `DLNFibre.DLN.Aoyagi.throughSubspaceAdaptedChainMapMatrix_zero_eq_edgeProductMatrix`,
  `DLNFibre.DLN.Aoyagi.toMatrix_chainMap_zero_last_eq_adaptedEdgeProductMatrix`,
  `DLNFibre.DLN.Aoyagi.identityCornerForm_throughSubspaceAdaptedEdgeMatrix`,
  `DLNFibre.DLN.Aoyagi.productReduction_throughSubspaceAdaptedChainMapMatrix_suffixChain_rightElim`,
  `DLNFibre.DLN.Aoyagi.toMatrix_chainMap_zero_last_endpointChartData_eq_fromBlocks_one_zero_zero`,
  `DLNFibre.DLN.Aoyagi.endpointChartData_edge_and_totalProduct_blocks`,
  `DLNFibre.DLN.Aoyagi.nonempty_throughSubspaceChartDataOfFiniteDimensional`,
  `DLNFibre.DLN.Aoyagi.nonempty_throughSubspaceEndpointChartDataOfFiniteDimensional`,
  `DLNFibre.DLN.Aoyagi.exists_isCompl_ker_throughSubspaceEndpointChartDataOfFiniteDimensional`,
  `DLNFibre.DLN.Aoyagi.exists_toMatrix_throughSubspaceEdge_finiteDimensional_eq_fromBlocks_one_zero`,
  `DLNFibre.DLN.Aoyagi.exists_unitriangular_toMatrix_throughSubspaceEdge_finiteDimensional_eq_fromBlocks_one_zero`,
  `DLNFibre.DLN.Aoyagi.disjoint_ker_reverse_total_of_disjoint_ker_paperChainMap`,
  `DLNFibre.DLN.Aoyagi.isCompl_ker_reverse_total_of_isCompl_ker_paperChainMap`,
  `DLNFibre.DLN.Aoyagi.paperAdaptedReverseEdgeMatrix`,
  `DLNFibre.DLN.Aoyagi.paperUnitriangularLeft`,
  `DLNFibre.DLN.Aoyagi.identityCornerForm_paperAdaptedReverseEdgeMatrix`,
  `DLNFibre.DLN.Aoyagi.identityCornerDetChart_paperAdaptedReverseEdgeMatrix`,
  `DLNFibre.DLN.Aoyagi.identityCornerDetChart_unitriangular_paperAdaptedReverseEdgeMatrix`,
  `DLNFibre.DLN.Aoyagi.lowerRightBlock_paperAdaptedReverseEdgeMatrix_rank_eq_sub`,
  `DLNFibre.DLN.Aoyagi.productReduction_paperAdaptedReverseEdgeMatrix_rightElim`,
  `DLNFibre.DLN.Aoyagi.exists_isCompl_ker_paperEndpointChartDataOfFiniteDimensional`,
  `DLNFibre.DLN.Aoyagi.paperEndpointChartData_edge_and_totalProduct_blocks`,
  `DLNFibre.DLN.Aoyagi.exists_toMatrix_reverseEdge_finiteDimensional_eq_fromBlocks_one_zero`,
  `DLNFibre.DLN.Aoyagi.exists_unitriangular_toMatrix_reverseEdge_finiteDimensional_eq_fromBlocks_one_zero`,
  `DLNFibre.DLN.Aoyagi.toMatrix_paperChainMap_ker_finiteDimensional_eq_fromBlocks_one_zero_zero`,
  `DLNFibre.DLN.Aoyagi.productReduction_paperChainMap_endpointChartData_suffixChain_rightElim`,
  and
  `DLNFibre.DLN.Aoyagi.exists_isCompl_ker_throughSubspaceChartDataOfFiniteDimensional`
  in `lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`; full Theorem 3 target
  blocked. Topological determinant-chart theorems
  `DLNFibre.DLN.Aoyagi.isOpen_identityCornerDetChart`,
  `DLNFibre.DLN.Aoyagi.identityCornerDetChart_mem_nhds`,
  `DLNFibre.DLN.Aoyagi.leftMul_identityCornerDetChart_mem_nhds`,
  `DLNFibre.DLN.Aoyagi.fromBlocks_leftMul_identityCornerDetChart_mem_nhds`,
  `DLNFibre.DLN.Aoyagi.continuous_linearMap_toMatrix`,
  `DLNFibre.DLN.Aoyagi.identityCornerForm_mem_nhds_identityCornerDetChart`,
  `DLNFibre.DLN.Aoyagi.paperAdaptedReverseEdgeMatrix_mem_nhds_identityCornerDetChart`,
  and
  `DLNFibre.DLN.Aoyagi.unitriangular_paperAdaptedReverseEdgeMatrix_mem_nhds_identityCornerDetChart`
  are in `lean/DLNFibre/DLN/Aoyagi/ChartTopology.lean`. Endpoint basepoint
  certificate names/theorems `DLNFibre.DLN.Aoyagi.paperTotalMap`,
  `DLNFibre.DLN.Aoyagi.paperEndpointChartData`,
  `DLNFibre.DLN.Aoyagi.paperEndpointAdaptedEdgeMatrix`,
  `DLNFibre.DLN.Aoyagi.paperEndpointAdaptedTotalMatrix`,
  `DLNFibre.DLN.Aoyagi.lowerRightBlock_throughSubspaceEndpointAdaptedEdgeMatrix_rank_eq_sub`,
  `DLNFibre.DLN.Aoyagi.lowerRightBlock_paperEndpointAdaptedEdgeMatrix_rank_eq_sub`,
  `DLNFibre.DLN.Aoyagi.productReduction_paperEndpointAdaptedTotalMatrix_suffixChain_rightElim`,
  `DLNFibre.DLN.Aoyagi.PaperEndpointBasepointCertificate`, and
  `DLNFibre.DLN.Aoyagi.exists_paperEndpointBasepointCertificate` are in
  `lean/DLNFibre/DLN/Aoyagi/BasepointCertificate.lean`. Fixed-basepoint
  variable-chain definitions/theorems
  `DLNFibre.DLN.Aoyagi.lowerLeftBlock`,
  `DLNFibre.DLN.Aoyagi.schurResidualBlock`,
  `DLNFibre.DLN.Aoyagi.rank_schurResidualBlock_eq_sub_rank_of_identityCornerDetChart`,
  `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseEdgeMatrix`,
  `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseTotalMatrix`,
  `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseChainMapMatrix_succ_right`, and
  `DLNFibre.DLN.Aoyagi.rank_schurResidualBlock_paperEndpointFixedBaseEdgeMatrix_eq_sub`
  plus the basepoint topology wrappers
  `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseEdgeMatrix_selfBase_mem_nhds_identityCornerDetChart`
  and
  `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseEdgeMatrix_selfBase_mem_nhds_transformed_identityCornerDetChart`
  and
  `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseContinuousEdge_selfBase_mem_nhds_transformed_identityCornerDetChart`
  and
  `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseContinuousEdges_selfBase_mem_nhds_transformed_identityCornerDetChart`
  and
  `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseContinuousEdges_variableBprev_mem_nhds_transformed_identityCornerDetChart`
  and
  `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseContinuousEdges_recursiveBprev_mem_nhds_transformed_identityCornerDetChart`
  are in `lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean`; the one-step
  suffix theorem
  `DLNFibre.DLN.Aoyagi.productReduction_chartLocal_suffixStep_fromBlocks_indexed`
  and
  `DLNFibre.DLN.Aoyagi.productReduction_chartLocal_suffixChain_blockDiagonal_indexed`
  are in `lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`, with fixed-base
  wrappers `DLNFibre.DLN.Aoyagi.paperEndpointFixedBase_chartLocal_suffixStep`
  and
  `DLNFibre.DLN.Aoyagi.productReduction_paperEndpointFixedBaseChainMapMatrix_chartLocal_blockDiagonal`.
  Product-reduction boundary certificate wrappers
  `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseProductReductionCertificate`,
  `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseProductReductionCertificate_of_recursiveDetCharts`,
  `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseProductReductionCertificate_selfBase_mem_nhds`,
  `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseProductReductionLocalCertificate`,
  `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseProductReductionLocalCertificate_of_isCompl`,
  `DLNFibre.DLN.Aoyagi.PaperEndpointProductReductionLocalCertificate`, and
  `DLNFibre.DLN.Aoyagi.exists_paperEndpointProductReductionLocalCertificate`
  are in `lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`.
- **Proved.** one chart-local algebraic induction-step identity over a
  commutative ring, under explicit determinant-unit hypotheses for the prefix
  corner `C1` and next-layer corner `A1`, plus the same identity over arbitrary
  finite block index types. Also proved elementary
  matrix-entry ideal algebra: determinant-unit left/right multiplication
  preserves the entry ideal, product entries lie in the ideal generated by
  factor entries, and `D - F3 * F2` may replace `D` inside the four-family
  entry ideal generated by `X`, `F2`, `F3`, and `D`. Also proved the local
  upper-unitriangular chart-stability block identity preserving an identity
  top-left corner and zero lower-left block. Also proved the elementary
  through-layer subspace transport theorem for an upward chain, including
  adjacent restricted-edge equivalences. Also proved that a through-layer edge
  has matrix form `[I B; 0 D]` in transported `Module.Basis.sumQuot` bases and
  in transported direct-sum bases built from supplied complements. Also proved
  the prefix-transported version where one initial through-basis is transported
  to adjacent layers by `throughSubspacePrefixEquiv`. Also proved that the
  total chain map has endpoint matrix form `[I 0; 0 0]` when the
  source complement is the total kernel and the target through-basis is
  transported. Also proved that the upper-unitriangular chart transformation
  preserves existence of an identity-corner, zero-lower-left block form,
  including indexed versions for arbitrary finite basis index types. Also
  bundled supplied per-layer complement choices and complement bases in
  `ThroughSubspaceChartData`. Also proved that finite-dimensional layers
  supply concrete `Fin (finrank ...)`-indexed `ThroughSubspaceChartData` using
  chosen complements and `Module.finBasis`, and that one may choose the initial
  through-subspace complementary to the total kernel while preserving
  `finrank U₀ = finrank range P`. Also proved concrete finite-basis
  instantiations of the per-edge `[I B; 0 D]`, unitriangular
  chart-preservation, and endpoint `[I 0; 0 0]` block statements. Also proved
  Aoyagi-order product bookkeeping: `paperChainMap` composes maps
  `W_(s+1) -> W_s` in paper order and splits the full product as prefix
  followed by suffix, and reversing the vertices turns the source-to-target
  `chainMap` into the corresponding `paperChainMap`. Also proved finite
  paper-order edge wrappers for the concrete adapted-basis `[I B; 0 D]` block
  statement, its unitriangular chart-form preservation corollary, and the
  endpoint `[I 0; 0 0]` block form for the total paper product.
  Also proved an algebraic identity-corner/determinant-chart predicate layer:
  identity-corner form implies selected determinant-unit chart membership, and
  adapted paper edge matrices plus their unitriangular transforms satisfy it.
  Also proved one-edge right elimination: the explicit witnessed block identity
  is proved over a `NonAssocRing`; the equality and identity-corner wrappers
  give the form used by adapted edge matrices, with the paper adapted-edge
  corollary in the reversed Aoyagi order. Also proved deterministic
  right-elimination wrappers using the actual `upperRightBlock` and
  `lowerRightBlock` of an identity-corner matrix, including the version after
  an accumulated upper-unitriangular left multiplier. Also proved abstract
  suffix-chain right elimination and its supplied through-subspace adapted-basis
  instantiation: a segment matrix can be right-eliminated to `[I 0; 0 D]`.
  Also proved
  endpoint-compatible chart data with a shared adapted basis family: edge
  matrices and the total product matrix can now be stated in the same supplied
  basis family, including paper-order wrappers for the reversed Aoyagi chain.
  Also proved adapted matrix composition laws: extending a chain segment by one
  edge gives `edge * prefix`, splitting a segment after one edge gives
  `suffix * edge`, and the recursively defined product of adapted edge
  matrices from `i` to `j` is exactly the adapted matrix of `chainMap i j`.
  Also proved the paper-order endpoint suffix-chain wrapper: in the reversed
  Aoyagi chain with endpoint-compatible finite chart data, the adapted matrix
  of the total `paperChainMap` admits a source-side upper-unitriangular right
  elimination to `[I 0; 0 D]`. Also proved the rank bridge from adapted
  matrices back to source maps: matrix rank of a `toMatrix` representation is
  the finrank of the linear-map range, the Schur-complement rank formula has a
  subtraction form, and the lower-right residual block of an adapted paper edge
  has rank `finrank range(reverseEdge) - finrank U0`. Also proved the
  topological determinant-chart bridge: over a topological ring with open
  units, the selected determinant chart is open, hence adapted paper edge
  matrices and their unitriangular transforms have chart neighborhoods; fixed
  left multiplication pulls chart neighborhoods back to matrix-space
  neighborhoods, giving transformed fixed-base edge determinant-chart
  neighborhoods at the base chain `C = B`, pointwise in the fixed accumulated
  upper block, and the fixed-basis coordinate map pulls this back to a
  neighborhood of the base edge in the continuous-linear-map topology. Also
  proved finite product-topology assembly for a fixed prescribed family of
  accumulated upper blocks `Bprev p`, giving a neighborhood of the base edge
  family on which all those transformed determinant-chart predicates hold. Also
  proved the parameter-space handoff: if edge and `Bprev` families are
  continuous at a parameter and the transformed determinant charts hold there,
  then the same transformed chart predicates hold on a parameter neighborhood.
- **Assumed.** matrix dimensions encoded by types; determinant-unit chart
  hypotheses `IsUnit C1.det` and `IsUnit A1.det`; finite-dimensional layer
  hypotheses for the chart-data existence theorem; topological ring/open-units
  hypotheses for determinant-chart openness; nontrivially normed complete field
  and topological-vector-space hypotheses for the continuous-linear-map edge,
  finite product-topology, and variable-parameter continuity bridges. The full
  product-reduction theorem would additionally need source-faithful fixed-chart
  assembly for nearby variable layers, a deterministic construction and
  continuity proof for the chart-local induction's produced `Bprev` blocks, and
  certificate transport, not yet proved. Exact rank strata remain explicit
  hypotheses, not open-neighborhood conclusions.
- **Cited.** none for the chart-local algebraic theorem. Analytic invariance
  may only enter through the allowed analytic interface after it is fixed.
- **Deferred.** post-Theorem-3 RLCT reduction and regular-coordinate additivity
  as analytic theorems; instead, prove the elementary entry-ideal algebra and
  later build a full regular-suspension normal-crossing certificate. Full
  Theorem 3 assembly from source hypotheses, target-product normalization, and
  local analytic/certificate transport remain open. The shared adapted-basis
  layer removes the previous endpoint-basis mismatch, and the all-layer
  composition theorem identifies the adapted total matrix with the recursively
  ordered edge product, and the suffix theorem plus deterministic block
  projections provide a supplied-data suffix-chain reduction theorem, now
  packaged in paper order at the endpoint. The determinant-chart openness,
  transformed basepoint matrix-neighborhood packaging, and residual-rank bridge
  are proved, and the continuous-linear-map pullback plus fixed-family
  edge-product neighborhood assembly plus variable-`Bprev` continuity handoff
  are proved. The deterministic recursive suffix-state algebra is proved, and
  continuity of the recursively produced `Bprev` field plus its fixed-base
  transformed-chart neighborhood handoff are now proved under recursive
  basepoint chart hypotheses. Still open: source-faithful full Theorem 3
  statement, certificate transport, and continuity of the remaining state
  fields if a later certificate needs them. Exact rank-stratum hypotheses remain separate; see
  `threads/03-block-product-reduction/paper-order-bridge-notes.md`.

## Claim A3 - deepest singular point

- **Statement.** The global RLCT is attained at the deepest singular point used
  by Aoyagi's reduction.
- **Tier.** Established in Aoyagi; status to be decided by probe.
- **Status.** scope conflict / probe. Xhigh scout says this is analytic
  background cited to another Aoyagi paper, but the goal permits only the
  normal-crossing extraction citation in Lean.
- **Kill-condition.** The proof depends on lower semicontinuity/global analytic
  facts rather than elementary homogeneous scaling or explicit reduction.
- **Evidence/source.** Aoyagi Theorem 4, PDF p. 14.
- **Pen-and-paper reproduction.** pending/probe.
- **Reproduction check.** pending.
- **Lean target.** TBD by thread 02 or 06.
- **Proved.** pending.
- **Assumed.** TBD.
- **Cited.** not allowed as a separate Lean citation under current goal.
- **Deferred.** restricted proof or avoidance strategy pending.
- **Controller caution.** Allowed paths are: prove a restricted homogeneous
  deepest-point lemma, avoid Theorem 4 by formulating locally at the deepest
  point, or surface an operator decision to expand the cited boundary.

## Claim A4 - blow-up transition certificate

- **Statement.** Aoyagi's recursive Case 1 / Case 2 coordinate substitutions
  transform the reduced ideal into a monomial/diagonal normal-crossing form with
  the exponent vectors stated in the paper.
- **Tier.** New Lean packaging of source-guided finite bookkeeping; the full
  transition proof is not yet established.
- **Status.** blocked after repair pass. The source-confirmed repair separates
  actual widths `M^{(s)}` from prefix minima `M(S)`, but it exposes a Case 2
  incompatibility: the printed vector update on PDF p. 20 uses
  `t^{(i)} = M^{(i+1)}` for `i < S`, while the same chart records the
  numerator increment `(M(S)-J)(M^{(S+1)}-J)`; substituting the printed vector
  into the terminal exponent formula on PDF p. 22 gives
  `(M^{(S)}-J)(M^{(S+1)}-J)` unless `M(S)=M^{(S)}`. The monomial divisibility
  and normalized local `Q/P` algebra are now proved narrowly, and the quotient
  witness layer is connected to pivot-first `Q/P` algebra by existential
  wrappers. The source-displayed Case 2 top-left pivot `Q/P` product identity
  is also proved under flat displayed residual-row weights, and finite
  following-factor and diagonal row-weight reindexing are proved. The displayed
  Case 2 theorem now also accepts a residual following factor before
  pivot-first reindexing. The first source-substitution factoring bridge is
  also proved: the selected variable in the displayed residual block is moved
  into updated row weights before applying `Q/P`. The finite source-block
  tail lift is also proved: already-proved displayed residual-tail identities
  can be reattached below unchanged top rows. The displayed top-left
  source-coordinate chart map is now named and proved to restrict to the
  existing displayed selected-entry block API, with a source-chart version of
  the supplied displayed `Q/P` identity. The displayed residual-block
  coordinate count is also proved:
  `(M(S)-J)(M^{(S+1)}-J)`, with prefix-minimum rows and actual-width columns
  kept separate, and the corrected numerator expression is identified with
  that count under continuation. Missing arbitrary pivot charts,
  non-top-left source-displayed formulas, the full source blockdiag identity
  beyond the unchanged-top lift, full polynomial-coordinate chart construction,
  and proof that the chart produces the supplied recurrence post-state remain
  open. The printed `b'_i` versus
  standalone-`u` ambiguity is now handled only by the single-count
  normalization: the selected variable is absorbed into successor weights, not
  counted a second time outside them. Termination and boundary cases remain
  open.
- **Kill-condition.** The transition system misses a source chart or permits a
  terminal state not covered by Aoyagi's proof; or the Case 2 mismatch is a
  genuine source gap with no certificate-level repair compatible with the
  terminal formula.
- **Evidence/source.** Aoyagi blow-up section, PDF pp. 14-23.
- **Pen-and-paper reproduction.** draft at
  `threads/04-blow-up-certificate/reproduction-draft.md`; current repair
  report at `threads/04-blow-up-certificate/reproduction-repair-a4.md`.
- **Reproduction check.** failed/blocked at
  `threads/04-blow-up-certificate/reproduction-check.md`; source-image scout
  `Russell the 2nd` and pen-and-paper scout `Hume the 2nd` independently
	  confirmed the Case 2 mismatch and the prefix-minimum repaired vector.
	  Xhigh scouts `McClintock the 2nd`, `Gauss the 2nd`, and `Franklin the 2nd`
	  checked the monomial recurrence divisibility, normalized `P` row operation,
	  and normalized `Q` column operation respectively. Xhigh reviews of the
	  finite label-product bridge are saved at
	  `threads/04-blow-up-certificate/review-case2-label-product-gap-a4.md`.
	  Review of the successor source-substitution handoff is saved at
	  `threads/04-blow-up-certificate/review-case2-successor-source-substitution-a4.md`.
	  Review of the Case 1 source-substituted local handoff is saved at
	  `threads/04-blow-up-certificate/review-case1-source-substituted-local-handoff-a4.md`.
	  Review of the Case 1 selected-old pullback boundary is saved at
	  `threads/04-blow-up-certificate/review-case1-selected-old-pullback-boundary-a4.md`.
	  Review of the Case 1 selected-old supplied chart-family boundary is
	  saved at
	  `threads/04-blow-up-certificate/review-case1-selected-old-supplied-chart-family-boundary-a4.md`.
	  Review of the Case 2 supplied source-selected pivot boundary is saved at
	  `threads/04-blow-up-certificate/review-case2-supplied-source-selected-pivot-boundary-a4.md`.
	  Review of the Case 2 displayed concrete-update boundary is saved at
	  `threads/04-blow-up-certificate/review-case2-displayed-concrete-update-boundary-a4.md`.
	  Review of the Case 2 displayed source-chart map is saved at
	  `threads/04-blow-up-certificate/review-case2-displayed-source-chart-map-a4.md`.
	  Review of the Case 2 displayed center count is saved at
	  `threads/04-blow-up-certificate/review-case2-displayed-center-count-a4.md`.
- **Lean target.** No full transition theorem yet. Safe narrow targets must
  stay inside finite bookkeeping or monomial divisibility lemmas that do not
  assert Aoyagi's Case 2 transition. The first such target is landed in
  `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.
- **Proved.** terminal-exponent split API:
  `terminalExponent`, `printedCase2Vector`, `prefixMin`,
  `prefixCase2Vector`, `prefixMin_step_factor_zero`,
  `terminalExponent_printedCase2Vector`, and
  `terminalExponent_prefixCase2Vector`. These prove that the printed Case 2
  vector evaluates to the actual-width expression, while the prefix-minimum
  repaired vector evaluates to the printed update. Added the exact printed
  mismatch boundary:
  `terminalExponent_printedCase2Vector_sub_prefixFormula`,
  `terminalExponent_printedCase2Vector_eq_prefixFormula_iff`, and
  `terminalExponent_case2Printed_ne_corrected_of_prefixDrop_of_cont`,
  which characterize equality by equal row width or the degenerate
  zero-column-factor case and prove genuine mismatch under continuation plus a
  prefix-width drop. Also proved the monomial
  recurrence divisibility API `monomialRec`, `monomialTail`,
  `monomialRec_add_eq_tail_mul`, `monomialRec_dvd_of_le`,
  `monomialRec_pivot_dvd`, `mul_left_dvd_mul_left_of_dvd`, and
  `pivotMul_monomialRec_dvd_of_le`, which isolates the arithmetic needed for
  regularity of `b'_i / b'_(J+1)`. Also proved the normalized block
  row-operation theorem `weightedPivotBlockRowOp_mul_diagonal_mul`, with helper
  definitions `weightedPivotBlockRowOp`, `weightedPivotBlockMatrix`,
  `weightedPivotClearedBlock`, and `weightedPivotDiagonal`. Also proved the
  normalized column-operation API `pivotPreQBlock`, `pivotQ`, `pivotQinv`,
  `pivotPostQBlock`, `pivotPreQBlock_mul_pivotQ`,
  `pivotQ_mul_pivotQinv`, `pivotQinv_mul_pivotQ`, and
  `pivotPreQBlock_mul_eq_postQ_mul_Qinv_mul`, which clears the pivot row and
  multiplies the following factor by the displayed inverse. Also proved the
  combined normalized pivot-step API
  `pivotPostQBlock_eq_weightedPivotBlockMatrix`,
  `weightedPivotBlockRowOp_mul_diagonal_mul_pivotPostQBlock`,
  `weightedPivotBlockRowOp_mul_diagonal_mul_pivotPreQBlock_mul_pivotQ`, and
  `weightedPivotBlockRowOp_mul_diagonal_mul_pivotPreQBlock_mul`, which package
  the displayed `Q` and `P` matrix identities into one local product identity.
  Also proved actual-width label bookkeeping:
  `prefixMinNat`, `actualWidthLabel`, `prefixWidthLabel`,
  `actualWidthLabel_of_prefixWidthLabel`,
  `actualWidthLabel_not_prefixWidthLabel_of_prefixMinNat_lt_width`,
  `actualWidthLabel_case2_new`, `prefixWidthLabel_case2_new`,
  `correctedCase2PivotVector`, and
  `terminalExponent_correctedCase2PivotVector`, separating source label ranges
  from prefix-minimum continuation bounds and packaging the corrected Case 2
  vector over natural widths. Also proved introduced-label bookkeeping:
  `introducedLabel`, `introducedLabel_mono_J`,
  `not_introducedLabel_case2_new_before`, and
  `introducedLabel_case2_new_after`, identifying the active source labels at
  state `(S,J)` and the new pivot label added by advancing `J`; the prefix-bound
  corollary keeps the actual-width label result separate from the stronger
  source continuation condition. Also proved the corrected Case 2 vector
  minimum bookkeeping: `prefixMinNat_antitone`,
  `correctedCase2PivotVector_eq_prefix_of_lt`,
  `correctedCase2PivotVector_eq_J_of_le`,
  `le_correctedCase2PivotVector_of_le_prefixMinNat`, and
  `correctedCase2PivotVector_min_certificate`, plus the finite source-range
  least-value theorem `correctedCase2PivotVector_isLeast_valueSet_Icc`. Also
  proved the Prop-valued one-label certificate
  `CorrectedCase2NewLabelCertificate` and constructors
  `correctedCase2NewLabelCertificate_of_actualBound_of_stateBound` and
  `correctedCase2NewLabelCertificate_of_prefixBound`, packaging introducedness,
  corrected terminal exponent, and least-value data for the corrected Case 2
  new label only. Also proved finite exponent-domain bookkeeping:
  `LabelExponentCertificate`, `IntroducedLabelExponentCertificates`,
  `introducedLabel_succ_cases`, `introducedLabel_succ_iff`,
  `IntroducedLabelExponentCertificates.extendDomain_succ_current`,
  `IntroducedLabelExponentCertificates.extendDomain_correctedCase2NewLabel_of_bounds`,
  and
  `IntroducedLabelExponentCertificates.extendDomain_correctedCase2NewLabel_of_prefixBound`,
  plus the Case 2 residual-block entry set
  `case2ResidualBlockPivotEntries` and displayed-pivot membership theorem
  `case2_displayedPivot_mem_residualBlockPivotEntries_of_cont`. Also proved
  selected-entry substitution algebra `selectedEntryChartMap`,
  `selectedEntryChartMap_pivot`, `selectedEntryChartMap_of_ne`,
  `selectedEntryChartMap_pivot_dvd`,
  `selectedEntryChartMap_pivot_mem_valueSet`, and the Case 2 displayed-pivot
  specialization `case2_displayedPivot_selectedEntryChartMap_value_mem`. Also proved
  the Case 1 tail-lowering terminal-exponent arithmetic
  `lowerTailVector`, `terminalExponent_lowerTailVector_of_flatFromPred`, and
  `terminalExponent_lowerTailVector_of_flatFromPred_add`, with the required
  flat-tail and `2 <= S <= L` hypotheses explicit. Also proved
  `FlatTailFromPred`, lower-tail component/minimum facts, and the one-label
  transformer `LabelExponentCertificate.lowerTailVector_of_flatFromPred_add`,
  which additionally assumes old least value `J+J1` and `J <= J+J1`. Also
  proved finite Case 1 center-generator bookkeeping:
  `Case1CenterGenerator`, `case1StripRows`, `case1StripCols`,
  `case1StripEntries`, `case1CenterGenerators`,
  `mem_case1StripEntries_iff`, `case1_selectedOld_mem_center`,
  `case1_stripEntry_mem_center`, `case1_displayedPivot_mem_center_of_bounds`,
  and selected-entry value-set specializations for the selected-old and
  displayed-pivot choices. Also proved row-strip residual-block containment
  `case1StripRows_subset_case2ResidualBlockRows`,
  `case1StripCols_eq_case2ResidualBlockCols`,
  `case1StripEntries_subset_case2ResidualBlockPivotEntries`, and
  `case1_displayedPivot_mem_residualBlockPivotEntries_of_bounds`, making the
  explicit row-validity bound `J+J1 <= mu_S` visible. Also packaged the finite
  Case 1 first-jump and selected-label hypotheses as
  `Case1FirstJumpHypotheses`, including the strict nonterminal boundary
  `J+J1 < mu_S`, selected introduced label, selected level, gap, componentwise
  minimality, Nat-to-Int selected-level cast, and row-strip containment
  consequences. Also proved same-domain Case 1 lower-tail certificate
  bookkeeping:
  `IntroducedLabelExponentCertificates.updateSelected`,
  `Case1FirstJumpHypotheses.lowerTailVector_labelExponentCertificate`, and
  `IntroducedLabelExponentCertificates.case1_selectedLowerTail_sameDomain`,
  conditional on `leastValue = level`, flat-tail, boundary, selected post-data,
  and unchanged non-selected introduced labels. Added selected-label
  update-data helpers `updateSelectedLabelVector` and
  `updateSelectedLabelScalar` plus
  `case1_selectedLowerTail_updateData` to instantiate the same theorem with
  total assignment overrides. Added the conditional bridge package
  `IntroducedLabelLevelTailInvariants` and
  `case1_selectedLowerTail_of_levelTailInvariants`, assuming
  `leastValue = level` for introduced labels and flat-tail only above the
  current pivot. Added arbitrary selected-entry finite-center facts for Case 1
  and Case 2 centers: selected value-set membership and divisibility by the
  selected variable for every transformed finite-center generator. Added the
  generic pivot-first `Q/P` algebra bridge: a matrix with a selected pivot
  entry equal to `1` reindexes to `pivotPreQBlock`, and the existing normalised
  `Q/P` identities apply under explicit quotient witnesses
  `forall i, b i = q i * b0`. Added generic pivot-row quotient witnesses from
  divisibility, equality, monomial recurrence tails, equality-or-later
  recurrence data, and common pivot multiplication. Added pivot-first
  existential `Q/P` wrappers
  `exists_pivotFirstQP_mul_pivotQ_of_forall_dvd`,
  `exists_pivotFirstQP_mul_pivotQ_of_monomialRec_eq_or_le`,
  `exists_pivotFirstQP_mul_pivotQ_of_pivotMul_monomialRec_eq_or_le`,
  `exists_pivotFirstQP_mul_of_forall_dvd`,
  `exists_pivotFirstQP_mul_of_monomialRec_eq_or_le`, and
  `exists_pivotFirstQP_mul_of_pivotMul_monomialRec_eq_or_le`, plus the small
  `Case1FirstJumpHypotheses` displayed-pivot and strip-entry membership
  corollaries. Added source-displayed Case 2 top-left pivot data and algebra:
  `Case2ResidualRowIndex`, `Case2ResidualColIndex`,
  `case2DisplayedPivotRow`, `case2DisplayedPivotCol`,
  `selectedEntryNormalizedMap`, `selectedEntryNormalizedMatrix`,
  `selectedEntrySubstitutionMatrix`, and
  `exists_case2DisplayedQP_mul_of_flat_weights`. Added finite following-factor
  reindexing transport `pivotFirstFollowingFactor` and
  `pivotFirstMatrix_mul_pivotFirstFollowingFactor`. Added finite diagonal
  row-weight transport `weightedPivotDiagonal_eq_pivotFirst_diagonal`. Added
  the displayed Case 2 pivot-first following-factor package:
  `case2DisplayedNormalizedMatrix`, `case2DisplayedFollowingFactor`,
  `case2DisplayedNormalizedMatrix_mul_followingFactor`, and
  `exists_case2DisplayedQP_mul_pivotFirstFollowingFactor_of_flat_weights`.
  Added the displayed Case 2 source-substitution factorisation:
  `diagonal_mul_selectedEntrySubstitutionMatrix`,
  `pivotFirst_diagonal_mul_selectedEntrySubstitutionMatrix`,
  `case2DisplayedSubstitutionMatrix`,
  `case2DisplayedSubstitutionMatrix_eq_mul_normalized`,
  `case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst`,
  `case2Displayed_diagonal_mul_substitutionMatrix_mul_followingFactor`, and
  `exists_case2DisplayedQP_mul_sourceSubstitution_of_flat_weights`. Added
  `case2ResidualRowLevel`, `case2ResidualRowLevel_ge`,
  `case2ResidualRowLevel_displayedPivotRow`,
  `case2DisplayedTransportedFollowingFactor`, and
  `exists_case2DisplayedQP_mul_transportedFollowingFactor_of_rowIndex_monomialRec`.
  Added the finite source-block tail-lift API `verticalBlock`,
  `fromBlocks_mul_verticalBlock`, `fromBlocks_mul_verticalBlock_eq_of_tail`,
  `exists_case2DisplayedQP_verticalBlock_sourceSubstitution_of_flat_weights`,
  and
  `exists_case2DisplayedQP_verticalBlock_transportedFollowingFactor_of_rowIndex_monomialRec`.
  Added the displayed Case 2 recurrence-gap row-weight bridge
  `monomialTail_eq_one_of_forall_eq_one`,
  `monomialRec_eq_of_step_eq_one_on_Ico`,
  `case2ResidualRow_monomialRec_eq_pivot_of_gap`, and
  `exists_case2DisplayedQP_mul_sourceSubstitution_of_gap_monomialRec`, proving
  flat displayed residual row weights from an explicit gap hypothesis. Added
  the finite label-product gap bridge `levelProductStep`,
  `levelProductStep_eq_one_of_forall_ne`, `levelProductStep_eq_one_of_gap`,
  `case2ResidualRow_levelProduct_monomialRec_eq_pivot_of_gap`, and
  `exists_case2DisplayedQP_mul_sourceSubstitution_of_labelGap`, proving that a
  supplied finite label gap gives the recurrence-factor gap used by the
  displayed row-weight theorem. Added the introduced-label finite-domain
  bridge `actualWidthLabelFinset`, `mem_actualWidthLabelFinset`,
  `introducedLabelFinset`, `mem_introducedLabelFinset`,
  `levelProductStep_introducedLabelFinset_eq_one_of_gap`,
  `case2ResidualRow_introducedLabel_monomialRec_eq_pivot_of_gap`, and
  `exists_case2DisplayedQP_mul_sourceSubstitution_of_introducedLabelGap`,
  proving the same displayed bridge when the finite product ranges over
  Lean's introduced-label domain. Added the recurrence-state interface
  `IntroducedLabelRecurrenceState`, `IntroducedLabelLevelInvariants`,
  `case2IntroducedLabelLeastValueGap`,
  `IntroducedLabelRecurrenceState.case2Gap`,
  `IntroducedLabelRecurrenceState.case2Gap_of_leastValueGap`,
  `IntroducedLabelRecurrenceState.step`,
  `IntroducedLabelRecurrenceState.weight`,
  `IntroducedLabelRecurrenceState.case2ResidualRowWeight`,
  `IntroducedLabelRecurrenceState.step_eq_one_of_case2Gap`,
  `IntroducedLabelRecurrenceState.case2ResidualRow_weight_eq_pivot_of_case2Gap`,
  `IntroducedLabelRecurrenceState.case2ResidualRowWeight_eq_pivot_of_case2Gap`,
  `IntroducedLabelRecurrenceState.case2ResidualRowWeight_eq_displayedPivot_of_case2Gap`,
  and
  `exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap`,
  packaging the same conditional bridge through named recurrence data. Added
  the conditional Case 2 recurrence-weight update
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
  `CorrectedCase2NewLabelCertificate.case2_weight_succ_current_residual_flat_of_preGap`,
  proving that a supplied successor state with old recurrence data preserved
  and new label `(S,J+1)` at level `J` with variable `u` satisfies
  `post.weight i = u * pre.weight i` for every `J+1<=i`. Added the displayed
  Case 2 successor source-substitution handoff
  `CorrectedCase2NewLabelCertificate.case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst_succWeights`
  and
  `CorrectedCase2NewLabelCertificate.exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights`,
  rewriting the pivot-first and displayed `Q/P` right-side diagonals from
  `u * pre.weight` to the supplied successor weights `post.weight`, while the
  left side remains the old-weighted source substitution. Added the
  recurrence-local supplied post-data package
  `IntroducedLabelRecurrenceState.Case2SuppliedPostData`, its concrete
  `case2Succ` constructor, recurrence update and residual-flatness methods,
  and corrected-certificate `_of_postData` wrappers for the displayed
  source-substitution and `Q/P` handoff. Added the corrected Case 2 exponent
  update-data wrapper
  `IntroducedLabelExponentCertificates.extendDomain_correctedCase2NewLabel_updateData_of_prefixBound`,
  which changes only `(S,J+1)` to the corrected vector, numerator, and least
  value by selected-label update functions and extends the exponent certificate
  package to `(S,J+1)`. Added the corrected Case 2 exponent post-data package
  `Case2CorrectedExponentPostData`,
  `IntroducedLabelExponentCertificates.extendDomain_correctedCase2NewLabel_of_postData`,
  `Case2CorrectedExponentPostData.updateSelected`,
  `IntroducedLabelRecurrenceState.Case2SuppliedPostData.levelInvariants_of_correctedExponentPostData`,
  and
  `IntroducedLabelRecurrenceState.Case2SuppliedPostData.case2Gap_of_leastValueGap_of_correctedExponentPostData`,
  packaging explicit old/new exponent-map data and connecting supplied
  recurrence post-data plus supplied corrected exponent least values to the
  successor recurrence-level Case 2 gap. Added arbitrary selected-entry Case 2
  source-substitution transport:
  `case2ResidualBlockPivotRowOfMem`, `case2ResidualBlockPivotColOfMem`,
  `case2ResidualBlockPivotOfMem_pair`, `case2SelectedNormalizedMatrix`,
  `case2SelectedSubstitutionMatrix`,
  `case2SelectedSubstitutionMatrix_eq_mul_normalized`,
  `case2Selected_diagonal_mul_substitutionMatrix_pivotFirst`,
  `case2SelectedFollowingFactor`,
  `case2SelectedTransportedFollowingFactor`,
  `case2SelectedNormalizedMatrix_mul_followingFactor`,
  `case2Selected_diagonal_mul_substitutionMatrix_mul_followingFactor`,
  `exists_case2SelectedQP_mul_sourceSubstitution_of_forall_dvd`, and
  `exists_case2SelectedQP_mul_sourceSubstitution_of_flat_weights`, proving
  finite pivot-first transport and conditional `Q/P` for any supplied Case 2
  residual-block pivot under explicit row-weight divisibility or flatness.
  Added arbitrary selected-entry recurrence handoff:
  `exists_case2SelectedQP_mul_sourceSubstitution_of_recurrenceStateGap`,
  `CorrectedCase2NewLabelCertificate.case2Selected_diagonal_mul_substitutionMatrix_pivotFirst_succWeights`,
  `CorrectedCase2NewLabelCertificate.case2Selected_diagonal_mul_substitutionMatrix_pivotFirst_succWeights_of_postData`,
  `CorrectedCase2NewLabelCertificate.exists_case2SelectedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights`,
  and
  `CorrectedCase2NewLabelCertificate.exists_case2SelectedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights_of_postData`,
  proving the same arbitrary selected-pivot handoff under packaged old
  recurrence gaps and supplied successor post-data.
  Added source-selected pair wrappers:
  `case2SourceResidualBlock`, `case2SourceFollowingFactor`,
  `case2SourceSelectedNormalizedMatrixOfMem`,
  `case2SourceSelectedSubstitutionMatrixOfMem`,
  `case2SourceSelectedFollowingFactorOfMem`,
  `case2SourceSelectedTransportedFollowingFactorOfMem`,
  `exists_case2SourceSelectedQP_mul_sourceSubstitution_of_recurrenceStateGap`,
  `CorrectedCase2NewLabelCertificate.case2SourceSelected_diagonal_mul_substitutionMatrix_pivotFirst_succWeights_of_postData`,
  and
  `CorrectedCase2NewLabelCertificate.exists_case2SourceSelectedQP_of_recurrenceStateGap_succWeights_of_postData`,
  instantiating the arbitrary selected-pivot recurrence/post-data theorems
  from a supplied source pivot pair in `case2ResidualBlockPivotEntries` and
  source-coordinate residual/following data.
  Added the supplied source-selected pivot boundary:
  `Case2SourceSelectedSuppliedChartFamilyBoundary`,
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
  and
  `Case2SourceSelectedSuppliedChartFamilyBoundary.sourceSelectedQP`,
  packaging supplied pivot membership, corrected exponent post-data, recurrence
  post-data, chart-family predicates, finite selected-entry principalization,
  and source-selected arbitrary-pivot transport without claiming chart
  production or coverage.
  Added the displayed top-left Case 2 concrete-update boundary:
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
  `Case2DisplayedSuppliedChartFamilyBoundary.of_case2Succ_updateSelected`,
  and
  `Case2DisplayedSuppliedChartFamilyBoundary.sourceDisplayedQP_sourceCoordinates`.
  This specializes the supplied source-selected boundary to the displayed pivot
  `(J+1,J+1)`, makes pivot membership follow from continuation, and chooses the
  concrete recurrence successor `pre.case2Succ u` and corrected selected-label
  exponent post-data.
  Added the displayed top-left Case 2 source-chart map:
  `case2DisplayedSourceChartMap`, `case2DisplayedSourceNormalizedMap`,
  `case2DisplayedSourceChartMap_pivot`,
  `case2DisplayedSourceNormalizedMap_pivot`,
  `case2DisplayedSourceChartMap_of_ne`,
  `case2DisplayedSourceChartMap_eq_mul_normalized`,
  `case2Displayed_source_pair_eq_pivot_iff`,
  `case2DisplayedSourceSubstitutionBlock`,
  `case2DisplayedSourceNormalizedBlock`,
  `case2DisplayedSourceNormalizedBlock_eq_displayedNormalizedMatrix`,
  `case2DisplayedSourceSubstitutionBlock_eq_displayedSubstitutionMatrix`,
  `case2DisplayedSourceSubstitutionBlock_eq_mul_normalized`,
  `case2DisplayedSource_diagonal_mul_substitutionBlock_pivotFirst`,
  `case2DisplayedSourceNormalizedBlock_mul_sourceFollowingFactor`,
  `case2DisplayedSourceTransportedFollowingFactor`,
  `case2DisplayedSourceTransportedFollowingFactor_eq_displayedTransportedFollowingFactor`,
  and
  `Case2DisplayedSuppliedChartFamilyBoundary.sourceDisplayedQP_sourceChartMap`,
  proving the source-coordinate displayed chart map, its residual-block
  restriction to the existing displayed block API, its `u * normalised` form,
  and the supplied displayed `Q/P` identity in source-chart names.
  Added the displayed Case 2 residual-block coordinate count:
  `case2_continuation_le_prefixMinNat_current`,
  `case2_continuation_le_width_next`, `case2ResidualBlockRows_card`,
  `case2ResidualBlockCols_card`, `case2ResidualBlockPivotEntries_card`,
  `correctedCase2NewLabelNumerator`,
  `correctedCase2NewLabelNumerator_eq_card_of_bounds`, and
  `correctedCase2NewLabelNumerator_eq_card_of_cont`, proving that the
  corrected Case 2 numerator expression equals the selected residual-block
  coordinate count under continuation.
  Added selected-entry principalization/unit facts:
  `weightedPivotBlockRowOp_isUnit`,
  `weightedPivotBlockRowOp_det_isUnit`, `pivotQ_isUnit`,
  `pivotQ_det_isUnit`, `pivotQinv_isUnit`, `pivotQinv_det_isUnit`,
  `selectedEntryChartMap_centerIdeal_eq_span_singleton`,
  `case2_selectedEntryChartMap_centerIdeal_eq_span_singleton_of_mem`,
  and `case1_selectedEntryChartMap_centerIdeal_eq_span_singleton_of_mem`,
  proving the finite `P/Q` operation matrices are units and the pulled-back
  finite selected-entry center ideal is `(u)`.
  Added Case 2 chart-family boundary names:
  `SelectedEntryChartFamilyBoundary`,
  `Case2ResidualBlockChartFamilyBoundary`,
  `case2ResidualBlockPivotEntries_nonempty_of_cont`,
  `Case2ResidualBlockChartFamilyBoundary.chart_regular_of_mem`,
  `Case2ResidualBlockChartFamilyBoundary.transition_regular_of_mem`, and
  `Case2ResidualBlockChartFamilyBoundary.chart_regular_displayedPivot_of_cont`,
  making chart regularity and transition regularity explicit supplied
  assumptions while proving only displayed-pivot nonemptiness under
  continuation.
  Added Case 1 chart-family boundary names:
  `case1CenterGenerators_nonempty`,
  `case1StripEntries_nonempty_of_bounds`,
  `mem_case1CenterGenerators_inr_iff`,
  `Case1CenterChartFamilyBoundary`,
  `Case1CenterChartFamilyBoundary.chart_regular_of_mem`,
  `Case1CenterChartFamilyBoundary.transition_regular_of_mem`,
  `Case1CenterChartFamilyBoundary.chart_regular_selectedOld`,
  `Case1CenterChartFamilyBoundary.chart_regular_displayedPivot_of_bounds`, and
  `Case1CenterChartFamilyBoundary.chart_regular_displayedPivot_of_firstJump_colBound`,
  making Case 1 chart regularity and transition regularity explicit supplied
  assumptions while proving only finite center nonemptiness/membership facts
  and boundary projections. The `Unit` branch still hides an externally chosen
  old label; its source validity remains outside the finite-center theorem.
  Added displayed top-left source-order adapter names:
  `Case1FirstJumpHypotheses.continuationBound_of_colBound`,
  `WeightedPivotFirstSubstitutionData`,
  `WeightedPivotFirstSubstitutionData.sourceOrder_identity`, and
  `exists_weightedPivotFirstSubstitution_sourceOrder_identity_of_forall_dvd`.
  These prove only finite width bookkeeping and a supplied weighted
  pivot-first `Q/P` product identity; chart construction, source-coordinate
  production, and transition post-data remain explicit obligations. Added the
  displayed Case 1(2) local handoff:
  `IntroducedLabelRecurrenceState.Case2SuppliedPostData.exists_case1DisplayedRowStrip_sourceOrder_identity_sourceWeights_succWeights_of_postData`,
  `Case1DisplayedRowStripSuppliedTransitionBoundary`,
  `Case1DisplayedRowStripSuppliedTransitionBoundary.continuationBound`,
  `Case1DisplayedRowStripSuppliedTransitionBoundary.newLabelActualWidth`,
  `Case1DisplayedRowStripSuppliedTransitionBoundary.sourceOrder_identity_sourceWeights`,
  and
  `Case1DisplayedRowStripSuppliedTransitionBoundary.extendExponentDomain`.
  This packages first-jump data, actual source column bounds, supplied
  factored-base recurrence post-data, supplied pre-state exponent certificates,
  level-tail invariants, and supplied Case 1 exponent post-data. It proves the
  displayed top-left source-order identity with original source recurrence
  weights on the left and supplied post weights on the right, and extends the
  exponent certificate domain to `(S,J+1)`. Added the selected-old source
  substitution boundary:
  `levelProductStep_eq_mulStepAt_of_updateSelected`,
  `IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData`,
  `IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData.step_eq_mulStepAt_of_firstJump`,
  and
  `case1ResidualRowStripOldWeight_eq_sourceWeight_of_selectedOldFactoredBase`.
  This proves, under supplied same-domain selected-old factorisation data, that
  the pulled-back source recurrence after `old = u*old'` is
  `mulStepAt factoredBase.step u (J+J1)`. Added the source-substituted local
  handoff
  `Case1DisplayedRowStripSuppliedTransitionBoundary.sourceOrder_identity_substitutedSourceWeights`,
  which rewrites the displayed Case 1(2) local handoff's left diagonal from the
  explicit recurrence `monomialRec (mulStepAt factoredBase.step u (J+J1))` to
  supplied substituted source weights
  `source.weight (case2ResidualRowLevel n S J i)`. Added the supplied
  selected-old pullback package
  `Case1DisplayedRowStripSelectedOldPullbackBoundary`, with projections
  `factoredBaseFirstJump`, `selectedOld_mem_center`,
  `sourcePullback_selectedIntroduced`, `selectedLevel`,
  `source_step_eq_mulStepAt`,
  `residualRowStripOldWeight_eq_sourceWeight`, `sourceOrder_identity`, and
  `extendExponentDomain`. This packages the selected-old source pullback and
  displayed local handoff with the handoff specialized to `factoredBase.level`.
  Added the supplied chart-family package
  `Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary`, with
  projections for selected-old/displayed-pivot finite center membership,
  supplied chart regularity, supplied transition regularity in both
  directions, selected-label facts, the source-step update, the source-order
  identity, and exponent-domain extension. Added the Case 1(1)
  selected-old chart source-coordinate identity:
  `case1SelectedOldPostWeight`,
  `case1SelectedOld_diagonal_mul_sourceMatrix`, and
  `case1SelectedOld_diagonal_mul_sourceMatrix_sourceCoordinates`. This proves
  only the elementary row-wise selected-old denominator algebra for Case 1(1);
  it does not introduce `(S,J+1)`, use the displayed Case 1(2) pivot, assert
  `Q/P`, or produce charts/transitions. Added the supplied Case 1(1)
  same-domain boundary:
  `Case1SelectedOldLowerTailExponentPostData`,
  `IntroducedLabelExponentCertificates.case1_selectedLowerTail_of_postData`,
  `IntroducedLabelExponentCertificates.case1_selectedLowerTail_of_levelTailInvariants_postData`,
  `Case1SelectedOldSuppliedSameDomainBoundary`,
  `Case1SelectedOldSuppliedSameDomainBoundary.sourceCoordinates_identity`, and
  `Case1SelectedOldSuppliedSameDomainBoundary.updateExponentCertificates`.
  This packages supplied selected-old post-data with the row-wise source
  identity and same-domain exponent update, still without chart production or
  domain advancement. Added the pure Case 1(1) recurrence post-weight
  calculation:
  `monomialRec_mulStepAt_case1_selectedOld_postWeight`,
  `case1SelectedOldPostWeight_eq_monomialRec_loweredLevel`,
  `case1SelectedOld_diagonal_mul_sourceMatrix_loweredLevel`, and
  `case1SelectedOld_diagonal_mul_sourceMatrix_sourceCoordinates_loweredLevel`.
  This proves the strip post weights from a supplied base recurrence, not from
  constructed source recurrence data. Added the supplied source-facing lowered
  recurrence boundary:
  `Case1SelectedOldLoweredRecurrenceBoundary`,
  `Case1SelectedOldLoweredRecurrenceBoundary.selectedOldPostWeight_eq_postWeight`,
  `Case1SelectedOldLoweredRecurrenceBoundary.sourceCoordinates_identity_postWeights`,
  and `Case1SelectedOldLoweredRecurrenceBoundary.updateExponentCertificates`.
  This ties the recurrence-weight calculation to supplied pre/post recurrence
  states and the same-domain exponent update without constructing those states
  from coordinates. Added the selected-old `Unit` chart-family boundary:
  `Case1SelectedOldUnitSuppliedChartFamilyBoundary`, with projections for
  selected introducedness and level, selected-old finite center membership,
  supplied chart regularity, supplied transition regularity from/to any finite
  Case 1 center generator, selected-old finite selected-entry value-set,
  divisibility, ideal-principalization, pre/post recurrence source identities,
  and same-domain exponent certificates. This packages the `Sum.inl ()`
  selected-old chart token separately from the displayed Case 1(2) pivot and
  keeps the domain `(S,J)`.
  Added the erased-base source model:
  `levelProductStep_eq_mulStepAt_erase`,
  `levelProductStep_erase_eq_of_eq_on_erase`,
  `IntroducedLabelRecurrenceState.erasedStep`,
  `IntroducedLabelRecurrenceState.step_eq_mulStepAt_erasedStep`,
  `IntroducedLabelRecurrenceState.Case1SelectedOldLevelMoveData`, and
  `Case1SelectedOldLoweredRecurrenceBoundary.of_levelMoveData`. This defines
  the Case 1(1) base recurrence by erasing the selected old label, proves that
  the pre-state reinserts it at `J+J1` and the post-state reinserts it at `J`,
  and instantiates the lowered recurrence boundary without treating
  `baseStep` as arbitrary.
  Added the concrete same-domain level-move state:
  `IntroducedLabelRecurrenceState.case1SelectedOldLevelMove`,
  `IntroducedLabelRecurrenceState.case1SelectedOldLevelMove_levelMoveData`, and
  `Case1SelectedOldLoweredRecurrenceBoundary.of_sameDomain_case1SelectedOldLevelMove`.
  This canonical post-state lowers only the selected old label's recurrence
  level to `J`, keeps recurrence-label variables unchanged, and instantiates
  the erased-base boundary from `sameDomain` over `pre.level`.
  Added the concrete Unit boundary wrapper
  `Case1SelectedOldUnitSuppliedChartFamilyBoundary.of_sameDomain_case1SelectedOldLevelMove`,
  which combines this concrete lowered recurrence boundary with a supplied
  finite Case 1 chart-family boundary.
- **Assumed.** finite dimension/rank hypotheses; no transition invariant is
  accepted yet. The displayed Case 2 gap `step k=1` over `J+1<=k<mu_S` is an
  explicit hypothesis of one row-weight bridge, not a proved invariant. The
  introduced-label and recurrence-state bridges remove arbitrary finite-label
  and row-weight expression sprawl, but still assume the supplied states are
  Aoyagi's recurrence data: the Nat-valued `level` map is the current
  `tilde_t`, the variable map is the recurrence variable assignment, old data
  are preserved where assumed, the introduced-label Case 2 gap holds where
  flatness is used, and row weights are generated by this recurrence. This
  displayed bridge keeps residual rows
  `J+1..mu_S` separate from actual-width residual columns `J+1..n_(S+1)`, and
  counts the selected variable once in the updated weights `u*b_i`. It does not
  prove the source's Case 2 comparability sentence; the label gap alone is
  insufficient. The successor-weight handoff assumes the post-state and does
  not prove chart production. The supplied post-data package also keeps source
  validity, the old Case 2 gap, and displayed pivot bounds as separate theorem
  hypotheses rather than fields. The Aoyagi-specific arbitrary chart
  construction, coordinate transport, row-weight hypotheses in pivot-first
  coordinates, and full exponent transition updates remain open. The concrete
  exponent update-data wrapper does not follow from recurrence post-data and
  does not prove a chart leaves old exponent assignments unchanged. The Case
  1(2) local handoff also assumes the factored-base state, recurrence
  post-data, exponent post-data, and normalized pivot block; it does not prove
  chart production or hidden old-label source validity. The selected-old
  source substitution boundary assumes the supplied hidden old label and
  substituted source recurrence; the source-substituted local handoff also
  assumes `level = factoredBase.level` to transport the first-jump data to the
  recurrence-state level map. The selected-old pullback package removes that
  extra equality only by specializing the supplied handoff to
  `factoredBase.level`; it still does not identify the `Unit` center generator
  with a source label or construct the selected-old chart. The supplied
  chart-family package assumes chart regularity and transition regularity as
  fields; it does not prove them from coordinates or prove chart coverage. The
  selected-old source-coordinate wrapper restricts source residual and
  following-factor functions into the existing displayed source-order boundary
  under the displayed pivot normalization, and projects finite
  principalization facts for the displayed top-left chart token. It does not
  project selected-old `Unit` principalization with this same displayed pivot
  variable. It still does not construct the selected-old chart, raw source
  pullback, chart-produced post-data, or a transition invariant. The
  selected-old `Unit` chart-family boundary now projects finite
  principalization for the selected-old `Sum.inl ()` token itself, but only as
  a supplied chart-family/principalization interface over `(S,J)`: it does not
  identify the hidden source label from the token, construct charts or
  recurrence states from coordinates, use `(S,J+1)` or the displayed pivot,
  assert `Q/P`, or prove coverage, regularity from coordinates, Jacobians,
  normal crossings, RLCT, or transition invariance. The erased-base source
  model removes only the arbitrary base-step field for the recurrence
  checkpoint; it still assumes the moved-level recurrence data and does not
  construct that data from a chart or raw source coordinates. The concrete
  level-move state supplies that recurrence data from a pre-state by overriding
  the selected recurrence level only; it still does not prove that raw chart
  coordinates produce this state. The concrete Unit wrapper still assumes the
  finite chart-family boundary and does not prove regularity or transitions
  from coordinates. The displayed Case 1(2)
  paper `Q/P` adapter now exposes the source's local notation
  `Q`, `Q^-1`, `D''`, `C'`, and `D'''` over the supplied source-coordinate
  identity. It proves the post-`Q` block identification and `C' = Q^-1 C`
  orientation, but still assumes the normalized chart block,
  recurrence/exponent post-data, quotient witnesses, regularity, and
  transition data rather than constructing them.
  The Case 2 supplied source-selected pivot boundary assumes the pivot pair,
  recurrence post-data, corrected exponent post-data, chart regularity, and
  transition regularity. It derives bookkeeping projections from these fields,
  but does not prove atlas coverage, source-displayed non-top-left charts,
  chart-produced post-data, regularity from coordinates, Jacobians, normal
  crossings, RLCT extraction, termination, a full transition invariant, or a
  repair of the printed Case 2 vector mismatch.
  The displayed concrete-update boundary removes supplied recurrence/exponent
  post-data only by choosing concrete assignment functions. It still does not
  prove that the displayed affine chart produces those assignments, and it
  keeps chart regularity, transition regularity, coordinate regularity,
  Jacobians, normal crossings, RLCT extraction, termination, and the full
  transition invariant open.
  The displayed source-chart map proves only source-coordinate substitution
  and residual-block restriction for the top-left displayed pivot. It does not
  prove non-top-left formulas, chart coverage, chart-produced recurrence or
  exponent post-data, coordinate regularity, Jacobians, normal crossings, RLCT,
  termination, or a full transition invariant.
  The displayed center count is only a selected coordinate-equation count. It
  is not a center-dimension theorem, Jacobian exponent, chart-produced exponent
  update, chart coverage theorem, normal-crossing certificate, RLCT extraction,
  termination theorem, transition invariant, or printed-vector repair.
- **Cited.** none planned.
- **Deferred.** none planned.

## Claim A5 - arithmetic minimisation and pole-order count

- **Statement.** The exponent vectors from the blow-up certificate have minimum
  ratio and multiplicity/order equal to Aoyagi's closed formula.
- **Tier.** Established in Aoyagi; to be proved in Lean.
- **Status.** blocked after independent reproduction check; interior quadratic
  algebra is promising, but endpoint cases, terminal-variable restriction,
  minimiser feasibility, and Lemma 5 order-count construction are not checked.
- **Kill-condition.** Boundary cases in the dimension vector contradict the
  stated minimiser or pole-order count.
- **Evidence/source.** Aoyagi quadratic exponent expression and Lemmas 3-5,
  PDF pp. 22-27.
- **Pen-and-paper reproduction.** draft at
  `threads/05-arithmetic-tail/reproduction-draft.md`.
- **Reproduction check.** failed/blocked at
  `threads/05-arithmetic-tail/reproduction-check.md`.
- **Lean target.** TBD by thread 05.
- **Proved.** pending.
- **Assumed.** exact integer hypotheses from Aoyagi; no RLCT/arithmetic final
  theorem is accepted yet.
- **Cited.** none planned.
- **Deferred.** none planned.

## Claim A6 - final Aoyagi formula, conditional on A0

- **Statement.** Combining the proved Aoyagi-specific reductions with the cited
  normal-crossing extraction interface gives Aoyagi's RLCT and RLCT-order
  formula for deep linear networks.
- **Tier.** Final synthesis claim.
- **Status.** open.
- **Kill-condition.** Any source hypothesis, rank bound, dimension convention,
  or pole-order convention is lost in translation.
- **Evidence/source.** Aoyagi Theorem 2, PDF pp. 8-9. Aoyagi Theorem 1
  (PDF pp. 6-7) is a cited earlier three-layer formula, not the multi-layer
  main theorem.
- **Pen-and-paper reproduction.** pending.
- **Reproduction check.** pending.
- **Lean target.** TBD after A1-A5.
- **Proved.** pending; should include all Aoyagi-specific content.
- **Assumed.** cited analytic interface A0 and source hypotheses.
- **Cited.** A0 only, if expedition succeeds as intended.
- **Deferred.** formal analytic extraction theorem.
