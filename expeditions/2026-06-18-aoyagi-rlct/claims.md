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
  complement. The Aoyagi-style triangular endpoint multiplier wrapper is also
  proved: the deterministic suffix state's `L` is lower unitriangular, and the
  fixed-base certificate exposes regular `[I 0; F3 I]` and `[I F2; 0 I]`
  factors with proof witness `F2 = -S.B`. The full source Theorem 3 claim
  remains blocked.
- **Kill-condition.** The reduction silently uses the cited normal-crossing/RLCT
  theorem or another analytic equivalence not represented as a hypothesis.
- **Evidence/source.** Aoyagi Theorem 3 and following regular-variable
  contribution, PDF pp. 11-13.
- **Pen-and-paper reproduction.** draft at
  `threads/03-block-product-reduction/reproduction-draft.md`; through-layer
  basis repair at
  `threads/03-block-product-reduction/through-layer-basis-reproduction.md`;
  triangular endpoint wrapper at
  `threads/03-block-product-reduction/reproduction-a2-triangular-block-diagonal.md`.
- **Reproduction check.** findings at
  `threads/03-block-product-reduction/reproduction-check.md`; not
  formalisation-ready as stated. Repair report at
  `threads/03-block-product-reduction/reproduction-repair-a2.md`. Through-layer
  basis repair checked by xhigh checker `Hooke`; finite chart-data construction
  rechecked by xhigh explorer `Arendt`; paper-order bridge inventory at
  `threads/03-block-product-reduction/paper-order-bridge-notes.md`; triangular
  endpoint wrapper checked by xhigh reviewer `Kepler`.
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
  that count under continuation. The supplied corrected exponent post-data
  now also projects its new-label numerator to exactly this selected-coordinate
  count through the source-selected and displayed boundary packages; this is
  supplied bookkeeping, not chart-produced post-data. The displayed
  source-coordinate chart map now also principalizes the finite residual-block
  center ideal to `Ideal.span {u}` in source-chart names, with value and
  divisibility projections exported by the displayed boundary package. Missing
  direct displayed-boundary projections for the successor level/least-value
  bridge, successor least-value gap, and successor recurrence gap are now also
  filled by forwarding the already proved source-selected boundary facts. The
  terminal source-model and actual-width relabel layers now package supplied
  `Atop`, `Ctop`, and `F` under `n(S+1)=J+1`, derive the stopped terminal
  entry-ideal candidate, and copy supplied old `(S,J+1)` recurrence/exponent
  data to a candidate `(S+1,0)` state. This remains supplied-data
  bookkeeping: it does not prove source-produced `C'^(S+1)`, chart production,
  automatic Case 2 gap/tail transport, or terminal transition invariance. The
  terminal relabel-weight bridge now restates that candidate using
  `terminalRelabelPost.weight(J+1)` as the surviving scalar, with the terminal
  source model specialized to that relabelled weight. The displayed
  source-chart terminal model constructor now composes the concrete
  source-chart boundary constructor with this terminal wrapper, so arbitrary
  recurrence/exponent post-data are removed from that wrapper while
  chart-family predicates and terminal old-top/suffix data remain supplied.
  The actual-width column-exhaustion fact now records that the displayed pivot
  column complement is empty when `n(S+1)=J+1`.
  The companion current-prefix row-exhaustion fact records that the displayed
  pivot row complement is empty when `prefixMinNat n S=J+1`, independently of
  actual-width exhaustion.
  The source old-top/suffix specialization now constructs the old top row
  index `1..J`, the old top diagonal from `pre.weight`, and the old top block
  by restricting the supplied source following matrix, while keeping the
  suffix `F` supplied. The source suffix-chain checkpoint now names Aoyagi's
  remaining right product `prod_{s=S+2}^L C^(s)` as a raw paper-order matrix
  chain and instantiates the stopped source old-top theorem with that named
  suffix product. The source terminal product candidate checkpoint now
  reindexes the stopped terminal candidate into source rows `1..J+1`, with the
  surviving pivot row placed at `J+1`. The product-form bridge now proves that
  this reindexed candidate is
  `(case2DisplayedSourceTerminalWeight *
  case2DisplayedSourceTerminalCprimeCandidate) * F`. This still does not
  construct source-produced `C'^(S+1)`. The terminal-frontier bridges now
  reindex this candidate onto terminal prefix rows `1..M(S+1)` under stopped
  continuation and prove a supplied-terminal-matrix handoff from explicit
  old-row and pivot-row equations, packaged as `SuppliedTerminalCprimeBridge`.
  The continuing-branch post-pivot domain and next-block adapter are now also
  proved: after deleting the displayed pivot `(J+1,J+1)`, the lower-right row
  and column domains are the next same-stage residual domains `(S,J+1)`, the
  lower-right cleared block `D - x*y` and tail of `C' = Q^-1 C` are reindexed
  over those domains, and the lower rows of `D''' * C'` equal their product.
  This adapter is now connected to the displayed source-chart corrected
  post-data boundary: the concrete source-chart package uses `pre.case2Succ`
  at the displayed pivot value and conjoins the lower-row product identity
  with corrected supplied exponent/level/gap projections at `(S,J+1)`. This
  is still supplied-data compatibility, not chart production or transition
  invariance.
  The post-pivot following-factor tail is now also identified: `Q^-1` changes
  only the pivot row, so the reindexed post-pivot following-factor candidate
  is exactly the source following factor restricted to the next same-stage
  columns `(S,J+1)`. This is not a proof that the chart produces Aoyagi's full
  next `C'^(S+1)`.
  Combining these facts, Lean now rewrites the continuing lower-row product
  directly as the post-pivot residual block times
  `case2SourceFollowingFactor (J := J+1) C`, with supplied-boundary and
  concrete corrected-post-data projections.  The xhigh source/API audit also
  records that stronger chart-production claims are blocked at the present
  boundary: Aoyagi pp. 19-22 do not provide coordinate production of
  recurrence data, corrected exponent data, a successor chart family, full
  source-produced `C'^(S+1)`, or a transition invariant.
  Missing arbitrary pivot
  charts,
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
	  Review of the Case 2 corrected post-data center-count projection is saved
	  at
	  `threads/04-blow-up-certificate/review-case2-corrected-postdata-center-count-a4.md`.
	  Review of the Case 2 displayed source-chart principalization is saved at
	  `threads/04-blow-up-certificate/review-case2-displayed-source-chart-principalization-a4.md`.
	  Review of the Case 2 displayed successor gap projections is saved at
	  `threads/04-blow-up-certificate/review-case2-displayed-successor-gap-projections-a4.md`.
	  Review of the Case 2 source-selected chart-map adapter is saved at
	  `threads/04-blow-up-certificate/review-case2-source-selected-chart-map-a4.md`.
	  Review of the Case 2 displayed source-chart recurrence boundary is saved
	  at
	  `threads/04-blow-up-certificate/review-case2-displayed-source-chart-recurrence-boundary-a4.md`.
	  Review of the Case 2 displayed source-chart boundary constructor is saved
	  at
	  `threads/04-blow-up-certificate/review-case2-displayed-source-chart-boundary-constructor-a4.md`.
	  Review of the Case 2 post-pivot exhaustion boundary is saved at
	  `threads/04-blow-up-certificate/review-case2-post-pivot-exhaustion-a4.md`.
	  Review of the Case 2 displayed pivot-complement exhaustion boundary is
	  saved at
	  `threads/04-blow-up-certificate/review-case2-displayed-pivot-complement-exhaustion-a4.md`.
	  Reproduction/check of the Case 2 post-pivot domain handoff is saved at
	  `threads/04-blow-up-certificate/reproduction-case2-post-pivot-domain-handoff-a4.md`
	  and
	  `threads/04-blow-up-certificate/review-case2-post-pivot-domain-handoff-a4.md`.
	  Reproduction/check of the Case 2 post-pivot next-block adapter is saved
	  at
	  `threads/04-blow-up-certificate/reproduction-case2-post-pivot-next-block-a4.md`
	  and
	  `threads/04-blow-up-certificate/review-case2-post-pivot-next-block-a4.md`.
	  Reproduction of the Case 2 source-chart post-pivot boundary is saved at
	  `threads/04-blow-up-certificate/reproduction-case2-source-chart-post-pivot-boundary-a4.md`;
	  landed-patch review is saved at
	  `threads/04-blow-up-certificate/review-case2-source-chart-post-pivot-boundary-a4.md`.
	  Reproduction of the Case 2 post-pivot following-factor tail is saved at
	  `threads/04-blow-up-certificate/reproduction-case2-post-pivot-following-factor-tail-a4.md`;
	  landed-patch review is saved at
	  `threads/04-blow-up-certificate/review-case2-post-pivot-following-factor-tail-a4.md`.
	  Reproduction of the Case 2 post-pivot source-following product adapter
	  is saved at
	  `threads/04-blow-up-certificate/reproduction-case2-post-pivot-source-following-product-a4.md`;
	  the stronger chart-production blocker audit is saved at
	  `threads/04-blow-up-certificate/blocked-audit-case2-chart-production-next-following-a4.md`;
	  landed-patch review is saved at
	  `threads/04-blow-up-certificate/review-case2-post-pivot-source-following-product-a4.md`.
	  Reproduction of the Case 2 constructed-`Cprime` coordinate direction is
	  saved at
	  `threads/04-blow-up-certificate/reproduction-case2-constructed-cprime-a4.md`;
	  landed-patch review is saved at
	  `threads/04-blow-up-certificate/review-case2-constructed-cprime-a4.md`.
	  Review of the Case 2 stage-relabel domain audit is saved at
	  `threads/04-blow-up-certificate/review-case2-stage-relabel-domain-a4.md`.
	  Review of the Case 2 displayed cleared-block vacuity corollary is saved
	  at
	  `threads/04-blow-up-certificate/review-case2-displayed-cleared-block-vacuity-a4.md`.
	  Review of the Case 2 displayed cleared-block following-factor absorption
	  scaffold is saved at
	  `threads/04-blow-up-certificate/review-case2-displayed-cleared-block-following-factor-a4.md`.
	  Review of the Case 2 displayed terminal source model is saved at
	  `threads/04-blow-up-certificate/review-case2-displayed-terminal-source-model-a4.md`.
	  Review of the Case 2 actual-width terminal relabel is saved at
	  `threads/04-blow-up-certificate/review-case2-actual-width-terminal-relabel-a4.md`.
	  Review of the Case 2 terminal relabel-weight candidate is saved at
	  `threads/04-blow-up-certificate/review-case2-terminal-relabel-weight-candidate-a4.md`.
	  Review of the Case 2 source-chart terminal model constructor is saved at
	  `threads/04-blow-up-certificate/review-case2-source-chart-terminal-model-constructor-a4.md`.
	  Review of the Case 2 actual-width column exhaustion is saved at
	  `threads/04-blow-up-certificate/review-case2-actual-width-column-exhaustion-a4.md`.
	  Review of the Case 2 current-prefix row exhaustion is saved at
	  `threads/04-blow-up-certificate/review-case2-current-prefix-row-exhaustion-a4.md`.
	  Review of the Case 2 source old-top/suffix specialization is saved at
	  `threads/04-blow-up-certificate/review-case2-source-old-top-suffix-specialization-a4.md`.
	  Review of the Case 2 source suffix chain is saved at
	  `threads/04-blow-up-certificate/review-case2-source-suffix-chain-a4.md`.
	  Review of the Case 2 source terminal product candidate is saved at
	  `threads/04-blow-up-certificate/review-case2-source-terminal-product-candidate-a4.md`.
	  Review of the Case 2 source terminal product form is saved at
	  `threads/04-blow-up-certificate/review-case2-source-terminal-product-form-a4.md`.
	  Review of the Case 2 terminal frontier bridges is saved at
	  `threads/04-blow-up-certificate/review-case2-terminal-frontier-bridges-a4.md`.
	  Review of the Case 2 source-chart terminal source-suffix wrappers is
	  saved at
	  `threads/04-blow-up-certificate/review-case2-source-chart-terminal-source-suffix-a4.md`.
	  Review of the source suffix split and actual-width terminal boundary is
	  saved at
	  `threads/04-blow-up-certificate/review-source-suffix-chain-split-and-actual-width-boundary-a4.md`.
	  Review of the source suffix utilities is saved at
	  `threads/04-blow-up-certificate/review-source-suffix-utilities-a4.md`.
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
  `Case2DisplayedSuppliedChartFamilyBoundary.postLevelInvariants`,
  `Case2DisplayedSuppliedChartFamilyBoundary.successorLeastValueGap`,
  `Case2DisplayedSuppliedChartFamilyBoundary.postCase2Gap`,
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
  The constructed-`Cprime` coordinate direction proves only pivot-first matrix
  algebra: `C=Q*Cprime`, `Q^-1*C=Cprime`, and
  `D''*Cprime=D_chart*C`.  It does not construct a total source-coordinate
  following function, chart-produced post-data, a successor chart family,
  coverage, regularity, Jacobians, normal crossings/RLCT, or a transition
  invariant.
  The constructed-`Cprime` `Q/P` wrapper proves only the finite product
  identity `(P*weighted source-substituted block)*(Q*Cprime) =
  (weighted D''')*Cprime` under supplied displayed-boundary data. It does not
  source-produce `Cprime`, construct next `C'^(S+1)`, produce recurrence or
  exponent post-data, or prove chart coverage, regularity, Jacobians, normal
  crossings/RLCT, or a transition invariant.
  The constructed source following-factor lift proves only that the old
  pivot-first following factor can be represented by a total source-coordinate
  function whose displayed source-following restriction is the supplied matrix.
  Applied to `Q*Cprime`, this gives the source-coordinate form of
  `Q^-1*(Q*Cprime)=Cprime` and a supplied-boundary `Q/P` wrapper. It still
  does not source-produce the full next `C'^(S+1)`, recurrence or exponent
  post-data, successor chart-family data, coverage, regularity, Jacobians,
  normal crossings/RLCT, arbitrary-pivot coverage, terminal relabeling, or a
  transition invariant.
  The displayed center count is only a selected coordinate-equation count. It
  is not a center-dimension theorem, Jacobian exponent, chart-produced exponent
  update, chart coverage theorem, normal-crossing certificate, RLCT extraction,
  termination theorem, transition invariant, or printed-vector repair.
  The corrected post-data center-count projection only reads supplied corrected
  exponent post-data and exposes the same count through the source-selected and
  displayed supplied boundary packages; it still does not construct exponent
  post-data from the chart or compute a Jacobian/volume exponent.
  The displayed source-chart principalization is only finite residual-block
  center ideal algebra in the names of Aoyagi's displayed top-left source
  chart; it is not an arbitrary-pivot chart, loss/Kullback ideal statement,
  analytic germ statement, chart-production theorem, coverage theorem, or
  Jacobian/volume calculation. It also does not prove normal crossings, RLCT
  extraction, termination, a transition invariant, or repair of the printed
  Case 2 vector mismatch.
  The displayed successor gap projections only forward source-selected
  successor bookkeeping through the displayed boundary; recurrence and exponent
  post-data remain supplied fields, not chart-produced data.
  The source-selected chart-map adapter names the selected-entry source chart
  map for any supplied Case 2 residual-block pivot and rewrites the existing
  arbitrary-pivot source-selected `Q/P` identity in those source-chart names.
  The pivot remains supplied, and this does not prove atlas coverage,
  non-top-left displayed source formulas, chart-produced recurrence/exponent
  post-data, coordinate regularity, Jacobian/volume arithmetic, normal
  crossings, RLCT extraction, termination, transition invariance, or printed
  vector repair.
  The displayed source-chart recurrence boundary ties the concrete recurrence
  successor `pre.case2Succ u` to the displayed source chart's pivot value and
  proves the row-weight update from `J+1` onward. This is still recurrence
  bookkeeping only; it does not construct the affine chart, prove
  chart-produced exponent post-data, compute Jacobians, prove coverage or
  coordinate regularity, prove normal crossings, extract RLCT, prove
  termination/transition invariance, or repair the printed vector mismatch.
  The displayed source-chart boundary constructor packages the displayed
  supplied boundary with scalar equal to the displayed source chart pivot value
  and post state `pre.case2Succ` of that pivot. It is only a source-facing
  wrapper over supplied corrected exponent post-data and supplied chart-family
  predicates, not chart production, coverage, Jacobian arithmetic, or a
  transition invariant.
  The post-pivot exhaustion boundary proves the finite lower-right domain
  after the displayed Case 2 pivot: rows `J+2..M(S)`, columns
  `J+2..M^(S+1)`, cardinalities, nonemptiness iff
  `J+2 <= M(S+1)`, and emptiness when the next continuation bound fails. This
  is only domain bookkeeping and does not construct the `S+1` advance,
  post-data, Jacobians, termination, or transition invariance.
  The displayed pivot-complement exhaustion boundary identifies the displayed
  pivot row/column complements with those post-pivot domains and proves that
  failure of the next continuation bound empties one complement type. The
  lower-right complement matrix is therefore subsingleton, and zero over a
  codomain with zero. This is lower-right domain-vacuity bookkeeping only; it
  does not construct `D'''_J`, prove `D'''_J = (1,0,...,0)` or its transpose,
  construct `C'^(S+1)`, build the `S+1` recurrence/exponent state, prove
  chart coverage or regularity, compute Jacobians, prove normal crossings,
  extract RLCT, prove termination/transition invariance, or repair the
  printed vector mismatch.
  The post-pivot domain handoff now proves that the displayed Case 2
  lower-right row, column, and entry domains after deleting pivot `(J+1,J+1)`
  are exactly the next same-stage residual domains at `(S,J+1)`. It also
  restates next residual-center nonemptiness as
  `J+2 <= prefixMinNat n (S+1)` and gives row/column subtype equivalences from
  displayed pivot complements directly to the next residual row/column index
  types. This is finite domain bookkeeping only; it does not produce the next
  residual matrix, chart coverage, transition regularity or invariance,
  Jacobian arithmetic, terminal-product principalization, normal crossings,
  RLCT extraction, or the terminal `(S+1,0)` relabel branch.
  The post-pivot next-block adapter now packages the displayed continuing
  branch as supplied same-stage data: the lower-right cleared block `D - x*y`
  is reindexed to the next `(S,J+1)` residual row/column types, the tail of
  `C' = Q^-1 C` is reindexed to the next column type, and the lower rows of
  `D''' * C'` are proved equal to their product. The nonemptiness theorem
  exposes the continuing bound `J+2 <= prefixMinNat n (S+1)`. This is finite
  block algebra and reindexing only; it does not prove chart production,
  recurrence/exponent post-data from coordinates, chart coverage, coordinate
  regularity, transition invariance, Jacobian arithmetic, normal crossings,
  RLCT extraction, arbitrary pivot coverage, terminal relabeling, or repair of
  the printed vector mismatch.
  The displayed source-chart post-pivot boundary projects that adapter through
  the supplied displayed boundary and packages the concrete source-chart
  constructor with corrected post-data projections at `(S,J+1)`. This proves
  compatibility of the supplied next-block product with the corrected
  recurrence/exponent boundary, not chart production, successor chart-family
  construction, transition invariance, Jacobian arithmetic, normal crossings,
  RLCT extraction, arbitrary pivot coverage, terminal relabeling, or repair of
  the printed vector mismatch.
  The post-pivot following-factor tail theorem proves the lower rows of
  `Q^-1 C` are unchanged and reindexes them to the next same-stage residual
  columns. This closes a narrow following-product candidate while explicitly
  not proving source production of the full next `C'^(S+1)`.
  The stage-relabel domain audit proves the finite side split
  `prefixMinNat n S = J+1 ∨ n(S+1)=J+1`, the old `(S,J+1)` to `(S+1,0)`
  introduced-label equality under actual-width exhaustion `n(S+1)=J+1`, and
  the explicit row-side extra-label witness `(S,J+2)` when
  `J+2 <= n(S+1)`. This is finite domain bookkeeping only; it does not
  construct the `S+1` recurrence/exponent state, prove terminal `D'''` shape,
  construct `C'^(S+1)`, prove chart coverage or regularity, compute Jacobians,
  prove normal crossings, extract RLCT, prove termination/transition
  invariance, or repair the printed vector mismatch.
  The displayed cleared-block vacuity corollary applies the complement
  matrix-vacuity theorem to the already-cleared displayed pivot-first block,
  proving `weightedPivotClearedBlock (D - x*y) = weightedPivotClearedBlock 0`
  under failed next continuation. This is only lower-right vacuity in
  pivot-first coordinates; it does not construct the full `D'''_J` terminal
  branch, choose the row/column presentation, construct `C'^(S+1)`, build the
  `S+1` recurrence/exponent state, prove chart coverage or regularity,
  compute Jacobians, prove normal crossings, extract RLCT, prove termination
  or transition invariance, or repair the printed vector mismatch.
  The displayed cleared-block following-factor absorption scaffold proves
  that `weightedPivotClearedBlock 0 * verticalBlock Ctop Ctail =
  verticalBlock Ctop 0`, plus the displayed failed-continuation specialization
  after lower-right vacuity. This is pivot-first block multiplication only; it
  does not construct or identify `C'^(S+1)`, construct the full `D'''_J`
  terminal branch, choose the row/column presentation, build `S+1` post-data,
  prove chart coverage or regularity, compute Jacobians, prove normal
  crossings, extract RLCT, prove termination or transition invariance, or
  repair the printed vector mismatch.
  The displayed paper terminal absorption layer names the displayed Case 2
  paper blocks `D_chart`, `Q`, `Q^-1`, `D''`, `C' = Q^-1 C`, and `D'''`.
  It restates the supplied displayed source-chart `Q/P` identity in this
  notation and proves that, under failed next continuation,
  `matrixEntryIdeal (D''' * C')` equals the matrix-entry ideal of the top
  pivot row of `C'`. The supporting generic lemma says zero bottom rows do
  not change a matrix-entry ideal. This is paper notation and zero-row
  absorption only; it does not construct or identify Aoyagi's next-stage
  `C'^(S+1)`, choose the row/column terminal presentation, build `S+1`
  post-data, prove chart coverage or regularity, compute Jacobians, prove
  normal crossings, extract RLCT, prove termination or transition invariance,
  or repair the printed vector mismatch.
  The displayed terminal stack layer proves that stacking a fixed old top
  block over two bottom blocks respects matrix-entry ideal equality. Applied
  to the stopped displayed Case 2 terminal block, it proves
  `<entries([Cold; D''' * C'])> = <entries([Cold; C0])>` for arbitrary
  supplied `Cold`, where `C0` is the top pivot row of `C'`. This does not
  identify `Cold` with the source old top rows or `[Cold;C0]` with
  Aoyagi's full `C'^(S+1)`, prove the diagonal-weighted full terminal product
  ideal, choose the row/column terminal presentation, build `S+1` post-data,
  prove chart coverage or regularity, compute
  Jacobians, prove normal crossings, extract RLCT, prove termination or
  transition invariance, or repair the printed vector mismatch.
  The displayed weighted terminal-product layer adds supplied old top weights
  `Wold`, supplied old top block `Cold`, residual weights `b0`, `b`, and a
  supplied following suffix `F`. It proves the stopped terminal entry-ideal
  equality
  `<entries((blockdiag(Wold,diag(b0,b))*[Cold;D'''*C'])*F)> =
  <entries([(Wold*Cold)*F;(b0*C0)*F])>`. The suffix `F` is included before
  zero-row deletion, and the pivot-row weight `b0` is retained without a unit
  assumption. This still does not identify `Cold`, `Wold`, or `F` with the
  source old top rows, source diagonal weights, or source remaining product,
  identify the right hand side with `C'^(S+1)`, choose the row/column terminal
  presentation, build `S+1` post-data, prove chart coverage or regularity,
  compute Jacobians, prove normal crossings, extract RLCT, prove termination or
  transition invariance, or repair the printed vector mismatch.
  The displayed source-terminal candidate layer names the source-order weight
  matrix, unweighted `Cnext` stack, and product
  `(blockdiag(Wold,[b0]) * [Cold;C0]) * F`; proves that the product expands to
  `[(Wold*Cold)*F;(b0*C0)*F]`; and combines the supplied displayed source-chart
  `Q/P` identity with stopped terminal absorption under a supplied displayed
  boundary. In the wrapper, `b0` is `post.weight (J+1)`, but `Atop`, `Ctop`,
  and `F` are still supplied. This still does not prove those supplied objects
  are Aoyagi's actual old weights, old top rows, or remaining product, and it
  does not prove `[Ctop;C0]` is source-produced `C'^(S+1)`.
  The displayed terminal source-model layer packages supplied `Atop`, `Ctop`,
  and `F` with actual next-width exhaustion `n(S+1)=J+1`.  It proves failed
  next continuation, the finite introduced-label-domain equality between old
  `(S,J+1)` and stage-relabelled `(S+1,0)`, and the supplied-boundary
  entry-ideal equality to the model's terminal product.  This is not
  recurrence or exponent post-data over `(S+1,0)`, and it still does not prove
  `[Ctop;C0]` is source-produced `C'^(S+1)`.
  The actual-width terminal relabel layer now copies supplied old post-state
  recurrence maps from `(S,J+1)` to `(S+1,0)` and proves `step` and `weight`
  equality under `n(S+1)=J+1`.  It also transports the supplied
  `leastValue = level` invariant and all-label exponent certificates across
  the introduced-label domain equality.  This does not prove chart production,
  source-produced `C'^(S+1)`, automatic Case 2 gap/tail transport, normal
  crossings/RLCT, termination, transition invariance, or printed-vector
  repair.
  The terminal relabel-weight candidate bridge now rewrites the stopped
  supplied terminal product with surviving pivot scalar
  `data.terminalRelabelPost.weight(J+1)`, using actual-width exhaustion to
  recover failed next continuation and the equality with `post.weight(J+1)`.
  A source-model wrapper is specialized to that relabelled scalar, and the
  same scalar rewrite is available for the source old-top/source suffix theorem
  through a supplied terminal `Cterm`.  This is only presentational API and
  does not construct source-produced `C'^(S+1)`.
  The source-chart terminal model constructor composes the concrete displayed
  source-chart boundary with that terminal wrapper.  It fixes
  `post = pre.case2Succ(case2DisplayedSourceChartMap(...)(J+1,J+1))` and the
  corrected selected-label exponent post-data, but still leaves chart-family
  predicates and terminal `Atop`, `Ctop`, `F` supplied.
  The actual-width column-exhaustion fact proves
  `case2DisplayedPivotColComplement_isEmpty_of_width_next_eq` and the
  terminal source-model projection
  `displayedPivotColComplement_isEmpty`; this only identifies the exhausted
  finite side.
  The current-prefix row-exhaustion fact proves
  `case2DisplayedPivotRowComplement_isEmpty_of_prefixMin_current_eq`; this
  only identifies the row side under `prefixMinNat n S=J+1`.
  The source old-top/suffix specialization proves
  `case2SourceOldTopRowIndex`, `case2DisplayedSourceOldTopWeight`,
  `case2DisplayedSourceOldTopBlock`, and
  `Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceDisplayedOldTopSuffixTerminalProduct_entryIdeal_eq_of_not_next_cont`.
  It removes arbitrary old-top data from one stopped terminal theorem, but
  keeps the suffix `F` supplied and does not construct source-produced
  `C'^(S+1)`.
  The source suffix-chain checkpoint proves `paperMatrixChainStep`,
  `paperMatrixChain`, `paperMatrixChain_self`,
  `paperMatrixChain_proof_irrel`, `paperMatrixChain_succ_right`,
  `paperMatrixChain_edge`, `sourceLayerIndex`, `sourceEdgeIndex`,
  `sourceEdgeIndex_castSucc`, `sourceEdgeIndex_succ`, and
  `sourceSuffixProduct` in `MatrixChain.lean`, and
  `Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceDisplayedOldTopSourceSuffixProduct_entryIdeal_eq_of_not_next_cont`
  in `BlowupArithmetic.lean`.  It replaces the abstract supplied suffix in
  the stopped source old-top theorem by Aoyagi's raw right suffix product.
  The source terminal product candidate checkpoint proves
  `matrixEntryIdeal_submatrix_equiv`,
  `case2SourceTerminalRowIndex`, `case2SourceTerminalRowEquiv`,
  `case2SourceTerminalRowEquiv_inl`, `case2SourceTerminalRowEquiv_inr`,
  `case2DisplayedSourceTerminalCprimeCandidate`,
  `case2DisplayedSourceTerminalCprimeCandidate_submatrix_terminalRowEquiv`,
  `matrixEntryIdeal_case2DisplayedSourceTerminalCprimeCandidate_eq_terminalCnext`,
  `pivotQinv_mul_top_apply`,
  `case2DisplayedPaperCprimeTop_apply`,
  `case2DisplayedSourceTerminalWeight`,
  `case2DisplayedSourceTerminalProductReindexedCandidate`,
  `case2DisplayedSourceTerminalProductReindexedCandidate_eq_terminalCprimeCandidate_submatrix`,
  `case2DisplayedSourceTerminalProductReindexedCandidate_eq_weight_mul_cprimeCandidate_mul`,
  `case2SourceTerminalPrefixRowIndex`,
  `case2SourceTerminalRowEquivPrefix`,
  `case2SourceTerminalRowEquivPrefixOfNotNext`,
  `case2DisplayedSourceTerminalCprimeCandidate_oldRow`,
  `case2DisplayedSourceTerminalCprimeCandidate_pivotRow`,
  `SuppliedTerminalCprimeBridge`,
  `case2DisplayedSourceTerminalCprimeCandidate_eq_of_oldRows_pivotRow`,
  `case2DisplayedSourceTerminalProductReindexedCandidate_eq_weight_mul_suppliedCterm_mul`,
  `SuppliedTerminalCprimeBridge.cprimeCandidate_eq`,
  `SuppliedTerminalCprimeBridge.terminalProduct_eq_weight_mul_Cterm_mul`,
  `SuppliedTerminalCprimeBridge.cprimePrefixCandidate_eq`,
  `SuppliedTerminalCprimeBridge.terminalPrefixProduct_eq_weight_mul_CtermPrefix_mul`,
  `case2DisplayedSourceTerminalWeightPrefixCandidate`,
  `case2DisplayedSourceTerminalCprimePrefixCandidate`,
  `case2DisplayedSourceTerminalProductPrefixCandidate`,
  `case2DisplayedSourceTerminalProductPrefixCandidate_eq_weight_mul_cprimePrefixCandidate_mul`,
  `matrixEntryIdeal_sourceTerminalProductPrefixCandidate_eq_sourceTerminalProduct`,
  `matrixEntryIdeal_sourceTerminalProductReindexedCandidate_eq_terminalCprimeCandidate`,
  and
  `Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceOldTopSourceSuffix_entryIdeal_eq_sourceTerminalProduct_of_not_next_cont`,
  `Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceOldTopSourceSuffix_entryIdeal_eq_suppliedTerminalCprimeProduct_of_not_next_cont`,
  `Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceOldTopSourceSuffix_entryIdeal_eq_suppliedTerminalPrefixProduct_of_not_next_cont`,
  `Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceOldTopSourceSuffix_entryIdeal_eq_sourceTerminalPrefixProduct_of_not_next_cont`.
  This reindexes the stopped terminal candidate into one-based source rows and
  terminal prefix rows, proves its product form, expands the top row of
  `Q^-1 C` as `C(J+1,-)` plus the displayed pivot-row sum over post-pivot
  columns, and records the row-equation handoff for a supplied terminal
  matrix. Under actual-width exhaustion `n(S+1)=J+1`, the pivot-column
  complement is empty, so the top row is exactly the original source row
  `C(J+1,-)`. Lean now instantiates `SuppliedTerminalCprimeBridge` with the
  original source rows `1..J+1` and specializes the relabelled
  old-top/source-suffix theorem to those rows. This actual-width specialization
  does not apply to failed continuation, prefix exhaustion, or row-exhausted
  wide-next cases. The bridge is now consumed by both
  the source-row terminal product and the terminal-prefix product, and by the
  stopped source old-top/source suffix theorem in source-row and prefix-row
  form. It does not construct
  source-produced `C'^(S+1)`.
  The row-exhausted branch now has a separate Lean wrapper:
  `prefixMinNat n S=J+1` forces failed next continuation, and the source
  old-top/source suffix theorem is restated with terminal-prefix rows and with
  an explicit transported-row terminal matrix.  In that matrix, row `J+1` is
  the top row of `Q^-1 C`, including possible post-pivot column corrections;
  this row is not identified with the original source row unless the separate
  actual-width hypothesis `n(S+1)=J+1` is available.
  The source-chart terminal source-suffix wrappers now compose the concrete
  displayed source-chart constructor with both stopped branches:
  `exists_sourceChart_oldTopSuffix_entryIdeal_eq_originalRowsProduct_of_actualWidth`
  for actual-width original rows and
  `exists_sourceChart_oldTopSuffix_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted`
  for row-exhausted transported rows.  These wrappers fix the post recurrence
  state to `pre.case2Succ(case2DisplayedSourceChartMap(...)(J+1,J+1))` and
  use corrected selected-label exponent overrides, but still leave
  `chartFamily`, the source following matrix, and the suffix chain supplied.
  They do not prove source-produced `C'^(S+1)`, chart coverage,
  chart-produced post-data, Jacobian arithmetic, normal crossings/RLCT,
  termination, transition invariance, automatic Case 2 gap/tail transport, or
  printed-vector repair.
  The raw paper-order source suffix chain split `paperMatrixChain_trans` is
  now proved in `MatrixChain.lean`; it is raw matrix-chain algebra only and
  does not yet state source-suffix empty or peel wrappers.  The actual-width
  source-chart terminal boundary
  `sourceChart_actualWidth_terminalOriginalRowsBoundary` now packages the
  original-row terminal source-suffix entry-ideal equality with the
  actual-width relabelled level invariant and exponent-domain certificate for
  `(S+1,0)`.  This boundary requires `n(S+1)=J+1` and does not apply to
  row-exhausted wide-next cases.
  The source suffix utility layer now proves
  `sourceSuffixProduct_proof_irrel`,
  `sourceSuffixProduct_eq_paperMatrixChain`, and
  `sourceSuffixProduct_split_at`, exposing the raw suffix as a
  proof-irrelevant paper-order chain that splits at a source layer.  Endpoint
  split identity simplifications remain unproved; the terminal-last
  empty-suffix identity is now the separate
  `sourceSuffixProduct_terminalLast_eq_cast_one` theorem recorded below.  The
  one-edge peel is now Lean-proved as `paperMatrixChain_succ_left`,
  `sourceSuffixFirstEdge`, and `sourceSuffixProduct_peel`: under `S+2<=L`,
  the suffix rewrites as the first source edge `C^(S+2)`, reindexed to
  adjacent source-suffix endpoints, times the tail suffix from `S+3`.
  The stopped terminal source-row wrappers are also now available with an
  arbitrary supplied following matrix `F`, via
  `exists_sourceOldTopSuffix_entryIdeal_eq_sourceTerminalProduct_of_not_next_cont`,
  `exists_sourceOldTopSuffix_entryIdeal_eq_suppliedTerminalCprimeProduct_of_not_next_cont`,
  `exists_oldTopSuffix_entryIdeal_eq_relabelSuppliedTerminalProduct_of_actualWidth`,
  and
  `exists_oldTopSuffix_entryIdeal_eq_relabelOriginalRowsTerminalProduct_of_actualWidth`.
  These wrappers consume supplied suffix/bridge data and keep actual-width
  original-row specialization separate from row-exhausted wide-next cases.
  The concrete displayed source-chart actual-width boundary now has the same
  arbitrary-`F` form as
  `exists_sourceChart_oldTopSuppliedSuffix_entryIdeal_eq_originalRowsProduct_of_actualWidth`
  and `sourceChart_actualWidth_terminalOriginalRowsSuppliedSuffixBoundary`:
  the post recurrence/exponent data are fixed by the displayed source chart,
  while the following matrix `F` remains supplied.
  The displayed source-chart actual-width terminal boundary is now also
  bundled with finite residual-block center principalization as
  `sourceChart_actualWidth_terminalOriginalRowsSuppliedSuffixBoundary_withFiniteCenterIdeal`.
  This adds that the selected variable `u` occurs among the transformed finite
  center values, divides every transformed finite center value, and generates
  the transformed finite center ideal.  It does not principalize the terminal
  product ideal; `F`, `chartFamily`, and actual-width exhaustion remain
  explicit boundaries.
  The raw terminal-last source suffix identity is now proved as
  `sourceLayerIndex_terminalLast` and
  `sourceSuffixProduct_terminalLast_eq_cast_one`: under `S+1=L`, the suffix is
  the empty paper-order chain, with the identity matrix transported along the
  endpoint equality.  This is raw chain algebra and only supports wrappers
  whose following factor is exactly this source suffix.
  The actual-width identity-following boundary is now proved as
  `sourceChart_actualWidth_terminalOriginalRowsIdentityFollowingBoundary`,
  specializing the arbitrary following matrix to `1` while retaining the
  actual-width original-row side condition and relabelled level/exponent
  certificates.  It does not prove source suffix emptiness or row-exhausted
  wide-next terminal data.
  The actual-width terminal-last boundary is now proved as
  `sourceChart_actualWidth_terminalLastOriginalRowsBoundary`, with the entry
  equality factored through `matrixEntryIdeal_mul_sourceSuffixProduct_terminalLast`
  and the raw empty-suffix identity.  It requires both `n(S+1)=J+1` and
  `S+1=L`, consumes the actual source suffix, and packages the relabelled
  level/exponent certificates.  It still does not cover the row-exhausted
  wide-next branch or prove source production, chart coverage, chart-produced
  following products, Jacobian arithmetic, normal crossings/RLCT, termination,
  transition invariance, or printed-vector repair.
  The row-exhausted terminal-last source-suffix removal is now proved as
  `exists_sourceChart_oldTopTerminalLast_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted`,
  with the supplied-boundary companion
  `exists_sourceOldTopTerminalLast_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted`.
  It requires `prefixMinNat n S=J+1` and `S+1=L`, consumes the actual source
  suffix, and keeps the terminal side as transported prefix rows.  It still
  does not identify row `J+1` with the original source row, relabel recurrence
  or exponent data to `(S+1,0)`, or prove source production, chart coverage,
  chart-produced following products, Jacobian arithmetic, normal crossings/RLCT,
  termination, transition invariance, or printed-vector repair.
  The terminal-last actual-width and row-exhausted terminal boundaries are now
  also packaged with finite residual-block center principalization as
  `sourceChart_actualWidth_terminalLastOriginalRowsBoundary_withFiniteCenterIdeal`
  and
  `sourceChart_rowExhausted_terminalLastTransportedPrefixBoundary_withFiniteCenterIdeal`.
  These conjoin the terminal product boundary with the facts that `u` is a
  transformed finite center value, divides all transformed finite center values,
  and generates the transformed finite center ideal.  They do not principalize
  the terminal product ideal or add chart coverage, source production,
  Jacobian arithmetic, normal crossings/RLCT, termination, transition
  invariance, or printed-vector repair.
- **Cited.** none planned.
- **Deferred.** none planned.

## Claim A5 - arithmetic minimisation and pole-order count

- **Statement.** The exponent vectors from the blow-up certificate have minimum
  ratio and multiplicity/order equal to Aoyagi's closed formula.
- **Tier.** Established in Aoyagi; to be proved in Lean.
- **Status.** blocked after independent reproduction check; interior quadratic
  algebra is promising, and the isolated endpoint-corrected Lemma 3 integer
  numerator minimisation, equality-case classification, and equality-count
  over the source interval are now Lean-proved and reviewed.  The elementary
  Lemma 5 interval-excess sum is also Lean-proved and reviewed.  The full A5
  claim remains blocked: terminal-variable restriction, minimiser feasibility,
  the Lemma 4 two-value hypothesis from source vector inequalities,
  vector admissibility/correspondence to `lambda`, quadratic rewrite from
  terminal exponents, and Lemma 5 order-count construction are not checked.
  The finite bridge from Lemma 4's all-increment count to the Lemma 3
  free-count equality cases is now Lean-proved and reviewed at the same narrow
  arithmetic scope.
  The terminal endpoint squeeze used in Lemma 4 is also Lean-proved at the
  finite arithmetic level: the common endpoint for `Htilde_ell` and
  `Htilde'_ell` is zero under Definition 3's selected-width sum, so supplied
  endpoint inequalities imply `H_ell=0`.
  The displayed `Htilde`/`Htilde'` chain arithmetic is now Lean-proved at the
  same finite scope: the high-first and low-first chains start at
  `H_0=M(S_1)`, realise the two ordered increment patterns, share the common
  terminal endpoint, and differ pointwise by the Lemma 5 interval-excess
  formula.
  A same-coordinate interval-bound layer is also Lean-proved: the displayed
  lower chain is pointwise below the upper chain, finite integer value sets
  between them have Aoyagi's interval sizes, supplied same-coordinate chain
  bounds imply `H_ell=0`, and the existing count wrappers apply under the
  still-explicit two-value increment hypothesis.
  The same-coordinate value-set count behind Lemma 5 is now Lean-proved as a
  finite wrapper: the Nat-indexed interval value sets are empty outside range,
  have Aoyagi's interval sizes in range, and satisfy
  `1 + sum_{j=1}^{ell-1}(|I_j|-1)=a(ell-a)+1`.
  A binary prefix-delta bridge is now Lean-proved as a conditional interface
  for the two-value increment blocker: for
  `D_j=P(j)-H_j-j*(M-1)`, the identity
  `F_j=(M-1)+(D_(j+1)-D_j)` holds, so supplied binary deltas imply the
  two-value increment hypothesis.
  The endpoint/count bookkeeping for the same prefix-delta interface is now
  Lean-proved too: `D_0=0`, `D_ell=a`, the deltas telescope, and supplied
  binary deltas have exactly `a` ones and `ell-a` zeroes.
  The same-coordinate vector-bound interface and named binary prefix deltas
  are now also packaged through to the free-count Lemma 3 numerator equality:
  a supplied coordinate map reads `Tlo`, `T`, and `Thi` as the lower chain,
  intermediate chain, and upper chain, while supplied binary deltas provide
  the two-valued increments. This remains conditional and does not prove the
  source vector-to-chain correspondence or Lemma 5.
  The first Lemma 5 displayed-family audit is now recorded. Equations `(3)` and
  `(4)` are not yet source-family theorems; equation `(4)` needs the extra
  own-coordinate guard `j0<=ell-a`, and terminal-zero/legal-label data remain
  missing. Lean proves only the conditional chain arithmetic
  `Htilde'_p-p=Htilde_p` under `p<=a` and `p<=ell-a`.
  A follow-up guard-arithmetic layer now proves that the equation `(4)` tail
  cutoff needs `p+1<=a`, and that `k=Htilde_p+1` label bounds are exactly a
  prefix-crossing condition. Definition 3's selected-width arithmetic now
  discharges that label condition: the previous-prefix estimate gives the
  upper bound, while the tail estimate gives `pM<=P_(p+1)` under `p<=a`.
  Terminal-zero data and full displayed-vector realisation remain open.
  Equation `(3)` guard arithmetic now likewise shows that the special cutoff
  needs `1<=a`, the first upper/lower Htilde gap is `1` only in the interior
  case, and `k=Htilde'_1+1` is label-bounded exactly under the width guards
  `M-1<=W_1+W_2` and `W_1+2<=M`.
  Definition 3's strict selected-width inequality is now used to prove
  `W_i<=M-1` for selected widths. Applying this bound to both the previous
  prefix and the tail after `P_(p+1)` discharges both equation `(4)` label
  bounds `1<=Htilde_p+1<=W_(p+1)` under `1<=p`, `p<=a`.
  The corrected local equation `(4)` package now combines the selected-index
  guard `p+1<=a`, own-coordinate guard `p<=ell-a`, and legal label bounds.
  It remains a local arithmetic package, not a displayed-vector or terminal
  `tilde t=0` theorem.
  A conditional source-vector-facing equation `(4)` certificate now exists:
  supplied selected cutpoints plus supplied branch equations imply the
  own-coordinate value and legal label bounds.  This does not construct the
  vector or prove terminality, coverage, admissibility, or the Case 1(2)
  chart sequence.
  The same supplied equation `(4)` certificate now also has selected-span
  branch-value coverage: every `S_1-1<=S<S_(ell+1)-1` is classified into one
  of the advertised branch values, with the boundary singleton kept separate
  from the strict tail.  This is still conditional branch bookkeeping, not
  vector construction or Lemma 5 order-count coverage.
  A source audit reconfirms that equation `(4)` still cannot be promoted to a
  terminal displayed-vector theorem from the printed text: the Case 1(2) chart
  sequence, repeated gap checks, terminal endpoint convention, and `tilde t=0`
  proof are absent.  Lean now proves only a supplied terminal-endpoint
  boundary: if a future record supplies `T(S_(ell+1)-1)=Htilde'_ell`, then
  that endpoint value is zero.
  The first actual-source-label bridge is also Lean-proved: selected-width
  label bounds for `k=Htilde_p+1` imply `actualWidthLabel` only after explicit
  source-layer range, selected-width/actual-width compatibility, and Nat/Int
  label compatibility are supplied.
- **Kill-condition.** Boundary cases in the dimension vector contradict the
  stated minimiser or pole-order count.
- **Evidence/source.** Aoyagi quadratic exponent expression and Lemmas 3-5,
  PDF pp. 22-27.
- **Pen-and-paper reproduction.** draft at
  `threads/05-arithmetic-tail/reproduction-draft.md`; isolated Lemma 3
  endpoint arithmetic at
  `threads/05-arithmetic-tail/reproduction-lemma3-endpoint-arithmetic-a5.md`;
  equality cases at
  `threads/05-arithmetic-tail/reproduction-lemma3-equality-cases-a5.md`;
  equality count at
  `threads/05-arithmetic-tail/reproduction-lemma3-equality-count-a5.md`;
  Lemma 4 two-value count at
  `threads/05-arithmetic-tail/reproduction-lemma4-two-value-count-a5.md`;
  Lemma 4 source sum bridge at
  `threads/05-arithmetic-tail/reproduction-lemma4-sum-bridge-a5.md`;
  Lemma 4 free-count bridge at
  `threads/05-arithmetic-tail/reproduction-lemma4-free-count-bridge-a5.md`;
  Lemma 4 endpoint squeeze at
  `threads/05-arithmetic-tail/reproduction-lemma4-endpoint-squeeze-a5.md`;
  Lemma 4 same-coordinate bridge at
  `threads/05-arithmetic-tail/reproduction-lemma4-same-coordinate-bridge-a5.md`;
  `Htilde` chain arithmetic at
  `threads/05-arithmetic-tail/reproduction-htilde-chain-arithmetic-a5.md`;
  `Htilde` interval bounds at
  `threads/05-arithmetic-tail/reproduction-htilde-interval-bounds-a5.md`;
  Lemma 4 binary prefix delta at
  `threads/05-arithmetic-tail/reproduction-lemma4-binary-prefix-delta-a5.md`;
  Lemma 4 prefix-delta endpoint count at
  `threads/05-arithmetic-tail/reproduction-lemma4-prefix-delta-endpoint-count-a5.md`;
  Lemma 4 same-coordinate binary-delta free count at
  `threads/05-arithmetic-tail/reproduction-lemma4-same-coordinate-binary-delta-free-count-a5.md`;
  Lemma 5 displayed-family blocker audit at
  `threads/05-arithmetic-tail/blocked-audit-lemma5-displayed-family-realisation-a5.md`;
  Lemma 5 equation `(4)` own-coordinate sanity at
  `threads/05-arithmetic-tail/reproduction-lemma5-eq4-own-coordinate-a5.md`;
  Lemma 5 equation `(4)` guard arithmetic at
  `threads/05-arithmetic-tail/reproduction-lemma5-eq4-guard-arithmetic-a5.md`;
  Lemma 5 equation `(3)` guard arithmetic at
  `threads/05-arithmetic-tail/reproduction-lemma5-eq3-guard-arithmetic-a5.md`;
  Definition 3 selected-width upper label bound at
  `threads/05-arithmetic-tail/reproduction-definition3-selected-width-upper-label-a5.md`;
  Lemma 5 interval-excess arithmetic at
  `threads/05-arithmetic-tail/reproduction-lemma5-interval-excess-a5.md`;
  `Htilde` value-set count at
  `threads/05-arithmetic-tail/reproduction-htilde-value-set-count-a5.md`;
  selected-span equation `(4)` branch values at
  `threads/05-arithmetic-tail/reproduction-lemma5-eq4-selected-span-branch-value-a5.md`;
  terminal endpoint boundary at
  `threads/05-arithmetic-tail/reproduction-lemma5-eq4-terminal-endpoint-boundary-a5.md`;
  actual-width label bridge at
  `threads/05-arithmetic-tail/reproduction-lemma5-eq4-actual-width-label-a5.md`.
- **Reproduction check.** failed/blocked at
  `threads/05-arithmetic-tail/reproduction-check.md`; isolated Lemma 3
  endpoint arithmetic checked by xhigh `Lorentz the 5th` and recorded at
  `threads/05-arithmetic-tail/review-lemma3-endpoint-arithmetic-a5.md`;
  equality cases checked by xhigh `Epicurus the 5th` and xhigh Lean scout
  `Dalton the 5th` at
  `threads/05-arithmetic-tail/review-lemma3-equality-cases-a5.md`;
  equality count checked by xhigh `Lagrange the 5th` and xhigh Lean scout
  `Leibniz the 5th` at
  `threads/05-arithmetic-tail/review-lemma3-equality-count-a5.md`;
  Lemma 4 two-value count checked by xhigh `Hume the 5th` and xhigh Lean scout
  `Chandrasekhar the 5th` at
  `threads/05-arithmetic-tail/review-lemma4-two-value-count-a5.md`;
  Lemma 4 source sum bridge checked by xhigh `Dewey the 5th` at
  `threads/05-arithmetic-tail/review-lemma4-sum-bridge-a5.md`;
  Lemma 4 free-count bridge checked by xhigh `Arendt the 5th` and xhigh Lean
  scout `Banach the 5th` at
  `threads/05-arithmetic-tail/review-lemma4-free-count-bridge-a5.md`;
  Lemma 4 endpoint squeeze checked by xhigh `Parfit the 5th`, xhigh Lean
  scout `Galileo the 5th`, and final xhigh landed-patch reviewer
  `Ramanujan the 5th` at
  `threads/05-arithmetic-tail/review-lemma4-endpoint-squeeze-a5.md`;
  Lemma 4 same-coordinate bridge checked by xhigh `Cicero the 5th` and xhigh
  Lean scout `Jason the 5th` at
  `threads/05-arithmetic-tail/review-lemma4-same-coordinate-bridge-a5.md`;
  `Htilde` chain arithmetic checked by xhigh source checker
  `Schrodinger the 5th` and xhigh Lean scout `Halley the 5th`; final landed
  review pending at
  `threads/05-arithmetic-tail/review-htilde-chain-arithmetic-a5.md`;
  `Htilde` interval bounds checked by xhigh source checker
  `Nietzsche the 5th` and xhigh Lean scout `McClintock the 5th`; final landed
  review pending at
  `threads/05-arithmetic-tail/review-htilde-interval-bounds-a5.md`;
  Lemma 4 binary prefix delta checked by xhigh `Einstein the 5th`; final
  landed review pending at
  `threads/05-arithmetic-tail/review-lemma4-binary-prefix-delta-a5.md`;
  Lemma 4 prefix-delta endpoint count checked by xhigh `Linnaeus the 5th`;
  final landed review pending at
  `threads/05-arithmetic-tail/review-lemma4-prefix-delta-endpoint-count-a5.md`;
  Lemma 4 same-coordinate binary-delta free count checked by xhigh `Raman` at
  `threads/05-arithmetic-tail/review-lemma4-same-coordinate-binary-delta-free-count-a5.md`;
  Lemma 5 interval-excess arithmetic checked by xhigh `Confucius the 5th`
  and xhigh Lean scout `Maxwell the 5th` at
  `threads/05-arithmetic-tail/review-lemma5-interval-excess-a5.md`;
  `Htilde` value-set count checked by xhigh `Plato the 5th` and final landed
  xhigh reviewer `Goodall the 5th` at
  `threads/05-arithmetic-tail/review-htilde-value-set-count-a5.md`;
  selected-span equation `(4)` branch values checked by xhigh source/indexing
  scout `Copernicus` and xhigh Lean/API scout `Beauvoir` at
  `threads/05-arithmetic-tail/review-lemma5-eq4-selected-span-branch-value-a5.md`;
  terminal endpoint boundary/source gap checked by xhigh source audit `Kuhn`
  and xhigh Lean/API audit `Hilbert` at
  `threads/05-arithmetic-tail/review-lemma5-eq4-terminal-endpoint-boundary-a5.md`;
  actual-width label bridge checked by xhigh `Ohm` at
  `threads/05-arithmetic-tail/review-lemma5-eq4-actual-width-label-a5.md`.
- **Lean target.** isolated Lemma 3 endpoint arithmetic in
  `lean/DLNFibre/DLN/Aoyagi/ArithmeticTail.lean`; isolated Lemma 4 two-value
  count arithmetic in `lean/DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`;
  source `H`-bookkeeping sum bridge in
  `lean/DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`;
  finite Lemma 4 free-count bridge to Lemma 3 equality cases in
  `lean/DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`;
  terminal endpoint squeeze wrappers in
  `lean/DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`;
  same-coordinate vector-squeeze wrappers in
  `lean/DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`;
  displayed `Htilde`/`Htilde'` chain arithmetic in
  `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`;
  same-coordinate `Htilde` interval bounds, interval value sets, and
  chain-bound count wrappers in
  `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`;
  binary prefix-delta bridge for the two-value increment hypothesis in
  `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`;
  endpoint and binary-delta count bookkeeping for the prefix-delta interface in
  `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`;
  same-coordinate `Htilde` value-set count in
  `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`;
  same-coordinate vector-bound and binary-delta free-count wrapper in
  `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`;
  Lemma 5 equation `(4)` own-coordinate sanity in
  `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`;
  Lemma 5 equation `(4)` guard arithmetic in
  `lean/DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean` and
  `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`;
  Lemma 5 equation `(3)` guard arithmetic in
  `lean/DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean` and
  `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`;
  Definition 3 selected-width upper label bound in
  `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`;
  isolated Lemma 5 interval-excess arithmetic in
  `lean/DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean`;
  conditional equation `(4)` selected-span branch classification in
  `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`;
  conditional equation `(4)` terminal endpoint boundary in
  `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean` and
  `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`;
  actual-width source-label bridge in
  `lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`; broader A5 targets TBD.
- **Proved.** `aoyagiLemma3A`, `aoyagiLemma3A_eq_min_add`,
  `int_mul_succ_nonneg`, `aoyagiLemma3A_min_le`,
  `aoyagiLemma3A_at_right`, `aoyagiLemma3A_at_left`,
  `aoyagiLemma3A_eq_min_iff`, `aoyagiLemma3A_eq_min_iff_source_Icc`,
  `aoyagiLemma3A_eq_min_iff_source_Icc_zero`,
  `aoyagiLemma3A_eq_min_iff_source_Icc_top`,
  `aoyagiLemma3AMinimizerSet`, `aoyagiLemma3AMinimizerSet_eq_zero`,
  `aoyagiLemma3AMinimizerSet_eq_top`,
  `aoyagiLemma3AMinimizerSet_eq_interior`,
  `aoyagiLemma3AMinimizerSet_card_zero`,
  `aoyagiLemma3AMinimizerSet_card_top`,
  `aoyagiLemma3AMinimizerSet_card_interior`,
  `aoyagiLemma3AMinimizerSet_card`,
  `aoyagiLemma3A_isLeast_image_Icc`,
  `aoyagiLemma3A_isLeast_image_Icc_zero`, and
  `aoyagiLemma3A_isLeast_image_Icc_top`.  These prove only the cleared
  integer numerator identity and endpoint-corrected constrained minimum over
  integer `b`, plus exact equality cases and the endpoint-corrected count for
  that isolated lower bound.  Also proved
  `aoyagiLemma5IntervalExcess`, `aoyagiLemma5IntervalSize`,
  `aoyagiLemma5IntervalExcessFiber`,
  `aoyagiLemma5IntervalExcessFiber_eq_Ico_card`,
  `aoyagiLemma5IntervalExcessFiber_eq_excess`,
  `aoyagiLemma5IntervalExcessFiber_sum_range`,
  `aoyagiLemma5IntervalExcess_sum_range`,
  `aoyagiLemma5IntervalExcess_zero`, `aoyagiLemma5IntervalExcess_top`,
  `aoyagiLemma5IntervalExcess_sum_Icc`, and
  `aoyagiLemma5IntervalSize_excess_sum_Icc`.  These prove only finite
  interval-excess arithmetic, not Lemma 5's chart-family/order-count theorem.
  Also proved `twoStepInt_count_eq`, `aoyagiLemma4_twoValueCount_int`, and
  `aoyagiLemma4_twoValueCount_le_ell`, which prove finite two-value count
  arithmetic under a sum identity.  The source sum bridge is now proved as
  `aoyagiLemma4F`, `aoyagiLemma4F_sum_eq_selectedSum`,
  `aoyagiLemma4F_sum_eq_of_selectedSum_eq_pred_add_a`,
  `aoyagiLemma4_twoValueCount_of_terminalH`, and
  `aoyagiLemma4_twoValueCount_of_terminalH_le_ell`: with the convention
  `H_0=M(S_1)` and terminal condition `H_ell=0`, the increments telescope to
  the selected-width sum, and the two-value count follows without assuming
  `sum F_j=ell*(M-1)+a` directly.
  Also proved `highCount_castSucc_add_last_eq_total`,
  `highCount_castSucc_int_eq_or_eq_pred_of_total`,
  `aoyagiLemma4_freeHighCount_lemma3A_eq_min_of_totalCount`, and
  `aoyagiLemma4_terminalH_freeHighCount_lemma3A_eq_min`, which split the
  all-increment count into a free first-`ell-1` count plus the last increment
  and feed the resulting integer equality case into the isolated Lemma 3
  numerator theorem.
  Also proved `aoyagiLemma4TerminalEndpoint`,
  `aoyagiLemma4TerminalEndpoint_eq_zero_of_selectedSum`,
  `aoyagiLemma4_Hlast_eq_zero_of_terminalEndpoint_bounds`,
  `aoyagiLemma4_twoValueCount_of_terminalEndpointBounds`, and
  `aoyagiLemma4_terminalEndpointBounds_freeHighCount_lemma3A_eq_min`, which
  replace an explicit terminal condition `H_ell=0` by supplied endpoint
  inequalities around the displayed terminal endpoints.
  Also proved `aoyagiLemma4_terminalEndpointBounds_of_sameCoordinate`,
  `aoyagiLemma4_Hlast_eq_zero_of_sameCoordinate`,
  `aoyagiLemma4_twoValueCount_of_sameCoordinate`, and
  `aoyagiLemma4_sameCoordinate_freeHighCount_lemma3A_eq_min`, which replace
  supplied endpoint inequalities by explicit same-coordinate componentwise
  vector bounds.  A source-gap check shows that Aoyagi's Definition 4 alone
  does not supply this same-coordinate correspondence.
  Also proved `aoyagiSelectedWidthNat`, `aoyagiPrefixSum`,
  `aoyagiHtildeLowerChain`, `aoyagiHtildeUpperChain`,
  `aoyagiHtildeLowerChain_zero`, `aoyagiHtildeUpperChain_zero`,
  `aoyagiHtildeLowerIncrementPrefix_succ_sub`,
  `aoyagiHtildeUpperIncrementPrefix_succ_sub`,
  `aoyagiHtildeLowerChain_last_eq_terminalEndpoint`,
  `aoyagiHtildeUpperChain_last_eq_terminalEndpoint`,
  `aoyagiHtildeLowerChain_F_eq`, `aoyagiHtildeUpperChain_F_eq`,
  `aoyagiHtildeHighCount_diff_eq_intervalExcess`, and
  `aoyagiHtildeUpper_sub_lower_eq_intervalExcess`, which formalise the
  displayed high-first and low-first `Htilde` chains and their pointwise
  interval-excess gap.
  Also proved `aoyagiHtildeLowerChain_last_eq_zero_of_selectedSum`,
  `aoyagiHtildeUpperChain_last_eq_zero_of_selectedSum`,
  `aoyagiHtildeLowerChain_le_upperChain`, `aoyagiHtildeIntervalOffsets`,
  `aoyagiHtildeIntervalOffsets_card`, `aoyagiHtildeIntervalValueSet`,
  `aoyagiHtilde_mem_intervalValueSet_iff_bounds`,
  `aoyagiHtildeIntervalValueSet_card`,
  `aoyagiHtildeChainBounds_mem_intervalValueSet`,
  `aoyagiHtilde_interval_mem_of_sameCoordinateChain`,
  `aoyagiLemma4_Hlast_eq_zero_of_HtildeChainBounds`,
  `aoyagiHtildeLowerChain_F_twoValue`,
  `aoyagiHtildeUpperChain_F_twoValue`,
  `aoyagiLemma4_twoValueCount_of_HtildeChainBounds`,
  `aoyagiLemma4_HtildeChainBounds_freeHighCount_lemma3A_eq_min`,
  `aoyagiHtildeLowerChain_twoValueCount`, and
  `aoyagiHtildeUpperChain_twoValueCount`, which provide finite
  same-coordinate interval membership and conditional count wrappers without
  deriving arbitrary-vector two-valued increments.
  Also proved `aoyagiLemma4IncrementPrefix`,
  `aoyagiLemma4F_eq_pred_add_incrementPrefixDelta`,
  `aoyagiLemma4F_twoValue_of_binaryIncrementPrefix`,
  `aoyagiLemma4_twoValueCount_of_terminalH_binaryIncrementPrefix`, and
  `aoyagiLemma4_twoValueCount_of_HtildeChainBounds_binaryIncrementPrefix`,
  which turn supplied binary prefix deltas into the Lemma 4 two-value
  increment hypothesis and count wrappers.
  Also proved `aoyagiLemma4IncrementPrefixDelta`,
  `aoyagiLemma4F_eq_pred_add_incrementPrefixDelta_def`,
  `aoyagiLemma4IncrementPrefix_zero_of_H0`,
  `aoyagiLemma4IncrementPrefix_last_eq_a_of_terminalH`,
  `aoyagiLemma4IncrementPrefixDelta_sum_eq_last_sub_zero`,
  `aoyagiLemma4IncrementPrefixDelta_sum_eq_a_of_terminalH`,
  `aoyagiLemma4_binaryIncrementPrefix_count_eq`, and
  `aoyagiLemma4_binaryIncrementPrefix_count_eq_of_HtildeChainBounds`, which
  count supplied binary prefix deltas under terminal source hypotheses or
  same-coordinate chain-bound hypotheses.
  Also proved `aoyagiLemma4F_twoValue_of_binaryIncrementPrefixDelta` and
  `aoyagiLemma4_sameCoordinateChain_binaryIncrementPrefixDelta_freeHighCount_lemma3A_eq_min`,
  which package supplied same-coordinate vector bounds and supplied binary
  prefix deltas into the free-count Lemma 3 numerator equality.
  Also proved `aoyagiHtildeUpperChain_sub_index_eq_lowerChain_of_le_min` and
  `aoyagiHtildeUpperNat_sub_index_eq_lowerNat_of_le_min`, which prove the
  equation `(4)` own-coordinate arithmetic sanity under the extra overlap
  guard `p<=ell-a`.
  Also proved `aoyagiHtildeIntervalValueSetNat`,
  `aoyagiHtildeIntervalValueSetNat_card_of_lt`,
  `aoyagiHtildeIntervalValueSetNat_card`, and
  `aoyagiHtildeIntervalValueSetNat_excess_sum_Icc`, which package the
  same-coordinate interval value sets into a Nat-indexed source-facing count
  and recover `1 + sum_{j=1}^{ell-1}(|I_j|-1)=a(ell-a)+1` without proving
  Lemma 5's chart-family/order-count theorem.
  Also proved `AoyagiSelectedCutpoints.block_leftEndpoint_lt_of_ne`,
  `AoyagiSelectedCutpoints.leftEndpoint_lt_of_lt_block`,
  `AoyagiLemma5Eq4SelectedSpanBranchValue`,
  `aoyagiLemma5Eq4_boundaryIndex_le_ell_of_piecewiseSourceVector`,
  `aoyagiLemma5Eq4_boundaryIndex_lt_ell_iff`,
  `aoyagiLemma5Eq4_boundaryIndex_eq_ell_iff`,
  `aoyagiLemma5Eq4_boundaryEndpoint_mem_block_of_strictGuard`,
  `aoyagiLemma5Eq4_boundaryEndpoint_mem_selectedSpan_of_strictGuard`,
  `aoyagiLemma5Eq4_boundaryEndpoint_eq_terminal_of_predBoundary`,
  `aoyagiLemma5Eq4_boundaryEndpoint_not_block_of_predBoundary`,
  `aoyagiLemma5Eq4_branchValue_of_block`, and
  `aoyagiLemma5Eq4_selectedSpan_branchValue`, which classify selected-span
  points into the supplied equation `(4)` branch values.  The supplied
  equation `(4)` certificate now carries the source-boundary guards `a<=ell`
  and `p+1<=a`, and Lean records `p+(ell-a)+1<=ell`; this prevents the
  displayed boundary from being treated as source-valid only through the
  totalized `point` fallback.  Lean also splits the boundary: under `p+1<a`
  it is the left endpoint of the next selected block and lies in the
  half-open selected span, while under `p+1=a` it is the terminal selected
  endpoint and not in any selected block.  This still does not construct the
  displayed vector or prove terminal/chart/order-count claims.
  Also proved `aoyagiHtildeLowerNat_last_eq_zero_of_selectedSum`,
  `aoyagiHtildeUpperNat_last_eq_zero_of_selectedSum`,
  `AoyagiSelectedCutpoints.not_block_terminalEndpoint`,
  `aoyagiLemma5Eq4_prefix_leftEndpoint`,
  `aoyagiLemma5Eq4_middle_leftEndpoint`,
  `aoyagiLemma5Eq4_tail_leftEndpoint_of_cutoff_lt`, and
  `aoyagiLemma5Eq4_terminalEndpoint_zero_of_upperNatExtension`, which package
  terminal endpoint and branch-left-endpoint consequences under supplied data,
  without proving a terminal displayed vector.
  Also proved
  `aoyagiLemma5Eq4_terminalExtension_forces_lastWidth_of_predBoundary` and
  `aoyagiLemma5Eq4_no_terminalExtension_of_lastWidth_ne_predBoundary`, which
  show that in the terminal-collision case `p+1=a`, adding a supplied
  terminal extension `T(S_(ell+1)-1)=Htilde'_ell` forces the extra last-width
  compatibility `W_(ell+1)=M-p+1`, and failure of that compatibility rules
  out the supplied extension.  This still does not prove the terminal
  convention from Aoyagi's printed display.
  Also proved `aoyagiLemma5Eq4_actualWidthLabel_of_widthCompatibility`, which
  turns equation `(4)`'s selected-width label bounds into `actualWidthLabel`
  under explicit source-layer range, selected-width/actual-width compatibility,
  and Nat/Int label compatibility hypotheses.
  Also proved `aoyagiLemma5Eq3_localData_of_widthGuards`,
  `aoyagiHtildeUpperNat_one_add_one_labelBounds_of_sourceSelectedInequality_and_slack`,
  `aoyagiLemma5Eq3_slack_not_forced_by_selectedWidthHypotheses_example`,
  `aoyagiLemma5Eq3_localData_of_sourceSelectedInequality_and_slack`,
  `aoyagiLemma5Eq3_actualWidthLabel_of_widthCompatibility`, and
  `aoyagiLemma5Eq3_actualWidthLabel_of_sourceSelectedInequality_and_slack`,
  which package equation `(3)`'s local selected-index/gap/label arithmetic and
  actual-label bridge while keeping the missing slack `W_1+2<=M` explicit.
  The closed example `ell=3`, `a=2`, `M=3`, all selected widths `2`, satisfies
  the selected-sum and strict selected-width inequalities while failing both
  that slack and the upper selected-label bound.
  Also proved `AoyagiLemma5Eq3PiecewiseSourceVector`,
  `AoyagiLemma5Eq3SelectedSpanBranchValue`,
  `aoyagiLemma5Eq3_branchValue_of_block`,
  `aoyagiLemma5Eq3_selectedSpan_branchValue`, and
  `aoyagiLemma5Eq3_piecewise_ownCoordinate_of_sourceSelectedInequality_and_slack`,
  which classify supplied equation `(3)` branch data on the selected span and
  recover the own-coordinate selected-label handoff under explicit slack.
  Also proved
  `aoyagiLemma5Eq3_boundaryIndex_le_ell_of_piecewiseSourceVector`,
  `aoyagiLemma5Eq3_boundaryIndex_lt_ell_iff`,
  `aoyagiLemma5Eq3_boundaryEndpoint_mem_block_of_two_le`,
  `aoyagiLemma5Eq3_boundaryEndpoint_mem_selectedSpan_of_two_le`,
  `aoyagiLemma5Eq3_boundaryEndpoint_mem_selectedSpan_iff_two_le`,
  `aoyagiLemma5Eq3_boundaryEndpoint_eq_terminal_of_one`,
  `aoyagiLemma5Eq3_boundaryEndpoint_not_block_of_one`,
  `aoyagiLemma5Eq3_terminalEndpoint_one_of_one`, and
  `aoyagiLemma5Eq3_no_terminalEndpointZero_of_one`, which split equation
  `(3)`'s special boundary into the ordinary selected-span case `2<=a` and
  the terminal endpoint case `a=1`; in the terminal case the supplied branch
  assignment gives value `1` and rules out a simultaneous endpoint value zero.
  Also proved `aoyagiLemma5Eq3_boundaryValue_gt_upperNat`,
  `aoyagiLemma5Eq3_boundaryValue_not_mem_intervalValueSetNat`, and
  `aoyagiLemma5Eq3_boundaryValue_not_mem_intervalValueSetNat_of_two_le`, which
  show that the supplied equation `(3)` boundary value is one unit above the
  same-coordinate interval at coordinate `ell-a+1`; in the strict case `2<=a`,
  this selected-span singleton is outside the interval-value family counted by
  the `Htilde` arithmetic layer.
  Also proved `aoyagiHtildeUpperNat_pred_eq_sub_lastWidth_of_selectedSum`,
  `aoyagiLemma5Eq4_lastWidthCompatibility_not_forced_by_selectedWidthHypotheses_example`,
  `aoyagiLemma5Eq4_terminalEndpoint_value_of_predBoundary`, and
  `aoyagiLemma5Eq4_terminalEndpoint_zero_iff_lastWidth_of_predBoundary`, which
  record the supplied equation `(4)` terminal-collision boundary value and the
  exact extra last-width condition for it to be zero.  The concrete example
  `ell=3`, `a=2`, `p=1`, `M=3`, all selected widths `2`, satisfies the
  selected-sum and strict selected-width inequalities while failing that
  condition.
  Also proved
  `aoyagiLemma5Eq4_no_terminalUpperNatExtension_of_p1_sourceSelectedInequality`,
  which strengthens the terminal-extension obstruction in the `p=1`
  terminal-collision case: Definition 3's selected-width hypotheses force
  `W_(ell+1)<=M-1`, while a supplied terminal upper-chain extension would
  force `W_(ell+1)=M`.
  Also proved
  `aoyagiLemma5Eq4_terminalExtension_forces_two_le_p_of_sourceSelected`
  and
  `aoyagiLemma5Eq4_no_terminalExtension_of_sourceSelected_of_p_lt_two`,
  which give the general terminal-extension necessary condition: such an
  extension forces `2<=p`, and `p<2` rules it out.  The `p=0` edge is a
  Lean-totalized supplied-certificate consequence, not an additional printed
  source case.
  Also proved
  `aoyagiLemma5Eq4_terminalEndpoint_values_ell3_a2_p1_allWidthsTwo` and
  `aoyagiLemma5Eq4_no_terminalUpperNatExtension_ell3_a2_p1_allWidthsTwo`,
  which combine that concrete tuple with the supplied terminal-extension
  obstruction: any supplied equation `(4)` certificate for the tuple has
  terminal-collision branch value `1` while `Htilde'_ell=0`, and is therefore
  incompatible with the supplied terminal upper-chain extension
  `T(S_(ell+1)-1)=Htilde'_ell`.  This does not construct the certificate or a
  terminal extension.
  Also proved
  `aoyagiHtildeUpperNat_succ_eq_add_selectedWidthNat_sub_increment`,
  `aoyagiLemma5Eq4_boundaryCoordinate_intervalExcess_eq_min`,
  `aoyagiLemma5Eq4_boundaryValue_sub_upperNat_boundaryCoordinate`,
  `aoyagiLemma5Eq4_boundaryValue_mem_boundaryCoordinateIntervalValueSetNat_iff_widthWindow`,
  `aoyagiLemma5Eq4_boundaryValue_mem_boundaryCoordinateIntervalValueSetNat_iff_widthWindow_min`,
  `aoyagiLemma5Eq4_boundaryValue_gt_boundaryUpper_of_p1_sourceSelected`, and
  `aoyagiLemma5Eq4_boundaryValue_not_mem_boundaryInterval_of_p1_sourceSelected`,
  which classify the strict equation `(4)` boundary value against its own
  boundary-coordinate interval and rule out boundary-coordinate membership in
  the source-selected special case `p=1`.
  Also proved
  `aoyagiLemma5Eq4_boundaryValue_mem_boundaryInterval_forces_two_le_p_of_sourceSelected`
  and
  `aoyagiLemma5Eq4_boundaryValue_not_mem_boundaryInterval_of_sourceSelected_of_p_lt_two`,
  which generalize the source-selected obstruction to a necessary condition:
  boundary-coordinate membership forces `2<=p`, so `p<2` rules out
  membership.  This does not assert membership for `p>=2`.
  Also proved
  `aoyagiLemma5Eq4_boundaryValue_mem_boundaryInterval_p2_constantWidth_example`,
  and
  `aoyagiLemma5Eq4_boundaryValue_mem_boundaryInterval_p2_constantWidth_sourceSelected_example`,
  which supply a concrete `p=2` constant-width guardrail: the tuple
  `ell=5`, `a=4`, `p=2`, `M=5`, and all selected widths equal to `4`
  satisfies the selected-width sum and strict inequalities, and any supplied
  equation `(4)` certificate for it has the boundary value in the
  boundary-coordinate interval.  This does not construct the supplied
  certificate or displayed vector.
  Also proved `AoyagiLemma5Eq5OwnCoordinateBranch`,
  `aoyagiLemma5Eq5OffsetValueSet`,
  `aoyagiLemma5Eq5_offsetValue_injective`,
  `aoyagiLemma5Eq5OffsetValueSet_card`,
  `aoyagiLemma5Eq5OffsetValueSet_subset_intervalValueSetNat`,
  `aoyagiLemma5Eq5_ownCoordinate_value`,
  `aoyagiLemma5Eq5_ownCoordinate_eq_label_pred`,
  `aoyagiLemma5Eq5_ownCoordinate_mem_intervalValueSetNat`, and
  `aoyagiLemma5Eq5_ownCoordinate_mem_offsetValueSet`, which give the first
  supplied equation `(5)` own-coordinate offset slice.  With paper `j0`
  represented by Lean coordinate `p`, the own block value is
  `Htilde'_p-alpha`; under the supplied label relation
  `k=Htilde'_p+1-alpha`, this is `k-1`; and under
  `alpha<=Htilde'_p-Htilde_p`, it lies in the same-coordinate interval.  The
  finite offset-value set has cardinality `min(excess(ell,a,p),p-1)`.  This
  still does not construct equation `(5)`'s displayed vector, prove
  source-label legality, classify the selected span, prove terminal
  `tilde t=0`, build the chart sequence, or prove Lemma 5.
  Also proved `AoyagiLemma5Eq5PiecewiseSourceVector`,
  `AoyagiLemma5Eq5SelectedSpanBranchValue`,
  `aoyagiLemma5Eq5_branchValue_of_block`,
  `aoyagiLemma5Eq5_selectedSpan_branchValue`, and
  `aoyagiLemma5Eq5_ownCoordinateBranch_of_piecewiseSourceVector`, which extend
  equation `(5)` to a supplied piecewise branch certificate and selected-span
  classifier.  The full supplied certificate implies the previous narrow
  own-coordinate branch record, but still does not construct the displayed
  vector, prove source-label legality, prove terminal `tilde t=0`, build the
  chart sequence, or prove Lemma 5.
  Also proved
  `aoyagiHtildeLowerIncrementPrefix_le_prefixSum_of_selectedWidth_le_pred`,
  `aoyagiHtildeLowerNat_add_one_pos_any_of_sourceSelectedInequality`,
  `aoyagiPrefixSum_sub_current_le_mul_pred_of_selectedWidth_le_pred`,
  `aoyagiHtildeUpperNat_le_selectedWidth_of_selectedWidth_le_pred`,
  `aoyagiHtildeUpperNat_le_selectedWidth_of_sourceSelectedInequality`,
  `aoyagiLemma5Eq5_labelBounds_of_sourceSelectedInequality`,
  `aoyagiLemma5Eq5_actualWidthLabel_of_widthCompatibility`, and
  `aoyagiLemma5Eq5_piecewise_ownCoordinate_actualWidthLabel`, which prove
  equation `(5)`'s own-coordinate source-label legality under Definition 3
  selected-width hypotheses, the supplied offset guard
  `1<=alpha<=excess(ell,a,p)`, and explicit actual-width compatibility at
  `C.point p-1`.  The piecewise wrapper also combines this with the value
  rewrite `T(C.point p-1)=k-1`.  This still does not construct the displayed
  vector, prove arbitrary-point label legality across the whole block, prove
  terminal `tilde t=0`, build the chart sequence, or prove Lemma 5.
  Also proved `aoyagiLemma5Eq5_actualWidthLabel_at_of_widthCompatibility` and
  `aoyagiLemma5Eq5_piecewise_ownCoordinate_actualWidthLabel_of_block`, which
  remove the left-endpoint restriction: for arbitrary `S`, explicit source
  range and actual-width compatibility `n(S+1)=W_p` give
  `actualWidthLabel L n S k`; with `C.block p S` and a supplied Eq5 piecewise
  certificate, Lean also proves `T(S)=k-1`.  This still does not prove the
  actual-width compatibility itself, construct the displayed vector, prove
  terminal `tilde t=0`, build the chart sequence, or prove Lemma 5.
  Also proved `aoyagiLemma5Eq5_sourceIndex_pos_of_ownBlock` and
  `aoyagiLemma5Eq5_piecewise_ownCoordinate_actualWidthLabel_of_ownBlock_widthCompatibility`,
  deriving the lower source-range hypothesis `1<=S` from Eq5's
  `1<=alpha<p` guards and `C.block p S`, while keeping `S<=L` and
  `n(S+1)=W_p` explicit.
  Also proved selected-cutpoint source-range helpers
  `AoyagiSelectedCutpoints.selectedSpan_sourceIndex_le_of_terminalEndpoint_le`,
  `AoyagiSelectedCutpoints.selectedSpan_sourceIndex_le_of_lastPoint_le`,
  `AoyagiSelectedCutpoints.block_sourceIndex_le_of_terminalEndpoint_le`, and
  `AoyagiSelectedCutpoints.block_sourceIndex_le_of_lastPoint_le`, plus the
  Eq5 width-bound wrappers
  `aoyagiLemma5Eq5_actualWidthLabel_at_of_widthBound`,
  `aoyagiLemma5Eq5_piecewise_block_actualWidthLabel_of_widthBound`,
  `aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_widthBound`,
  `aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthCompatibility`,
  and
  `aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthBound`.
  These derive `S<=L` from `C.block p S` and `C.point ell<=L+1`, and weaken
  the arbitrary-block width side from equality `n(S+1)=W_p` to the sufficient
  bound `W_p<=n(S+1)`.  They still do not prove that width bound from
  Definition 3 or construct the displayed Eq5 vector.
  Also proved `AoyagiSelectedCutpoints.block_sourceLayer_mem_Ico`,
  `AoyagiSelectedCutpoints.block_sourceLayer_eq_left_or_between`,
  `AoyagiSelectedCutpoints.point_ne_of_between_adjacent`,
  `AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block`,
  `AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block_of_leftEndpoint_min`,
  `AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block_of_offSelected`,
  `AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block_of_offSelected_lt`,
  `aoyagiLemma5Eq5_ownBlock_actualWidthLabel_of_lastPoint_blockWidth`,
  `aoyagiLemma5Eq5_ownBlock_actualWidthLabel_of_lastPoint_leftMin`,
  `aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_offSelected`,
  and
  `aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_offSelected_lt`.
  These derive the width bound from explicit block-local width dominance,
  left-endpoint-minimum data, or index-level off-selected dominance.  They do
  not derive it from Definition 3 alone; the source check records a
  duplicate-width obstruction to that stronger claim.
  Also proved the closed guardrail
  `aoyagiLemma5Eq5_blockWidthBound_not_forced_by_selectedWidthHypotheses_example`.
  It packages the duplicate-width obstruction with selected cutpoint
  compatibility and the value-level non-selected condition: selected cutpoints
  `1,3,5,7`, selected widths `1,2,2,2`, and actual width `n(6)=1` satisfy the
  Definition 3-shaped selected-width data, but fail `W_p<=n(S+1)` for
  `p=2`, `S=5`.  This is a guardrail for the explicit Eq5 width hypotheses,
  not a construction theorem.
  Also proved
  `aoyagiLemma5IntervalExcess_eq_eq5OffsetCard_add_risingIndicator` and
  `aoyagiLemma5Eq5_lowerEndpoint_not_mem_offsetValueSet_of_le_min`, which
  decompose the interval excess into the Eq5 strict-offset count plus a
  rising-coordinate indicator, and show the lower endpoint is not a strict
  Eq5 offset value in the rising region.  This is count scaffolding only, not
  displayed-vector realisation or Lemma 5's order-count theorem.
  The follow-up Eq5 interval/introduced-label wrappers insert the lower
  endpoint into the strict-offset set in the rising region, prove the inserted
  set has excess-cardinality and lies in the same-coordinate interval, and
  package supplied Eq5 own-block data as interval membership, `T S=k-1`, and
  post-advance `introducedLabel L n S k S k`.  These remain count/API
  scaffolding only: the actual-width lower bound is explicit, and no displayed
  vector, terminality, admissibility, or order count is proved.
  Also proved the Eq3/Eq4 own-coordinate actual-label adapters
  `aoyagiLemma5Eq4_piecewise_ownCoordinate_actualWidthLabel_of_widthCompatibility`
  and
  `aoyagiLemma5Eq3_piecewise_ownCoordinate_actualWidthLabel_of_sourceSelected_slack`.
  These package `T(S)=k-1` with `actualWidthLabel` for supplied piecewise
  certificates.  The companion last-cutpoint wrappers
  `aoyagiLemma5Eq4_piecewise_ownCoordinate_actualWidthLabel_of_lastPoint` and
  `aoyagiLemma5Eq3_piecewise_ownCoordinate_actualWidthLabel_of_lastPoint`
  derive the upper source range from `C.point ell<=L+1`; they still assume
  actual-width compatibility, and Eq3 keeps the explicit one-unit slack.
  The post-advance introduced-label wrappers
  `aoyagiLemma5Eq4_piecewise_ownCoordinate_introducedLabel_of_lastPoint` and
  `aoyagiLemma5Eq3_piecewise_ownCoordinate_introducedLabel_of_lastPoint`
  package the same own-coordinate value as `introducedLabel L n S k S k`.
  Also proved
  `aoyagiLemma5Eq5_upperEndpoint_mem_intervalValueSetNat_of_lt`,
  `aoyagiLemma5Eq5_upperEndpoint_not_mem_insert_lowerEndpoint_offsets_of_le_min`,
  and
  `aoyagiLemma5Eq5_insertLower_offsets_eq_interval_erase_upper_of_le_min`.
  These identify, in the rising region, the lower endpoint plus strict Eq5
  offsets with the same-coordinate interval after erasing the upper endpoint.
  This is finite-set count scaffolding only; it does not prove that equations
  `(3)` or `(4)` realise the erased endpoint or prove displayed-vector
  construction.
  Also proved
  `aoyagiLemma5Eq4_piecewise_ownCoordinate_mem_introducedLabelFinset_of_lastPoint`,
  `aoyagiLemma5Eq3_piecewise_ownCoordinate_mem_introducedLabelFinset_of_lastPoint`,
  and
  `aoyagiLemma5Eq5_ownBlock_intervalValue_mem_introducedLabelFinset_of_lastPoint_widthBound`.
  These are finite-domain adapters over existing introduced-label wrappers;
  they do not provide `LabelExponentCertificate` terminal-exponent or
  least-value data.
  Also proved `aoyagiLemma5IntervalSize_eq_succ_of_le_min`,
  `aoyagiLemma5IntervalSize_eq_min_succ_of_min_le_of_le_max`,
  `aoyagiLemma5IntervalSize_eq_falling_of_max_le`, and
  `aoyagiLemma5IntervalSize_sourcePiecewise`, which reproduce the source
  three-region interval-size profile as finite arithmetic only.
  Also proved
  `aoyagiLemma5Eq5_ownBlock_offsetValue_mem_introducedLabelFinset_of_lastPoint_widthBound`,
  an Eq5 one-alpha adapter packaging offset-value membership, interval
  membership, `T S=k-1`, and introduced-label finite-domain membership.
  Also proved
  `aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_eq_interval_erase_upper_of_le_min`,
  which substitutes a supplied Eq4 own-coordinate lower endpoint into the
  Eq5 erase-upper finite-set equality.
  Also proved
  `aoyagiLemma5Eq5_offsets_eq_interval_erase_endpoints_of_le_min`, isolating
  the strict Eq5 offsets as the same-coordinate interval with both endpoints
  erased in the rising region.
  Also proved Eq3/Eq4 own-coordinate interval finite-domain adapters:
  `aoyagiLemma5Eq4_piecewise_ownCoordinate_intervalValue_mem_introducedLabelFinset_of_lastPoint`
  and
  `aoyagiLemma5Eq3_piecewise_ownCoordinate_intervalValue_mem_introducedLabelFinset_of_lastPoint`.
  Also proved the Eq5 one-step introduced-domain insert wrapper
  `aoyagiLemma5Eq5_ownBlock_introducedLabelFinset_succ_eq_insert_of_lastPoint_widthBound`.
  Also proved the generic one-step introduced-domain cardinality theorem
  `introducedLabelFinset_card_succ_eq_succ` and its Eq5 source-facing wrapper
  `aoyagiLemma5Eq5_ownBlock_introducedLabelFinset_card_succ_eq_succ_of_lastPoint_widthBound`.
  Also proved the Eq5 one-branch erased-endpoints interval finite-domain
  adapter
  `aoyagiLemma5Eq5_ownBlock_eraseEndpoints_mem_introducedLabelFinset_of_lastPoint_widthBound`.
  Also proved Eq3/Eq4 one-step introduced-domain insert/cardinality wrappers:
  `aoyagiLemma5Eq4_ownCoordinateFinset_succ_eq_insert_of_lastPoint`,
  `aoyagiLemma5Eq4_ownCoordinateFinset_card_succ_eq_succ_of_lastPoint`,
  `aoyagiLemma5Eq3_ownCoordinateFinset_succ_eq_insert_of_lastPoint`, and
  `aoyagiLemma5Eq3_ownCoordinateFinset_card_succ_eq_succ_of_lastPoint`.
  Also proved the Eq5 supplied-post-data recurrence-weight wrapper
  `aoyagiLemma5Eq5_ownBlock_case2_weight_succ_current_eq_newVar_mul_of_lastPoint_widthBound`.
  Also proved the Eq3/Eq4 supplied-post-data recurrence-weight wrappers
  `aoyagiLemma5Eq4_ownCoordinate_case2_weight_succ_current_eq_newVar_mul_of_lastPoint`
  and
  `aoyagiLemma5Eq3_ownCoordinate_case2_weight_succ_current_eq_newVar_mul_of_lastPoint`.
  Also proved the Eq3/Eq4/Eq5 supplied exponent-domain extension wrappers
  `aoyagiLemma5Eq4_ownCoordinate_extendExponentDomain_succ_current_of_lastPoint`,
  `aoyagiLemma5Eq3_ownCoordinate_extendExponentDomain_succ_current_of_lastPoint`,
  and
  `aoyagiLemma5Eq5_ownBlock_extendExponentDomain_succ_current_of_lastPoint_widthBound`.
  Also proved the first-interval supplied-shaped finite-set coverage theorem
  `aoyagiLemma5_suppliedEq3Upper_Eq4_firstInterval_insertOwnCoordinates_eq_intervalValueSetNat`,
  where the upper endpoint is a separately supplied Eq3-shaped certificate;
  printed Eq3 excludes `(S_2-1,Htilde'_1+1)`.
  Also proved the p-general supplied-upper finite-set coverage wrapper
  `aoyagiLemma5_suppliedUpper_Eq4_insertOwnCoordinate_eq_intervalValueSetNat_of_le_min`;
  its upper endpoint equality is an explicit hypothesis, not a printed Eq3
  claim.
  Also proved the supplied Eq3-shaped component-value wrapper
  `aoyagiLemma5Eq3_piecewise_component_upperEndpoint_of_le_gap` and its
  one-interval finite-set coverage instantiation
  `aoyagiLemma5_suppliedEq3UpperComponent_Eq4_interval_insertComponents_eq_intervalValueSetNat`;
  no source-label legality or introduced-label status is claimed.
  Also proved supplied-bound Eq3-shaped component source-label wrappers:
  `aoyagiLemma5Eq3_component_actualWidthLabel_of_lastPoint_labelBounds`,
  `aoyagiLemma5Eq3_component_introducedLabel_of_lastPoint_labelBounds`,
  `aoyagiLemma5Eq3_component_mem_introducedLabelFinset_of_lastPoint_labelBounds`,
  and
  `aoyagiLemma5Eq3_component_intervalValue_mem_introducedLabelFinset_of_lastPoint_labelBounds`.
  They keep actual-width compatibility and label bounds explicit.
  Also proved supplied-bound Eq3 component domain, recurrence, and exponent
  wrappers:
  `aoyagiLemma5Eq3_componentFinset_succ_eq_insert_of_lastPoint_labelBounds`,
  `aoyagiLemma5Eq3_componentFinset_card_succ_eq_succ_of_lastPoint_labelBounds`,
  `aoyagiLemma5Eq3_component_case2_weight_succ_current_eq_newVar_mul_of_lastPoint_labelBounds`,
  and
  `aoyagiLemma5Eq3_component_extendExponentDomain_succ_current_of_lastPoint_labelBounds`.
  The exponent wrapper keeps terminal-exponent equality and least-value data
  explicit.
  Also proved the Eq5 strict-offset rising count
  `aoyagiLemma5Eq5OffsetValueSet_card_eq_pred_of_le_min`, a one-coordinate
  finite count specialization of the existing offset-cardinality theorem.
  Also proved the Eq4 lower plus Eq5 offset count wrapper
  `aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_card_eq_offsetCard_add_one_of_le_min`.
  Also proved the supplied Eq3/Eq4 interval cardinality wrappers
  `aoyagiLemma5_suppliedEq3UpperComponent_Eq4_interval_insertComponents_card_eq_intervalSize`
  and
  `aoyagiLemma5_suppliedEq3Upper_Eq4_insertComponents_card_eq_offsetCard_add_two`.
  Also proved the supplied chart-family count boundary in
  `lean/DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean`:
  `AoyagiLemma5SuppliedNonbaseFamily`,
  `AoyagiLemma5SuppliedAdmissibleNonbaseFamily`,
  `aoyagiLemma5SuppliedNonbaseFamily_branch_card_eq_interval_card_sub_one`,
  `aoyagiLemma5SuppliedNonbaseFamily_count`,
  `aoyagiLemma5SuppliedNonbaseFamily_biUnion_count`, and
  `AoyagiLemma5SuppliedAdmissibleNonbaseFamily.branch_twoValueCount`.  These
  prove the aggregate count only from supplied base-value membership,
  injective erased-interval coverage, cross-coordinate disjointness for the
  union count, and explicit branchwise Lemma 4 obligations.
  Also proved the explicit supplied base-branch wrapper:
  `AoyagiLemma5SuppliedNonbaseFamily.fullBranches`,
  `AoyagiLemma5SuppliedNonbaseFamily.fullBranches_card`,
  `AoyagiLemma5SuppliedAdmissibleFamily`,
  `AoyagiLemma5SuppliedAdmissibleFamily.fullBranches_card`, and
  `AoyagiLemma5SuppliedAdmissibleFamily.base_twoValueCount`.  These encode the
  leading `1` as a supplied `none` branch and nonbase branches as `some b`,
  then count the resulting tagged finite family under the same supplied
  boundary.
  Also proved full tagged-branch admissibility wrappers:
  `AoyagiLemma5SuppliedNonbaseFamily.some_mem_fullBranches_iff`,
  `AoyagiLemma5SuppliedAdmissibleFamily.fullH`, and
  `AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_twoValueCount`.  These
  prove Lemma 4's finite two-value count for every tagged supplied full branch
  under explicit `a<=ell` and selected-width sum hypotheses.
  Also proved the full supplied-family free-count minimum wrappers:
  `AoyagiLemma5SuppliedAdmissibleFamily.fullBranches_card_and_fullBranch_twoValueCount`
  and
  `AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_freeHighCount_lemma3A_eq_min`.
  These combine the tagged supplied branch API with the existing finite Lemma
  4-to-Lemma 3 bridge; for total increment length `n+1`, every tagged branch's
  first-`n` free high-count parameter attains the isolated Lemma 3 numerator
  minimum.
  Also proved the terminal-numerator supplied bridge in
  `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`:
  `aoyagiLemma4FreeHighCount`,
  `AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_freeHighCountMin`, and
  `IntroducedLabelExponentCertificates.terminalExponent_eq_suppliedLemma5MinNumerator`.
  The bridge assumes the introduced-label numerator equals the Lemma 3
  free-count expression for a tagged supplied branch and then proves the
  corresponding `terminalExponent` equals the isolated Lemma 3 minimum
  numerator.
  Also proved the supplied terminal-candidate package:
  `AoyagiLemma5SuppliedTerminalCandidateFamily`,
  `AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches_card`,
  `AoyagiLemma5SuppliedTerminalCandidateFamily.branch_terminalLeastValue_zero`,
  `AoyagiLemma5SuppliedTerminalCandidateFamily.branch_terminalExponent_eq_minNumerator`,
  and
  `AoyagiLemma5SuppliedTerminalCandidateFamily.branch_terminalCandidateData`.
  This packages supplied branch-to-label maps, introduced-label proofs,
  terminal least-value-zero data, and numerator normalisation for each tagged
  branch.
  Also proved the supplied branch-label image wrappers
  `AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel`,
  `AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage`,
  `AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_mem_introducedLabelFinset`,
  `AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_subset_introducedLabelFinset`,
  `AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_card_eq_fullBranches_card_of_injOn`,
  `AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_card`, and
  `AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_terminalCandidateData`.
  These place the supplied branch labels in `introducedLabelFinset`, count the
  finite image of supplied branch labels under an explicit injectivity
  hypothesis, and transfer the branchwise candidate data to labels in that
  image.  They do not prove source-backed injectivity or any no-extra-minimizer
  theorem.
  Also proved the finite terminal minimum label boundary:
  `aoyagiLemma5MinNumerator`,
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels`,
  `AoyagiLemma5SuppliedTerminalCandidateFamily.mem_terminalMinimumLabels`,
  `AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_subset_terminalMinimumLabels`,
  and
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_noExtra`.
  These prove the supplied candidate labels are minimum labels, and under an
  explicit no-extra containment plus branch-label injectivity count the finite
  minimum-label set.  They do not prove the no-extra containment from the
  source or extract pole order.
  Also packaged the exactness hypotheses as
  `AoyagiLemma5SuppliedTerminalCandidateFamily.TerminalMinimumLabelExactness`
  and proved
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_eq_branchLabelImage_of_exactness`
  and
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_exactness`.
  This is only a convenience wrapper over supplied injectivity and no-extra
  containment.
  A follow-up source audit of Aoyagi Lemma 5's upper-bound paragraph records
  that Aoyagi asserts an upper count of terminal lambda-vectors by counted
  interval data, but a source-backed classifier has not yet been reproduced
  and the paragraph does not yet discharge
  `terminalMinimumLabels subset branchLabelImage`.  The missing bridges are
  label-to-vector, minimum-to-lambda, interval classifier, Case 1(2)
  uniqueness/injection, and back-to-label.  See
  `threads/05-arithmetic-tail/reproduction-lemma5-terminal-exactness-source-audit-a5.md`
  and
  `threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-exactness-source-frontier.md`.
  Also proved the bijection API
  `AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_bijOn_terminalMinimumLabels_of_exactness`,
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_branchLabel_bijOn`,
  and
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_branchLabel_bijOn`.
  This is only an equivalent finite packaging of supplied exactness as
  `Set.BijOn branchLabel fullBranches terminalMinimumLabels`; it does not
  construct the bijection from the source.
  Also proved the Eq3 special-boundary Eq5 obstruction:
  `aoyagiLemma5Eq3_boundaryValue_ne_upperEndpoint`,
  `aoyagiLemma5Eq3_boundaryValue_not_mem_Eq5_offsets`,
  `aoyagiLemma5Eq3_boundaryValue_insert_Eq5_offsets_ne_intervalValueSetNat`,
  and
  `aoyagiLemma5Eq3_boundaryValue_insert_Eq5_offsets_ne_intervalValueSetNat_of_eq_boundary`.
  At `p=ell-a+1`, the supplied Eq3 boundary value is `Htilde'_p+1`, hence it
  is outside the same-coordinate interval and cannot fill that interval when
  inserted into the Eq5 strict offsets.  This is an obstruction record, not an
  endpoint-coverage theorem.
  Also proved the Eq4 rising-boundary gap:
  `aoyagiLemma5Eq4_no_piecewiseSourceVector_of_not_indexGuard`,
  `aoyagiLemma5Eq4_no_piecewiseSourceVector_of_eq_a`, and
  `aoyagiLemma5Eq5_risingBoundary_eq_a_noEq4LowerEndpoint`.  At `p=a`, the
  repaired Eq4 guard would require `a+1<=a`; under the rising hypotheses
  `1<=a` and `a<=ell-a`, Eq5 still misses both endpoints at that coordinate.
  This is a gap record, not a lower-endpoint construction.
  Also proved the terminal Eq5 gap:
  `aoyagiLemma5Eq5OffsetValueSet_eq_empty_of_terminal`,
  `aoyagiHtildeIntervalValueSetNat_terminal_eq_singleton_zero_of_selectedSum`,
  `aoyagiLemma5Eq5_terminal_offsets_ne_intervalValueSetNat_of_selectedSum`,
  and
  `aoyagiLemma5_suppliedTerminalZero_Eq5_offsets_eq_intervalValueSetNat`, plus
  `aoyagiLemma5_suppliedTerminalUpper_Eq5_offsets_eq_intervalValueSetNat`.
  At `p=ell`, Eq5 offsets are empty; under the selected-width sum, the
  terminal interval is `{0}`.  A separately supplied terminal zero, or
  terminal upper endpoint, fills the interval.  This does not construct the
  terminal branch or prove terminal-label exactness.
  Also proved supplied-family terminal chain zero in
  `lean/DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean`:
  `AoyagiLemma5SuppliedAdmissibleNonbaseFamily.branch_terminalH_zero`,
  `AoyagiLemma5SuppliedAdmissibleFamily.base_terminalH_zero`,
  `AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalH_zero`,
  `AoyagiLemma5SuppliedBinaryNonbaseFamily.branch_terminalH_zero`,
  `AoyagiLemma5SuppliedBinaryFamily.base_terminalH_zero`, and
  `AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalH_zero`.  These prove
  terminal chain-coordinate equality `H_ell=0` for supplied branches.  They do
  not prove the source-coordinate terminal equality `T(C.point ell-1)=0`.
  Also proved the Eq4 local lower-endpoint wrappers:
  `aoyagiLemma5Eq4_piecewise_ownCoordinate_lowerEndpoint_of_le_min`,
  `aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_eq_interval_erase_upper_of_piecewise`,
  `aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_card_eq_offsetCard_add_one_of_piecewise`,
  `aoyagiLemma5_suppliedUpper_Eq4_insertOwnCoordinate_eq_intervalValueSetNat_of_piecewise`,
  and
  `aoyagiLemma5_Eq3Upper_Eq4_local_insertComponents_eq_intervalValueSetNat`.
  These remove source-label legality hypotheses from the lower-endpoint
  finite-set wrappers; they do not prove source-label legality or solve the
  `p=a` and `p+1=a` boundary issues.
  Also proved the terminal source-realisation bridge module
  `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalSourceBridge.lean`, with
  `AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalSource_Eq5Coverage`
  and
  `AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalSource_Eq5Coverage`.
  These require the explicit hypothesis
  `T(C.point ell-1)=fullH x (Fin.last ell)` before using branch terminal
  chain-zero to fill the terminal Eq5 singleton.
  Also proved the counted-datum classifier-boundary slice:
  `aoyagiLemma5CountDatumSet_mem_of_terminalH_binaryIncrementPrefixDelta`,
  `AoyagiLemma5SuppliedTerminalCandidateFamily.TerminalMinimumCountDatumClassifier`,
  and
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_countDatumClassifier`.
  The first theorem proves one nonbase `mapsTo` datum from terminal binary
  chain hypotheses and a non-base-value condition.  The second and third
  package a supplied injective classifier from terminal-minimum labels into
  the counted datum set and derive the upper bound.  They do not construct the
  classifier or prove branch-label exactness.
  Also hardened the supplied upper-bound classifier interface:
  `AoyagiLemma5SuppliedTerminalCandidateFamily.upperBoundClassifier_of_terminalMinimumLabels_subset_branchLabelImage`
  and
  `AoyagiLemma5SuppliedTerminalCandidateFamily.upperBoundClassifier_iff_terminalMinimumLabels_subset_branchLabelImage`
  prove that `UpperBoundClassifier` is equivalent to the supplied no-extra
  inclusion `terminalMinimumLabels ⊆ branchLabelImage`.
  Also packaged the supplied counted-datum back-to-branch-label boundary:
  `AoyagiLemma5SuppliedTerminalCandidateFamily.branchCountDatumOfCoord`,
  `AoyagiLemma5SuppliedTerminalCandidateFamily.TerminalMinimumCountDatumBackToBranchLabel`,
  and
  `AoyagiLemma5SuppliedTerminalCandidateFamily.upperBoundClassifier_of_countDatumBackToBranchLabel`.
  The bridge says that the counted datum assigned to each terminal-minimum
  label is realised by a supplied full branch with the same branch label; this
  derives the existing `UpperBoundClassifier`.  It does not construct the
  classifier, branch-coordinate map, or back-to-label bridge from Aoyagi's
  source.
  Also proved terminal source-label bookkeeping:
  `aoyagiLemma5_terminalSourceIndex_pos`,
  `aoyagiLemma5_terminal_actualWidthLabel_of_lastPoint`, and
  `aoyagiLemma5_terminal_intervalValue_mem_introducedLabelFinset_of_terminalZero`.
  These put the supplied terminal zero at source coordinate `C.point ell-1`
  together with legal label `k=1` under explicit terminal source-range and
  width-positivity hypotheses.  They do not construct the terminal source
  branch or the source-realisation equality from branch-chain data.
  Also proved the Eq5 post-`p` lower-bound obstruction
  `aoyagiLemma5Eq5_postP_belowLower_of_intervalExcess_lt_offset`: a supplied
  equation `(5)` post-`p` branch lies strictly below the lower Htilde chain
  whenever its printed subtraction `alpha+b-p` exceeds the Htilde interval
  excess at the same coordinate.  This is an obstruction criterion only, not a
  corrected Eq5 construction or chart-coverage theorem.
  Also proved Eq4 rising-guard exhaustion:
  `aoyagiLemma5Eq4_risingGuardFailure_iff_eq_a`,
  `aoyagiLemma5Eq4_selectedIndexGuardFailure_iff_eq_a`, and
  `aoyagiLemma5Eq4_risingGuardFailure_eq_a_and_no_piecewiseSourceVector`.
  Under `p<=a`, failure of the repaired Eq4 guard `p+1<=a`, equivalently
  failure of the raw selected-index guard under `a<=ell`, is exactly `p=a`.
  The displayed-vector wrapper derives only the supplied Eq4 certificate
  obstruction from guard failure.  It does not prove
  `not Eq4PiecewiseSourceVector iff p=a`, construct Eq4 branches, or fill the
  lower endpoint at `p=a`.
  Also proved the counted-datum back-to-branch-label card-bound wrapper
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_countDatumBackToBranchLabel`.
  It derives `C.terminalMinimumLabels.card <= a * (n+1-a) + 1` from a supplied
  counted-datum classifier and supplied back-to-label bridge by passing
  through the existing `UpperBoundClassifier`.  It does not construct the
  classifier, branch-coordinate map, or back-to-label bridge from Aoyagi's
  source, and it does not prove exact cardinality.
  Also proved terminal source-realisation iff terminal source zero:
  `AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalSource_realisation_iff_terminalZero`
  and
  `AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalSource_realisation_iff_terminalZero`.
  These use branch-chain terminal zero to rewrite
  `T(C.point ell-1)=fullH x (Fin.last ell)` as `T(C.point ell-1)=0`.  They do
  not prove terminal source zero or construct a terminal source branch.
- **Assumed.** for the proved endpoint minimum: integer hypotheses
  `1 <= ell` and `0 <= a <= ell`.  No terminal candidate, feasibility,
  pole-order, or RLCT theorem is accepted yet.
- **Cited.** none planned.
- **Deferred.** terminal candidate set with `\tilde t_{s,k}=0`, feasibility of
  the minimizing exponent chains, the Lemma 4 two-value hypothesis from source
  vector inequalities, the source `T -> (H_j),(S_j)` correspondence and proof
  that Aoyagi's displayed `Ttilde <= T <= Ttilde'` supplies the
  same-coordinate hypotheses, source-label and terminal `tilde t=0`
  realisation, identification of the source terminal-exponent numerator with
  the isolated Lemma 3 free-count expression, Lemma 4's correspondence to
  `lambda`, source-backed injectivity of supplied branch labels, absence of
  extra terminal minimizers,
  conclusion, source-backed Lemma 5 chart-family admissibility and coverage
  from Aoyagi's printed equations, existence of the supplied chart-family
  boundary data including the supplied base branch, pole-order count, and
  analytic extraction.

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
