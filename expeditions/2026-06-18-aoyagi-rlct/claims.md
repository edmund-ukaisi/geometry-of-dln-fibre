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
- **Status.** finite exponent interface, source-facing chart-certificate
  spine, finite min/order certificates, ratio chart-count rewrites, and
  Jacobian/prior loss-shift arithmetic proved; the chart-certificate lift of
  that shift is also proved as certificate algebra on supplied chart data;
  unit-only multiplication of chart-certificate loss/Jacobian-prior displays
  is proved with unchanged exponent data; analytic extraction remains Cited as
  extraction-only. A2 interface repair decision saved at
  `threads/02-analytic-interface/interface-repair-a2.md`.
- **Kill-condition.** Aoyagi's final extraction uses an analytic hypothesis not
  captured by the interface we state, or the interface computes a different
  invariant.
- **Evidence/source.** Aoyagi Definition 1, Definition 2, and
  Hironaka/normal-crossing extraction discussion, PDF pp. 5-6. Aoyagi Lemma 1
  is noted only as an excluded analytic generator-comparison theorem.
- **Pen-and-paper reproduction.**
  `threads/02-analytic-interface/reproduction-normal-crossing-exponent-interface-a0.md`;
  chart-certificate spine at
  `threads/02-analytic-interface/reproduction-normal-crossing-chart-certificate-spine-a0.md`;
  finite certificates at
  `threads/02-analytic-interface/reproduction-normal-crossing-finite-certificates-a0.md`;
  ratio chart counts at
  `threads/02-analytic-interface/reproduction-normal-crossing-ratio-chart-counts-a0.md`;
  Jacobian/prior loss shift at
  `threads/02-analytic-interface/reproduction-normal-crossing-jacobian-prior-loss-shift-a0.md`;
  chart-certificate lift at
  `threads/02-analytic-interface/reproduction-normal-crossing-chart-certificate-jacobian-prior-loss-shift-a0.md`;
  chart-certificate unit multiplication at
  `threads/02-analytic-interface/reproduction-normal-crossing-chart-certificate-unit-multiply-a0.md`.
- **Reproduction check.** analytic scout report at
  `threads/02-analytic-interface/scout-report.md`; controller interface draft
  at `threads/02-analytic-interface/interface-draft.md`; xhigh source/API
  reviews recorded in
  `threads/02-analytic-interface/review-normal-crossing-exponent-interface-a0.md`;
  chart-certificate spine review at
  `threads/02-analytic-interface/review-normal-crossing-chart-certificate-spine-a0.md`;
  finite-certificate and ratio-count reviews at
  `threads/02-analytic-interface/review-normal-crossing-finite-certificates-a0.md`
  and
  `threads/02-analytic-interface/review-normal-crossing-ratio-chart-counts-a0.md`;
  Jacobian/prior loss-shift reviews at
  `threads/02-analytic-interface/review-normal-crossing-jacobian-prior-loss-shift-a0.md`
  and
  `threads/02-analytic-interface/review-normal-crossing-chart-certificate-jacobian-prior-loss-shift-a0.md`;
  chart-certificate unit multiplication review at
  `threads/02-analytic-interface/review-normal-crossing-chart-certificate-unit-multiply-a0.md`.
- **Lean target.** A named hypothesis/interface for concrete
  normal-crossing-certificate extraction, not a theorem pretending to prove the
  analytic extraction or general ideal-generator invariance.
- **Proved.** finite exponent data and formula infrastructure in
  `lean/DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean`:
  `AoyagiNormalCrossingExponentData`, active-coordinate filtering,
  `ratioAt`, `activeRatios`, `exponentMinimum`, chartwise minimum-coordinate
  counts, `exponentOrder`, helper existence/bound lemmas,
  `coordsInChartAtRatio`, `countInChartAtRatio`, finite ratio-count rewrite
  lemmas, `jacobianPriorLossShift`, active ratio shift by `m/2`, finite
  minimum shift by `m/2`, and preservation of minimum-coordinate chart counts
  and finite order under that shift, and
  `AoyagiNormalCrossingChartCertificate` with projection to finite exponent
  data, a chart-level extraction-hypothesis wrapper, and
  `AoyagiNormalCrossingChartCertificate.jacobianPriorLossShift`, whose
  projected finite exponent data is definitionally the finite
  `jacobianPriorLossShift` and whose projected minimum/order consequences are
  proved, plus `AoyagiNormalCrossingChartCertificate.unitMultiply`, which
  absorbs supplied chartwise unit factors into the loss and Jacobian/prior
  unit fields while leaving projected exponent data, finite minimum, and finite
  order unchanged. The chart-level final
  socket `AoyagiTheorem2SuppliedChartFinalBoundary` is proved in
  `lean/DLNFibre/DLN/Aoyagi/Theorem2FinalAssembly.lean`.
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
  certificate. The Lean `jacobianPriorLossShift` lemmas, chart-certificate
  lift, and `unitMultiply` are finite/certificate algebra only and must not be
  used as analytic regular-coordinate additivity, as extraction transfer from a
  reduced certificate, or as permission to treat divisor monomial shifts as
  units without separately supplied unit witnesses.

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
  factors with proof witness `F2 = -S.B`. The fixed-base/source-rank-stratum
  endpoint wrapper now bundles that triangular residual-product form with the
  residual-rank formulas `rEdge p - r`. The transformed-edge rank predicate
  used by the recursive Schur-residual process is proved equivalent to the
  source edge-rank stratum by determinant-unit rank preservation for
  `[I Bprev; 0 I] * E_p`. The local source-rank endpoint package
  now lifts that pointwise shape into a `nhdsWithin` conclusion relative to
  the source rank stratum, with an existential wrapper choosing the
  total-kernel complement. The p. 13 block product-difference algebra is also
  proved pointwise: after the triangular endpoint form, subtracting
  `fromBlocks 1 0 0 0` gives
  `fromBlocks (Ctop - 1) (-F2) (-F3) (D - F3 * F2)`. The scalar
  matrix-entry-ideal consequence of that product-difference matrix is now also
  packaged at the fixed-base/source-rank boundary: determinant-unit triangular
  multiplication transports the entry ideal of `T - T0` to the cleaned
  four-block ideal generated by entries of `Ctop - 1`, `F2`, `F3`, and the
  deterministic residual product. The regular block-entry count from `C1 -
  Er`, `F2`, and `F3` is also proved to give the displayed regular term after
  dividing by two, and is connected to the finite `jacobianPriorLossShift`
  socket without asserting analytic additivity. The full source Theorem 3
  claim remains blocked.
- **Kill-condition.** The reduction silently uses the cited normal-crossing/RLCT
  theorem or another analytic equivalence not represented as a hypothesis.
- **Evidence/source.** Aoyagi Theorem 3 and following regular-variable
  contribution, PDF pp. 11-13.
- **Pen-and-paper reproduction.** draft at
  `threads/03-block-product-reduction/reproduction-draft.md`; through-layer
  basis repair at
  `threads/03-block-product-reduction/through-layer-basis-reproduction.md`;
  triangular endpoint wrapper at
  `threads/03-block-product-reduction/reproduction-a2-triangular-block-diagonal.md`;
  transformed-edge rank-stratum bridge at
  `threads/03-block-product-reduction/reproduction-a2-transformed-edge-rank-stratum-bridge.md`;
  local source-rank endpoint package at
  `threads/03-block-product-reduction/reproduction-a2-local-source-rank-endpoint-package.md`;
  pointwise block product-difference algebra at
  `threads/03-block-product-reduction/reproduction-a2-block-product-difference-algebra.md`;
  product-difference entry-ideal boundary at
  `threads/03-block-product-reduction/reproduction-a2-product-difference-entry-ideal-boundary.md`;
  regular-variable count at
  `threads/03-block-product-reduction/reproduction-a2-regular-variable-count.md`.
- **Reproduction check.** findings at
  `threads/03-block-product-reduction/reproduction-check.md`; not
  formalisation-ready as stated. Repair report at
  `threads/03-block-product-reduction/reproduction-repair-a2.md`. Through-layer
  basis repair checked by xhigh checker `Hooke`; finite chart-data construction
  rechecked by xhigh explorer `Arendt`; paper-order bridge inventory at
  `threads/03-block-product-reduction/paper-order-bridge-notes.md`; triangular
  endpoint wrapper checked by xhigh reviewer `Kepler`; source-rank-stratum
  endpoint wrapper checked by xhigh reviewer `Carson` in
  `threads/03-block-product-reduction/review-a2-source-rank-stratum-theorem3-boundary.md`;
  local source-rank endpoint package reviewed in
  `threads/03-block-product-reduction/review-a2-local-source-rank-endpoint-package.md`;
  block product-difference algebra independently checked by xhigh
  pen-and-paper scout `Lorentz` and accepted by xhigh fidelity/scope reviewer
  `Fermat` in
  `threads/03-block-product-reduction/review-a2-block-product-difference-algebra.md`;
  product-difference entry-ideal boundary reviewed by xhigh `Dewey` in
  `threads/03-block-product-reduction/review-a2-product-difference-entry-ideal-boundary.md`;
  regular-variable count and finite-shift bridge reviewed by xhigh `Franklin`
  in `threads/03-block-product-reduction/review-a2-regular-variable-count.md`.
- **Lean target.**
  `DLNFibre.DLN.Aoyagi.productReduction_chartLocalInductionStep_fromBlocks` in
  `lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`; indexed variant
  `DLNFibre.DLN.Aoyagi.productReduction_chartLocalInductionStep_fromBlocks_indexed` in
  `lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`; local chart-stability
  theorem `DLNFibre.DLN.Aoyagi.upperUnitriangular_mul_fromBlocks_one_zero` in
  the same file; chart-form preservation corollary
  `DLNFibre.DLN.Aoyagi.exists_fromBlocks_one_zero_of_upperUnitriangular_mul` in
  the same file; product-difference theorem
  `DLNFibre.DLN.Aoyagi.triangularBlockProductDifference_fromBlocks_indexed` in
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
  `lean/DLNFibre/DLN/Aoyagi/BlockElimination.lean`; entry-ideal transport,
  sign, block, and signed product-difference cleanup lemmas in
  `lean/DLNFibre/DLN/Aoyagi/EntryIdeal.lean`; product-difference entry-ideal
  boundary wrappers in
  `lean/DLNFibre/DLN/Aoyagi/ProductReductionEntryIdealBoundary.lean`;
  regular-variable count and finite-shift bridge in
  `lean/DLNFibre/DLN/Aoyagi/FinalFormula.lean` and
  `lean/DLNFibre/DLN/Aoyagi/RegularVariableShift.lean`;
  through-layer subspace theorem
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
  top-left corner and zero lower-left block. Also proved the pointwise block
  product-difference identity
  `[I 0; F3 I] * (T - [I 0; 0 0]) * [I F2; 0 I] =
  [Ctop - I, -F2; -F3, D - F3 * F2]` from the assumed triangular endpoint
  block form. Also proved the elementary
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
  Also proved the fixed-base/source-rank-stratum endpoint wrapper
  `PaperEndpointFixedBaseTriangularResidualProductSourceRanks` and constructor
  `PaperEndpointFixedBaseProductReductionCertificate.exists_triangularBlockDiagonal_residualProduct_sourceRanks`,
  which bundle the transformed residual-product endpoint form with the
  residual-rank formulas `rEdge p - r`. Also proved
  `paperEndpointFixedBaseSourceRankStratum_selfBase_mem`,
  `paperEndpointFixedBaseTriangularSourceRanks_selfBase_mem_nhdsWithin_source`,
  `PaperEndpointTriangularSourceRanksLocalCertificate`, and
  `exists_paperEndpointTriangularSourceRanksLocalCertificate`, which package
  basepoint source-stratum membership from supplied rank data and the same
  endpoint source shape as a local relative-neighborhood conclusion over the
  source rank stratum. Also proved the finite regular-variable count
  `aoyagiTheorem2RegularVariableCount`, its half-equality with the displayed
  regular term under endpoint rank-width bounds, and the finite
  `jacobianPriorLossShift` consequences for exponent minimum, finite order,
  chart-certificate projections, and supplied finite-formula hypotheses.
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
  fields if a later certificate needs them. Exact rank-stratum hypotheses are
  now packaged as relative-stratum boundaries, not open neighborhoods; see
  `threads/03-block-product-reduction/paper-order-bridge-notes.md` and
  `threads/03-block-product-reduction/reproduction-a2-rank-stratum-boundary.md`.
  The source-rank/residual-product bundle is recorded at
  `threads/03-block-product-reduction/reproduction-a2-source-rank-stratum-theorem3-boundary.md`;
  the local relative-neighborhood package is recorded at
  `threads/03-block-product-reduction/reproduction-a2-local-source-rank-endpoint-package.md`.
  These are still fixed-base/source-stratum and certificate-relative, not a
  source proof of regular-corner chart production, exact-rank openness,
  nonemptiness, Lemma 1 normalization, ideal transport, normal crossings, pole
  order, or RLCT.

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
  source-produced `C'^(S+1)`, or a transition invariant.  A 2026-06-23
  xhigh branch re-audit now separately checks the continuing, actual-width
  stopped, and row-exhausted stopped branches and confirms that existing
  supplied-obligation consumers are the safe boundary; no source-production
  theorem is justified by Aoyagi pp. 19-22 alone.
  The A4 chart-certificate coordinate adapter
  `Case2DisplayedContinuingA0ExponentCoordinateBridge.of_chartCertificate_coord_exponents`
  is also proved in `lean/DLNFibre/DLN/Aoyagi/Case2FiniteExponentBridge.lean`.
  It takes supplied equalities on `Cnc.lossExp` and
  `Cnc.jacobianPriorExp` and constructs the A0-facing wrapper around the
  generic Case 2 exponent-coordinate bridge for `Cnc.exponentData`.  This is
  definitional projection only; it does not construct the chart certificate,
  coordinate, active-ratio lower bounds, chart counts, normal crossings, pole
  order, or RLCT.
  The A4/A0 Case 2 local chart-certificate contribution summary
  `case2DisplayedCenterSqFormalJacobianChartCertificate.localChartCertificateContribution_summary`
  is also proved in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`.  It bundles
  the generic source bridge for the local microcertificate's own exponent
  data with the source-bridge ratio, local finite minimum, local ratio-count,
  local minimum-count, and local finite order.  This is a local one-chart
  summary only; it does not construct global A0 data, chart coverage,
  active-ratio lower bounds, chart counts for the full normal-crossing family,
  pole order, or RLCT.
  The A4/A0 Case 1 local chart-certificate contribution summaries
  `case1SelectedOldCenterSqFormalJacobianChartCertificate.localChartCertificateContribution_summary`
  and
  `case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.localChartCertificateContribution_summary`
  are also proved in
  `lean/DLNFibre/DLN/Aoyagi/Case1FiniteExponentBridge.lean`.  They bundle the
  generic Case 1 selected-entry bridge for each local microcertificate's own
  exponent data with the local ratio, local finite minimum, local ratio-count,
  local minimum-count, and local finite order.  This is local one-chart
  bookkeeping only; it does not construct global A0 data, the hidden
  selected-old source label, chart coverage, active-ratio lower bounds, chart
  counts for the full normal-crossing family, pole order, `theta`, or RLCT.
  The A4/A0 selected-entry all-pivot finite certificate
  `selectedEntryCenterSqFormalJacobianChartFamilyCertificate` is also proved
  in `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`.  It indexes
  charts by a supplied equivalence `Fin center.card ≃ center`; each chart
  delegates to the existing one-pivot selected-entry certificate for the
  selected pivot.  Its finite exponent data has ratio `center.card / 2`,
  chartwise ratio count `1`, finite minimum `center.card / 2`, and finite
  order `1`.  This is finite certificate-family bookkeeping only; it does not
  construct analytic atlas coverage, transition regularity, analytic
  Jacobian/volume-form control, source production, global active-ratio lower
  bounds, pole order, `theta`, or RLCT.
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
	  Review of the Case 2 continuing supplied-`Csucc` stack consumer is saved
	  at
	  `threads/04-blow-up-certificate/review-case2-source-production-obligation-continuing-csucc-stack-a4.md`.
	  Reproduction of the Case 2 next-state source-product reindex is saved at
	  `threads/04-blow-up-certificate/reproduction-case2-next-state-source-product-reindex-a4.md`;
	  xhigh review found no blocking issues and is saved at
	  `threads/04-blow-up-certificate/review-case2-next-state-source-product-reindex-a4.md`.
	  Reproduction of the Case 2 selected-entry chart-family data and displayed
	  source-product bridge is saved at
	  `threads/04-blow-up-certificate/reproduction-case2-selected-entry-chart-family-data-a4.md`;
	  xhigh review passed with the printed weight-factor caveat recorded at
	  `threads/04-blow-up-certificate/review-case2-selected-entry-chart-family-data-a4.md`.
	  Reproduction of the Case 2 selected-entry center square and formal
	  Jacobian microcertificate is saved at
	  `threads/04-blow-up-certificate/reproduction-case2-selected-entry-center-sq-jacobian-a4.md`;
	  xhigh source/math and Lean/API review passed and is saved at
	  `threads/04-blow-up-certificate/review-case2-selected-entry-center-sq-jacobian-a4.md`.
	  Reproduction of the Case 2 selected-entry center unit factor is saved at
	  `threads/04-blow-up-certificate/reproduction-case2-selected-entry-center-unit-a4.md`;
	  xhigh source/math and Lean/API review passed and is saved at
	  `threads/04-blow-up-certificate/review-case2-selected-entry-center-unit-a4.md`.
	  Reproduction of the Case 2 continuing reindexed source-chart certificate
	  is saved at
	  `threads/04-blow-up-certificate/reproduction-case2-continuing-reindexed-source-chart-certificate-a4.md`;
	  xhigh review passed and is saved at
	  `threads/04-blow-up-certificate/review-case2-continuing-reindexed-source-chart-certificate-a4.md`.
	  Reproduction of the Case 2 continuing reindexed source-chart unit
	  certificate is saved at
	  `threads/04-blow-up-certificate/reproduction-case2-continuing-reindexed-source-chart-unit-certificate-a4.md`;
	  xhigh source/math and Lean/API review passed and is saved at
	  `threads/04-blow-up-certificate/review-case2-continuing-reindexed-source-chart-unit-certificate-a4.md`.
	  Reproduction of the Case 2 continuing center-square/formal-Jacobian
	  certificate is saved at
	  `threads/04-blow-up-certificate/reproduction-case2-continuing-center-sq-formal-jacobian-certificate-a4.md`;
	  xhigh source/math and Lean/API review passed and is saved at
	  `threads/04-blow-up-certificate/review-case2-continuing-center-sq-formal-jacobian-certificate-a4.md`.
	  Reproduction of the Case 2 continuing certificate chart-family-free
	  directification is saved at
	  `threads/04-blow-up-certificate/reproduction-case2-continuing-certificate-without-chart-family-a4.md`;
	  xhigh fidelity/bedrock review passed and is saved at
	  `threads/04-blow-up-certificate/review-case2-continuing-certificate-without-chart-family-a4.md`.
	  Reproduction of the Case 2 continuing old-top/source-suffix paper-`C'`
	  stack chart-family-free directification is saved at
	  `threads/04-blow-up-certificate/reproduction-case2-continuing-oldtop-source-suffix-paper-cprime-stack-without-chart-family-a4.md`;
	  xhigh source/reproduction and Lean dependency reviews passed and are
	  saved at
	  `threads/04-blow-up-certificate/review-case2-continuing-oldtop-source-suffix-paper-cprime-stack-without-chart-family-a4.md`.
	  Reproduction of the Case 2 paper-`C'` lower-row chart-family-free
	  directification is saved at
	  `threads/04-blow-up-certificate/reproduction-case2-paper-cprime-lower-rows-without-chart-family-a4.md`;
	  xhigh source-frontier and Lean dependency reviews passed and are saved
	  at
	  `threads/04-blow-up-certificate/review-case2-paper-cprime-lower-rows-without-chart-family-a4.md`.
	  Reproduction of the Case 2 source-current stack chart-family-free
	  directification is saved at
	  `threads/04-blow-up-certificate/reproduction-case2-source-current-stack-without-chart-family-a4.md`;
	  xhigh source/fidelity and Lean dependency reviews passed and are saved
	  at
	  `threads/04-blow-up-certificate/review-case2-source-current-stack-without-chart-family-a4.md`.
	  Reproduction of the A4/A0 Case 2 exponent-coordinate bridge is saved at
	  `threads/04-blow-up-certificate/reproduction-case2-a0-exponent-coordinate-bridge-a4.md`;
	  xhigh source/math and Lean/API review passed and is saved at
	  `threads/04-blow-up-certificate/review-case2-a0-exponent-coordinate-bridge-a4.md`.
	  Reproduction of the A4/A0 Case 2 exponent-minimum bridge is saved at
	  `threads/04-blow-up-certificate/reproduction-case2-a0-exponent-minimum-bridge-a4.md`;
	  xhigh source/math and Lean/API review passed and is saved at
	  `threads/04-blow-up-certificate/review-case2-a0-exponent-minimum-bridge-a4.md`.
	  Reproduction of the selected-entry finite normal-crossing
	  microcertificate is saved at
	  `threads/04-blow-up-certificate/reproduction-selected-entry-normal-crossing-microcertificate-a4.md`;
	  xhigh fidelity/bedrock review passed and is saved at
	  `threads/04-blow-up-certificate/review-selected-entry-normal-crossing-microcertificate-a4.md`.
	  Reproduction of the Case 1 selected-entry formal-Jacobian cardinality
	  slice is saved at
	  `threads/04-blow-up-certificate/reproduction-case1-selected-entry-formal-jacobian-cardinality-a4.md`;
	  xhigh source/math and Lean/API review passed and is saved at
	  `threads/04-blow-up-certificate/review-case1-selected-entry-formal-jacobian-cardinality-a4.md`.
	  The 2026-06-23 branchwise source-production re-audit is saved at
	  `threads/04-blow-up-certificate/audit-case2-branchwise-successor-production-recheck-a4.md`.
	  Reproduction of the Case 2 local chart-certificate contribution is saved
	  at
	  `threads/04-blow-up-certificate/reproduction-case2-local-chart-certificate-contribution-a4.md`;
	  xhigh source/fidelity and Lean/API reviews passed and are saved at
	  `threads/04-blow-up-certificate/review-case2-local-chart-certificate-contribution-a4.md`.
	  Reproduction of the Case 1 local chart-certificate contributions is saved
	  at
	  `threads/04-blow-up-certificate/reproduction-case1-local-chart-certificate-contribution-a4.md`;
	  xhigh source/fidelity and Lean/API reviews passed and are saved at
	  `threads/04-blow-up-certificate/review-case1-local-chart-certificate-contribution-a4.md`.
	  Reproduction of the selected-entry multi-chart certificate is saved at
	  `threads/04-blow-up-certificate/reproduction-selected-entry-multi-chart-certificate-a4.md`;
	  xhigh fidelity review passed and is saved at
	  `threads/04-blow-up-certificate/review-selected-entry-multi-chart-certificate-a4.md`.
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
	  `selectedEntryChartMap_pivot_mem_valueSet`, the selected-entry chart-family
	  scaffold `SelectedEntryChartFamilyData`, its standard constructor and
	  value/divisibility/principalization projections, and the Case 2
	  displayed-pivot specializations
	  `case2_displayedPivot_selectedEntryChartMap_value_mem`,
	  `Case2ResidualBlockSelectedEntryChartFamilyData`,
	  `Case2ResidualBlockSelectedEntryChartFamilyData.displayedPivot`, and
	  `Case2ResidualBlockSelectedEntryChartFamilyData.standard_value_displayedPivot_eq_sourceChartMap`.
	  Also proved the finite selected-entry center square and formal
	  pivot-first determinant microcertificate:
	  `selectedEntryCenterSq`,
	  `selectedEntryCenterSq_selectedEntryChartMap`,
	  `selectedEntryPivotFirstJacobian`,
	  `selectedEntryPivotFirstJacobian_det`,
	  `SelectedEntryChartFamilyData.centerSq_chartMap`,
	  `case2DisplayedSourceChartMap_centerSq`,
	  `case2DisplayedSourceChartMap_pivotFirstJacobian_det`, and
	  `case2DisplayedSourceChartMap_pivotFirstJacobian_exponent_eq_centerCard_sub_one`.
	  Also proved the selected-entry center unit-factor microcertificate:
	  `selectedEntryCenterSq_nonneg`,
	  `selectedEntryCenterSqUnitFactor`,
	  `selectedEntryCenterSqUnitFactor_pos`,
	  `selectedEntryCenterSqUnitFactor_ne_zero`,
	  `selectedEntryCenterSqUnitFactor_isUnit`,
	  `case2DisplayedSourceChartMap_centerSqUnitFactor_pos`,
	  `case2DisplayedSourceChartMap_centerSqUnitFactor_ne_zero`, and
	  `case2DisplayedSourceChartMap_centerSqUnitFactor_isUnit`.
	  These are finite algebra only: the normalized square-sum factor is now
	  proved pointwise positive/nonzero and a unit over ordered fields, but
	  this is not analytic nonvanishing on a chart neighbourhood; the determinant
	  is not an analytic derivative or volume-form theorem.
	  Also proved the ordered-field local certificate refinement
	  `Case2DisplayedContinuingReindexedSourceChartUnitCertificate` and
	  `sourceChartMap_continuingReindexedSourceChartUnitCertificate`, which
	  package the existing displayed continuing reindexed source-chart
	  certificate together with the selected-entry center-square unit witness.
	  This is still not analytic chart coverage, unit control for `P`/`Q`,
	  a total loss unit, normal crossings, pole order, or RLCT.
	  Also proved the selected-entry finite normal-crossing microcertificate
	  in `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`:
	  `selectedEntryCenterSqFormalJacobianChartCertificate`,
	  `case2DisplayedCenterSqFormalJacobianChartCertificate`, and
	  `case2DisplayedCenterSqFormalJacobianChartCertificate.localExponentCoordinateBridge`.
	  This constructs a one-chart `AoyagiNormalCrossingChartCertificate` only
	  for the finite selected-entry center square-sum and formal pivot-first
	  determinant.  Its parameter is the finite-center value function and its
	  chart residuals are indexed by `center.erase pivot`; the generic Case 2
	  exponent-coordinate bridge is constructed only for that
	  microcertificate's own one-coordinate exponent data, while the A0-facing
	  wrapper remains reserved for later full-A0 data.  It is not global chart
	  production, chart coverage, source production, analytic
	  Jacobian/volume-form data, pole order, or RLCT extraction.
	  Also proved the local finite exponent arithmetic for that
	  microcertificate's own exponent data:
	  `selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_ratioAt_zero_zero`,
	  `selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_exponentMinimum_eq_centerCard_div_two`,
	  `selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_exponentOrder_eq_one`,
	  `case2DisplayedCenterSqFormalJacobianChartCertificate.exponentData_ratioAt_zero_zero`,
	  `case2DisplayedCenterSqFormalJacobianChartCertificate.exponentData_exponentMinimum_eq_centerCard_div_two`,
	  and
	  `case2DisplayedCenterSqFormalJacobianChartCertificate.exponentData_exponentOrder_eq_one`.
	  The local finite minimum is `center.card / 2` and the local finite
	  order is `1`; this is not the global A0 minimum, global A0 order, pole
	  order, or RLCT.
	  Also proved
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
  explicit row-validity bound `J+J1 <= mu_S` visible. Also proved the Case 1
  selected-entry formal-Jacobian cardinality slice:
  `case1StripRows_card`, `case1StripCols_card`,
  `case1StripEntries_card`, `case1CenterGenerators_card`,
  `case1CenterGenerators_erase_card_of_mem`,
  `case1CenterGenerators_erase_selectedOld_card`,
  `case1CenterGenerators_erase_displayedPivot_card_of_bounds`,
  `case1SelectedOldCenterSqFormalJacobianChartCertificate`,
  `case1SelectedOldCenterSqFormalJacobianChartCertificate.jacobianPriorExp_zero_zero`,
  `case1SelectedOldCenterSqFormalJacobianChartCertificate.pivotFirstJacobian_det`,
  `case1DisplayedRowStripCenterSqFormalJacobianChartCertificate`,
  `case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.jacobianPriorExp_zero_zero`,
  and
  `case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.pivotFirstJacobian_det`.
  These prove only that the two displayed finite selected-entry charts have
  formal determinant exponent `J1*(n(S+1)-J)`; they do not prove analytic
  Jacobian/volume-form control, chart production, coverage, transition
  regularity, normal crossings, pole order, or RLCT. Also proved the local
  finite exponent arithmetic for the two displayed Case 1 selected-entry
  microcertificates:
  `case1SelectedOldCenterSqFormalJacobianChartCertificate.lossExp_zero_zero`,
  `case1SelectedOldCenterSqFormalJacobianChartCertificate.exponentData_ratioAt_zero_zero`,
  `case1SelectedOldCenterSqFormalJacobianChartCertificate.exponentData_exponentMinimum_eq_nonpivotCount_add_one_div_two`,
  `case1SelectedOldCenterSqFormalJacobianChartCertificate.exponentData_exponentOrder_eq_one`,
  `case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.lossExp_zero_zero`,
  `case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.exponentData_ratioAt_zero_zero`,
  `case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.exponentData_exponentMinimum_eq_nonpivotCount_add_one_div_two`,
  and
  `case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.exponentData_exponentOrder_eq_one`.
  Their local finite ratio and local finite minimum are
  `(1 + J1*(n(S+1)-J))/2`, and their local finite order is `1`.  This is
  not a global A0 active-ratio lower bound, global A0 exponent minimum,
  global chart-count/order theorem, analytic Jacobian/volume-form theorem,
  pole order, or RLCT. Also proved the Case 1 selected-entry chart-family
  data slice:
  `Case1CenterSelectedEntryChartFamilyData`,
  `Case1CenterSelectedEntryChartFamilyData.standard`,
  `Case1CenterSelectedEntryChartFamilyData.selectedOldPivot`,
  `Case1CenterSelectedEntryChartFamilyData.displayedPivot`,
  `Case1CenterSelectedEntryChartFamilyData.standard_value_selectedOldPivot`,
  `Case1CenterSelectedEntryChartFamilyData.standard_value_displayedPivot`,
  `Case1CenterSelectedEntryChartFamilyData.standard_selectedOld_selected_mem_valueSet`,
  `Case1CenterSelectedEntryChartFamilyData.standard_displayedPivot_selected_mem_valueSet`,
  `Case1CenterSelectedEntryChartFamilyData.standard_centerSq_selectedOldPivot`,
  `Case1CenterSelectedEntryChartFamilyData.standard_centerSq_displayedPivot`,
  `Case1CenterSelectedEntryChartFamilyData.standard_centerIdeal_selectedOldPivot_eq_span_singleton`,
  and
  `Case1CenterSelectedEntryChartFamilyData.standard_centerIdeal_displayedPivot_eq_span_singleton`.
  These are finite coordinate-data and finite algebra facts only: the `Unit`
  old generator remains a token for an externally chosen source label,
  arbitrary row-strip pivots are not source-displayed transition formulas,
  and no chart coverage, regularity, analytic Jacobian, global A0 data, pole
  order, or RLCT is proved. Also packaged the finite
  selected-entry all-pivot chart-family certificate:
  `selectedEntryCenterSqFormalJacobianChartFamilyCertificate`,
  `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.lossExp_chart_zero`,
  `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.jacobianPriorExp_chart_zero`,
  `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exponentData_ratioAt_chart_zero`,
  `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exponentData_exponentMinimum_eq_centerCard_div_two`,
  `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exponentData_countInChartAtRatio_centerCard_div_two_eq_one`,
  `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exponentData_minCountInChart_eq_one`,
  and
  `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exponentData_exponentOrder_eq_one`.
  This finite family is indexed by a supplied equivalence
  `Fin center.card ≃ center`, delegates each chart to the corresponding
  one-pivot selected-entry microcertificate, and proves ratio
  `center.card / 2`, chartwise ratio count `1`, finite minimum
  `center.card / 2`, and finite order `1`.  It is not analytic chart
  coverage, transition regularity, source production, analytic Jacobian
  control, pole order, or RLCT.  Also proved the finite source-point
  presentation adapter for that all-pivot certificate:
  `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartPoint`,
  `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.chartMap_sourceChartPoint_eq`,
  `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.loss_sourceChartPoint_eq_centerSq`,
  `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.lossUnit_sourceChartPoint_eq`,
  `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.jacobianPrior_sourceChartPoint_eq_det`,
  `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.loss_monomial_sourceChartPoint`,
  and
  `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.jacobianPrior_monomial_sourceChartPoint`.
  These lemmas expose the one-pivot source-point calculation chartwise for
  pivot `chartEquiv c`; they do not prove coverage, transition regularity,
  source production, analytic Jacobian control, global A0 data, pole order, or
  RLCT.  Also proved finite selected-entry chart-map coverage:
  `selectedEntryCenterSqFormalJacobianChartCertificate.exists_oneChartPoint_chartMap_eq_value_of_pivot_ne_zero`,
  `selectedEntryCenterSqFormalJacobianChartCertificate.exists_oneChartPoint_chartMap_eq_value_of_forall_eq_zero`,
  `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exists_chartPoint_chartMap_eq_value_of_chart_pivot_ne_zero`,
  and
  `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exists_chartPoint_chartMap_eq_value`.
  These theorems invert a finite value with nonzero selected pivot by dividing
  by that pivot, cover the zero value by the zero source point, and then choose
  a nonzero coordinate as pivot for the all-pivot family.  This is finite map
  coverage only, not analytic atlas coverage, transition regularity,
  arbitrary-pivot source formulas, source production, analytic Jacobian data,
  normal-crossing certificate production, pole order, or RLCT.  Also
  specialized this finite coverage theorem to the existing Case 2 and Case 1
  all-pivot certificates:
  `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.exists_chartPoint_chartMap_eq_value`
  and
  `case1CenterSqFormalJacobianChartFamilyCertificate.exists_chartPoint_chartMap_eq_value`.
  These are definitional wrappers using the Case 2 continuation nonemptiness
  and the Case 1 old-generator nonemptiness.  They are not arbitrary-pivot
  source formulas, analytic atlas coverage, transition regularity, source
  production, normal-crossing certificate production, pole order, or RLCT.
  Also packaged the finite
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
  Added the row-index source-substitution form
  `exists_case2DisplayedQP_mul_sourceSubstitution_of_rowIndex_monomialRec`,
  which keeps the source-substituted displayed block on the left while using
  row-index recurrence divisibility for the `P` quotient witnesses.
  Added the finite source-block tail-lift API `verticalBlock`,
  `fromBlocks_mul_verticalBlock`, `fromBlocks_mul_verticalBlock_eq_of_tail`,
  `exists_case2DisplayedQP_verticalBlock_sourceSubstitution_of_flat_weights`,
  `exists_case2DisplayedQP_verticalBlock_sourceSubstitution_of_rowIndex_monomialRec`,
  and
  `exists_case2DisplayedQP_verticalBlock_transportedFollowingFactor_of_rowIndex_monomialRec`.
  Added all-pivot finite selected-entry/source-chart adapters
  `Case2ResidualBlockSelectedEntryChartFamilyData.standard_value_eq_sourceSelectedChartMapOfMem`,
  `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartPoint`,
  and
  `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.chartMap_sourceChartPoint_eq_sourceSelectedChartMapOfMem`,
  connecting each all-pivot certificate chart to the existing
  source-selected Case 2 chart map.
  Added the source-selected monomial/principalization adapters
  `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.centerIdeal_sourceSelectedChartMap_eq_span_singleton`,
  `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.loss_sourceChartPoint_eq_sourceSelectedCenterSq`,
  `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.lossUnit_sourceChartPoint_eq_sourceSelectedUnitFactor`,
  `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.jacobianPrior_sourceChartPoint_eq_sourceSelectedDet`,
  `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.loss_monomial_sourceChartPoint_sourceSelected`,
  and
  `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.jacobianPrior_monomial_sourceChartPoint_sourceSelected`,
  exposing the finite center principalization, loss/Jacobian monomial fields,
  normalized loss unit, and formal pivot-first determinant in those
  source-selected chart-map names.
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
	  Added the displayed source-chart reindexed product bridge
	  `sourceChartMap_reindexedNextSourceProduct_withCorrectedPostData`, now
	  backed by the direct theorem
	  `sourceChartMap_reindexedNextSourceProduct_fromCase2SuccCorrectedPostData`,
	  which composes the source-chart `Q/P` identity with the finite next
	  same-stage source-product reindex and returns corrected concrete
	  post-data projections without using the supplied chart-family boundary.
	  This is corrected displayed algebra, not source production or a literal
	  reading of the inconsistent printed outside-`u` factor.
	  Added the fielded continuing local certificate
	  `Case2DisplayedReindexedNextSourceProductEq`,
	  `Case2DisplayedContinuingReindexedSourceChartCertificate`, and
	  `sourceChartMap_continuingReindexedSourceChartCertificate`, packaging the
	  displayed source chart, finite center principalization, continuing
	  next-center nonemptiness, reindexed next-source product, corrected post
	  data, post-weight convention, and new-numerator center cardinality without
	  entering A0 normal-crossing data.
	  Added chart-family-free direct constructors
	  `sourceChartMap_continuingReindexedSourceChartCertificate_withoutChartFamily`,
	  `sourceChartMap_continuingReindexedSourceChartUnitCertificate_withoutChartFamily`,
	  and
	  `sourceChartMap_continuingCenterSqFormalJacobianCertificate_withoutChartFamily`.
	  The older chart-family-bearing continuing certificate constructors remain
	  compatibility wrappers only.  The direct path uses finite selected-entry
	  algebra, concrete `case2Succ` recurrence post-data, corrected exponent
	  post-data, and the chart-family-free reindexed next-source-product theorem;
	  it does not source-produce `Csucc`, successor chart families, suffixes,
	  coverage, transition regularity, analytic Jacobian data, normal crossings,
	  pole order, or RLCT.
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
  The continuing old-top/source-suffix paper-`C'` stack now has a
  chart-family-free constructor
  `sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withoutChartFamily`;
  the older
  `sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withCorrectedPostData`
  is a compatibility wrapper.  This removes only the vacuous finite
  `Case2ResidualBlockChartFamilyBoundary` dependency from that stack identity;
  the raw suffix remains supplied and the theorem does not source-produce
  `Csucc` or `C'^(S+1)`, suffixes, coverage, transition regularity, analytic
  Jacobians, normal crossings, pole order, or RLCT.
  The underlying paper-`C'` lower-row handoff and its arbitrary
  right-multiplied following-product variant now also have chart-family-free
  constructors
  `sourceChartMap_paperCprimeWeightedLowerRows_withoutChartFamily` and
  `sourceChartMap_paperCprimeWeightedLowerRows_mul_followingProduct_withoutChartFamily`;
  the older chart-family-bearing lower-row APIs are compatibility wrappers.
  These remain lower-row finite algebra only and do not add pivot-row
  equality, source-produced successor data, coverage, transition regularity,
  analytic Jacobians, normal crossings, pole order, or RLCT.
  The source-current row stack wrapper now has chart-family-free constructor
  `sourceChartMap_continuingOldTopSourceSuffixSuccFollowingBlock_withoutChartFamily`;
  the older chart-family-bearing source-current API is a compatibility
  wrapper.  This is only formula-level row presentation of the same continuing
  stack via `case2SourceCurrentFollowingBlock` and
  `case2SourceSuccessorFollowingBlock`; it does not source-produce `Csucc` or
  `C'^(S+1)`, produce suffixes, construct successor charts, prove transition
  regularity, analytic Jacobians, normal crossings, pole order, termination,
  or RLCT.
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
  The continuing weighted successor-following handoff is now proved as
  `continuingWeightedSuccFollowingFrontierPayload_of_sourceFollowing`, with
  package projection
  `SourceChartFrontierBoundaryPackages.continuingWeightedSuccFollowing`.  It
  converts the existing source-following payload to the canonical
  formula-level successor-following notation by the next same-stage
  restriction equality, and it remains only a finite adapter for
  `case2DisplayedSourceSuccessorFollowingFactor`, not arbitrary supplied
  `Csucc` source production.
  The supplied source-production-obligation projection
  `SourceProductionObligation.rowExhausted_Cterm_eq_originalRows_Csucc` now
  rewrites row-exhausted `Cterm` as original terminal rows of the supplied
  `Csucc`, using the obligation's supplied row-exhausted terminal-row
  equality, formula equality, and the existing transported-row/original-
  successor-row identity.  This is a consequence of supplied data only, not
  construction of `Csucc`, suffixes, charts, or a transition theorem.
  The supplied-obligation projections
  `SourceProductionObligation.continuing_Csucc_tail_eq_original` and
  `SourceProductionObligation.actualWidth_Cterm_eq_originalRows_Csucc` are now
  also proved.  They respectively rewrite the supplied `Csucc` next
  same-stage tail to the old source-following tail, and rewrite actual-width
  stopped `Cterm` as original rows of supplied `Csucc`.  The continuing
  theorem consumes `Csucc_eq_formula` and an existing finite tail identity;
  the actual-width theorem consumes the supplied `actualWidth_Cterm_eq`
  branch field, the actual-width collapse identity, and `Csucc_eq_formula`.
  They do not construct source data or a transition theorem.
  The canonical supplied-obligation constructor
  `SourceProductionObligation.of_formulaSuccessor_transportTerminalRows` is
  now proved.  It chooses `Csucc` and `Cterm` by the existing formula-level
  successor and transported terminal-row definitions.  It is still not source
  production of successor chart data, suffixes, coverage, transition
  regularity, or a full transition theorem.
  The follow-up API-hardening slice proves
  `SelectedEntryChartFamilyBoundary.exists_trivial`,
  `Case2ResidualBlockChartFamilyBoundary.exists_trivial`,
  and
  `Case2ResidualBlockChartFamilyBoundary.continuingSuccessorBoundary_exists_truePredicates`.
  This showed that the next-chart-family existential accepted arbitrary
  predicates, so `True` predicates were enough.  A source check of Aoyagi
  pp. 19-22 confirms that the paper does not construct this next chart
  family; the theorem is not source-backed chart production.
  The vacuous field has now been removed from the obligation.  The new main
  canonical constructor is
  `SourceProductionObligation.of_formulaSuccessor_transportTerminalRows`; the
  older supplied/true-predicate constructor names were removed from the
  current Lean API.  This hardens the interface but still does not
  source-produce successor data, suffixes, charts, coverage, transition
  regularity, or a full transition theorem.
  The continuing supplied-obligation stack consumer is now proved as
  `SourceProductionObligation.continuing_Csucc_currentFollowingBlock_eq_formula`
  and
  `SourceProductionObligation.continuing_sourceCurrentStack_suppliedCsucc`.
  It rewrites the existing old-top/source-suffix continuing stack payload with
  the supplied successor object `Csucc` on the successor side, consuming only
  `Csucc_eq_formula` and the already proved source-current stack theorem.
  This is still finite payload rewriting, not construction of `Csucc`,
  suffixes, charts, coverage, transition regularity, or a full transition
  theorem.
  The actual-width supplied-obligation `Cterm` frontier consumer is now proved
  as `ActualWidthSourceSuffixSuppliedCtermPayload` and
  `SourceProductionObligation.actualWidth_frontier_suppliedCterm`.  Under
  `n(S+1)=J+1`, it specializes the actual-width stopped frontier to the
  source suffix and rewrites the terminal factor through the supplied matrix
  `Cterm`.  This consumes only `actualWidth_frontier` and
  `actualWidth_Cterm_eq`; it does not construct source data or a transition
  theorem.
  The source-chart frontier package now also has a chart-family-free
  constructor:
  `sourceChartMap_frontierBoundaryPackages_withoutChartFamily`, supported by
  the continuing helpers
  `sourceChartMap_postPivotNextSameStageProduct_withSourceFollowingFactorAndCorrectedPostData_withoutChartFamily`,
  `sourceChartMap_continuingWeightedSourceFollowingPayload_withFiniteCenterIdeal_withoutChartFamily`,
  and
  `sourceChartMap_continuingWeightedSuccFollowingPayload_withFiniteCenterIdeal_withoutChartFamily`.
  The old package remains as a compatibility wrapper, and
  `SourceProductionObligation.of_formulaSuccessor_transportTerminalRows` now
  consumes the chart-family-free package.  This removes a vacuous finite
  caller dependency on `ChartRegular`, `TransitionRegular`, and
  `Case2ResidualBlockChartFamilyBoundary`.  The stopped fields still keep the
  accepted branch-implication meanings; the row-exhausted branch remains
  transported-prefix rows, not original rows.  This is not chart production,
  source production of `Csucc` or `C'^(S+1)`, suffix production, transition
  regularity, normal crossings, pole order, termination, or RLCT extraction.
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
  A 2026-06-22 Aoyagi-only source audit recommends freezing A5 as a supplied
  downstream boundary for now: PDF pp. 25-27's printed Lemma 5 paragraph and
  Eq3/Eq4/Eq5 families do not by themselves supply a classifier, injection,
  back-to-label map, or full Lemma 4 witness for source-backed no-extra
  terminal-minimum coverage.
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
  The terminal source endpoint payload is now also Lean-proved: a supplied
  branch whose terminal chain coordinate is explicitly realised by the source
  terminal coordinate gives terminal Eq5 finite-set coverage and terminal
  introduced-label membership, still under explicit source-realisation,
  source-range, and width-positivity hypotheses.
  The Eq4 rising non-strict endpoint inventory is now Lean-proved as a
  dispatcher over existing boundary facts: under `p<=a`, failure of `p+1<a`
  splits into terminal collision `p+1=a` or repaired-guard failure `p=a`,
  with terminal-collision consequences conditional on supplied Eq4 data and
  the `p=a` branch retaining the Eq5 erased-endpoints deficit.
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
  `threads/05-arithmetic-tail/reproduction-lemma5-eq4-actual-width-label-a5.md`;
  terminal source endpoint payload at
  `threads/05-arithmetic-tail/reproduction-lemma5-terminal-source-endpoint-payload-a5.md`;
  Eq4 rising non-strict endpoint split at
  `threads/05-arithmetic-tail/reproduction-lemma5-eq4-rising-nonstrict-endpoint-split-a5.md`;
  Eq5 endpoint raw branches at
  `threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-raw-branches-a5.md`;
  Eq5 endpoint branch coordinates at
  `threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-branchcoord-a5.md`;
  Eq5 endpoint branch-coordinate disjointness at
  `threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-branchcoord-disjoint-a5.md`;
  Eq5 endpoint raw value injectivity at
  `threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-value-injective-a5.md`;
  Eq5 endpoint raw cardinality at
  `threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-raw-cardinality-a5.md`;
  Eq5 endpoint counted-datum classifier at
  `threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-countdatum-classifier-a5.md`;
  Eq5 endpoint filtered cardinality at
  `threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-filtered-cardinality-a5.md`;
  Eq5 value-label branch injection at
  `threads/05-arithmetic-tail/reproduction-lemma5-eq5-value-label-branch-injection-a5.md`;
  Eq5 branch-coordinate/value cardinal squeeze at
  `threads/05-arithmetic-tail/reproduction-lemma5-eq5-branchcoord-value-cardinal-squeeze-a5.md`.
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
  `threads/05-arithmetic-tail/review-lemma5-eq4-actual-width-label-a5.md`;
  terminal source endpoint payload checked by xhigh API scout `Euclid` and
  xhigh hardener `Carver` at
  `threads/05-arithmetic-tail/review-lemma5-terminal-source-endpoint-payload-a5.md`;
  Eq4 rising non-strict endpoint split checked by xhigh Lean scout `Jason`
  and xhigh hardener `McClintock` at
  `threads/05-arithmetic-tail/review-lemma5-eq4-rising-nonstrict-endpoint-split-a5.md`;
  Eq5 endpoint raw branches checked by xhigh `Hilbert` at
  `threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-raw-branches-a5.md`;
  Eq5 endpoint branch coordinates checked by xhigh `Chandrasekhar` at
  `threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-branchcoord-a5.md`;
  Eq5 endpoint branch-coordinate disjointness checked by xhigh `Noether` at
  `threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-branchcoord-disjoint-a5.md`;
  Eq5 endpoint raw value injectivity checked by xhigh `Dalton` at
  `threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-value-injective-a5.md`;
  Eq5 endpoint raw cardinality checked by xhigh `Arendt` at
  `threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-raw-cardinality-a5.md`;
  Eq5 endpoint counted-datum classifier reviewed by xhigh `Hypatia` and
  `Dirac`, with documentation repairs recorded at
  `threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-countdatum-classifier-a5.md`;
  Eq5 endpoint filtered cardinality reviewed by xhigh `Harvey` at
  `threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-filtered-cardinality-a5.md`;
  Eq5 value-label branch injection reviewed by xhigh `Hume` at
  `threads/05-arithmetic-tail/review-lemma5-eq5-value-label-branch-injection-a5.md`;
  Eq5 branch-coordinate/value cardinal squeeze reviewed by xhigh `Godel` at
  `threads/05-arithmetic-tail/review-lemma5-eq5-branchcoord-value-cardinal-squeeze-a5.md`.
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
  `lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`;
  Eq5 supplied endpoint raw coverage in
  `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean`, including the
  endpoint branch-coordinate, disjointness, raw value-injectivity, filtered
  cardinality, and counted-datum classifier adapters; Eq5 terminal value-label branch
  injectivity, branch-coordinate/value adapters, and terminal cardinal-squeeze wrappers in
  `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`; broader A5
  targets TBD.
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
  Also proved the counted-datum back-to-branch-label exactness wrappers
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_countDatumBackToBranchLabel`
  and
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_countDatumBackToBranchLabel`.
  These combine supplied back-to-label data with supplied branch-label
  injectivity, and with the selected-width sum for exact cardinality.  They do
  not construct those supplied fields from source.
  Also proved the terminal order classifier-notation handoff in
  `Lemma5TerminalOrderBridge.lean`:
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_theorem2OrderFormula_of_upperBoundClassifier`,
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_upperBoundClassifier_and_branchLabel_injOn`,
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_theorem2OrderFormula_of_countDatumBackToBranchLabel`, and
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_countDatumBackToBranchLabel_and_injOn`.
  These are only final-order notation rewrites of existing supplied
  classifier/back-to-label routes; exact-count variants still require
  supplied branch-label injectivity.
  Also proved the Eq5 endpoint-family terminal order-formula handoff in
  `Lemma5Eq5TerminalOrderBridge.lean`:
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze`.
  This specializes the existing Eq5 endpoint-family block-width cardinal
  squeeze to `data : AoyagiDefinition3CeilData (N+1) m`, using
  `data.aParam_le` and `data.selectedSum_eq` and unfolding
  `data.theorem2OrderFormula`.  It does not construct Eq5 branches or
  terminal payloads from source, prove the endpoint-family equality, prove
  terminal `(p, alpha)` injectivity, prove branch-label injectivity/no-extra
  coverage, pole order, normal crossings, or RLCT.
  Also proved `aoyagiLemma5Eq5EndpointRawBranches`,
  `aoyagiLemma5Eq5EndpointRawBranches_value_image_eq_intervalValueSetNat`, and
  `AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage`.  The
  raw branch set inserts the upper endpoint at every interior coordinate and
  the lower endpoint exactly in the rising case `j<=a` and `j<=ell-a`.  The
  value-image theorem proves full same-coordinate interval coverage from
  strict Eq5 alpha-domain coverage and supplied endpoint value equalities.
  The constructor wrapper feeds this proved raw coverage into the existing
  supplied-family constructor, with base-value membership, raw injectivity,
  and cross-coordinate disjointness still supplied.
  Also proved `aoyagiLemma5Eq5EndpointRawBranches_branchCoord_eq` and
  `AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_branchCoord_eq`.
  These pass supplied component coordinate facts through the conditional raw
  branch set and the base-value filter.  They do not prove endpoint
  distinctness, survival through the base filter, source-produced coordinates,
  raw injectivity/disjointness, or any no-extra classifier theorem.
  Also proved
  `aoyagiLemma5Eq5EndpointRawBranches_pairwiseDisjoint_of_branchCoord_eq` and
  `AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_branchCoord`.
  These derive cross-coordinate raw-branch disjointness at distinct interior
  coordinates from supplied component coordinate facts and remove only the
  separate disjointness input from the endpoint supplied-family constructor.
  Raw value injectivity, source production, base-value membership, coverage
  data, endpoint values, base-filter survival, and no-extra classifier data
  remain supplied or unproved.
  Also proved
  `aoyagiLemma5Eq5EndpointRawBranches_value_injective_of_alpha_injective` and
  `AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord`.
  These derive one-coordinate raw value injectivity at interior coordinates
  from strict alpha-domain coverage, strict value formulas, endpoint value
  formulas, and supplied strict alpha injectivity.  The constructor wrapper
  combines this with coordinate-disjointness to remove only raw value
  injectivity and raw disjointness from the strictest Eq5 endpoint constructor;
  branch construction, source-label legality, source proof of strict alpha
  injectivity, base-filter survival, no-extra coverage, and order-count data
  remain unproved.
  Also proved
  `aoyagiLemma5Eq5EndpointRawBranches_card_eq_intervalSize_of_value_injective`
  and
  `aoyagiLemma5Eq5EndpointRawBranches_card_eq_intervalSize_of_alpha_injective`.
  These count one interior raw endpoint branch set through its injective value
  image and the Htilde interval value-set cardinality.  They do not count the
  filtered nonbase family, prove base-filter survival, or classify
  terminal-minimum labels.
  Also proved
  `AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord_branchCoord_eq`
  and
  `AoyagiLemma5SuppliedNonbaseFamily.countDatumClassifierOfEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord`.
  These package the strictest endpoint supplied family into the generic
  counted-datum classifier API for its supplied `fullBranches`.  They do not
  classify source terminal-minimum labels or prove no-extra coverage.
  Also proved
  `AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_branch_card_eq_intervalSize_sub_one`,
  `AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_fullBranches_card`,
  and
  `AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord_fullBranches_card`.
  These specialize the generic supplied-family counts to the filtered Eq5
  endpoint constructors, counting filtered supplied branches and tagged
  supplied full branches only.  They do not count terminal-minimum labels,
  prove source branch construction or source-label legality, prove base-filter
  survival for source records, prove source-backed no-extra coverage, or prove
  a Lemma 5 order count.
  Also proved
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_endpointBase_cardSqueeze`
  and
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_endpointBase_cardSqueeze`.
  These compose the structured terminal counted-datum injection and
  terminal-endpoint-base branch-label injection adapters into the existing
  finite cardinal squeeze.  They prove conditional terminal-minimum exactness
  and exact cardinality only under supplied terminal Eq5 payloads, terminal
  `(p, alpha)` injectivity, branch alpha data, terminal-label nonbase
  inequalities, and the terminal-endpoint base label.  They do not prove
  source-backed no-extra coverage or a Lemma 5 order count.
  Also proved
  `AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_nonbase_valueLabel`,
  `AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_nonbase_valueLabel_terminalEndpointBase`,
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze`,
  and
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze`.
  These prove branch-label injectivity from supplied selected-block
  membership, supplied nonbase value-label synchronisation, and endpoint-base
  separation, then compose it with terminal `(p, alpha)` counted-datum
  injectivity in the existing cardinal squeeze.  They do not construct the
  value-label relation or terminal Eq5 payloads from source, prove direct
  counted-datum back-to-label coverage, prove source-backed no-extra
  coverage, or prove a Lemma 5 order count.
  Also proved
  `AoyagiLemma5SuppliedTerminalCandidateFamily.branchBlock_of_branchCoord_leftEndpoint`,
  `AoyagiLemma5SuppliedTerminalCandidateFamily.valueLabel_of_branchK_value`,
  `AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_branchCoord_leftEndpoint_branchK_value_terminalEndpointBase`,
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_branchCoordVal_cardSqueeze`,
  and
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_branchCoordVal_cardSqueeze`.
  These derive the selected-block and value-label inputs from supplied
  branch-coordinate correctness, supplied left-endpoint `branchS` labels, and
  supplied `branchK`/value synchronisation before applying the existing
  value-label/pAlpha cardinal squeeze.  They do not construct those branch
  coordinates or labels from source, prove direct counted-datum back-to-label
  coverage, prove source-backed no-extra coverage, or prove a Lemma 5 order
  count.
  Also proved
  `AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_strict_branch_card_eq_intervalSize_sub_one`.
  This specializes the one-coordinate filtered count to the strictest Eq5
  endpoint constructor, still only counting filtered supplied branches after
  the supplied base value is erased.  It does not prove source branch
  construction, base-filter survival, terminal-minimum labels, no-extra
  coverage, or a Lemma 5 order count.
  Also proved
  `AoyagiLemma5SuppliedTerminalCandidateFamily.branchCoord_of_toNonbase_eq_eq5EndpointCoverage`
  and
  `AoyagiLemma5SuppliedTerminalCandidateFamily.branchBlock_of_toNonbase_eq_eq5EndpointCoverage_leftEndpoint`.
  These transport branch-coordinate correctness from the strictest endpoint
  constructor into a terminal-candidate family under an explicit nonbase-family
  equality, then use a supplied left-endpoint `branchS` formula to derive the
  selected-block input.  They do not construct endpoint branches from source,
  prove source labels or terminal Eq5 payloads, identify terminal-minimum
  labels with endpoint branches, prove no-extra coverage, or prove a Lemma 5
  order count.
  Also proved
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5EndpointFamily_branchCoordVal_cardSqueeze`
  and
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5EndpointFamily_branchCoordVal_cardSqueeze`.
  These compose the endpoint-family branch-coordinate transport with the
  existing branch-coordinate/value terminal cardinal squeeze.  They replace
  only the abstract terminal branch-coordinate hypothesis by an explicit
  endpoint-family equality and endpoint constructor data; terminal payloads,
  terminal `(p, alpha)` injectivity, branch source/value labels, endpoint base
  label, and source-backed/direct back-to-label no-extra coverage remain
  outside source proof.
  Also proved
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_eq_branchLabelImage_of_card_bound_and_branchLabel_injOn`
  and
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_iff_branchLabel_injOn_and_card_bound`.
  These isolate the generic finite obstruction after supplied branches are
  known to attain the terminal minimum: supplied branch-label injectivity plus
  a supplied cardinal upper bound
  `terminalMinimumLabels.card <= a*(n+1-a)+1` is equivalent to terminal
  exactness.  They do not prove the upper bound, branch-label injectivity, or
  no-extra coverage from source.
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
  Latest handoff wrapper: a supplied terminal-minimum counted-datum classifier
  now gives the Theorem 2 order-formula upper bound directly, and supplied
  branch-label injectivity upgrades that bound to equality:
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_theorem2OrderFormula_of_countDatumClassifier`
  and
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_countDatumClassifier_and_branchLabel_injOn`
  in `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalOrderBridge.lean`.  Reproduction:
  `threads/05-arithmetic-tail/reproduction-lemma5-countdatum-classifier-order-formula-bridge-a5.md`;
  review:
  `threads/05-arithmetic-tail/review-lemma5-countdatum-classifier-order-formula-bridge-a5.md`.
  This is finite notation handoff only and does not construct the classifier,
  branch-label injectivity, back-to-label coverage, no-extra coverage, pole
  order, normal crossings, or RLCT.
  Latest Eq5 endpoint-family order-formula wrapper: the supplied
  endpoint-family block-width cardinal squeeze now rewrites directly to
  `data.theorem2OrderFormula` as
  `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze`
  in `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalOrderBridge.lean`.
  Reproduction:
  `threads/05-arithmetic-tail/reproduction-lemma5-eq5-terminal-order-formula-bridge-a5.md`;
  review:
  `threads/05-arithmetic-tail/review-lemma5-eq5-terminal-order-formula-bridge-a5.md`.
  This is finite supplied-payload notation plumbing only and does not move the
  source-exactness, pole-order, normal-crossing, or RLCT boundary.

## Claim A6 - final Aoyagi formula, conditional on A0

- **Statement.** Combining the proved Aoyagi-specific reductions with the cited
  normal-crossing extraction interface gives Aoyagi's RLCT and RLCT-order
  formula for deep linear networks.
- **Tier.** Final synthesis claim.
- **Status.** open.  Formula-notation, Definition 3 bridge, Definition 3
  source-data ceiling, Definition 3 source-data local wrappers, Definition 3
  source-data final-boundary handoff, conditional finite-exponent bridge,
  terminal-order equality-bridge, Eq5 terminal-order bridge, and Definition 3
  source-data Eq5 terminal-order bridge slices have landed, but the final RLCT
  theorem remains open.
- **Kill-condition.** Any source hypothesis, rank bound, dimension convention,
  or pole-order convention is lost in translation.
- **Evidence/source.** Aoyagi Theorem 2, PDF pp. 8-9. Aoyagi Theorem 1
  (PDF pp. 6-7) is a cited earlier three-layer formula, not the multi-layer
  main theorem.
- **Pen-and-paper reproduction.** Definition 3/Theorem 2 formula translation
  reproduced at
  `threads/06-dln-translation/reproduction-definition3-theorem2-translation-a6.md`;
  dimension/rank convention map reproduced at
  `threads/06-dln-translation/reproduction-dimension-rank-convention-a6.md`;
  source-data ceiling reproduced at
  `threads/06-dln-translation/reproduction-definition3-source-data-ceil-a6.md`;
  source-data local wrappers reproduced at
  `threads/06-dln-translation/reproduction-definition3-source-data-local-wrappers-a6.md`;
  source-data final-boundary handoff reproduced at
  `threads/06-dln-translation/reproduction-definition3-source-data-final-boundary-a6.md`;
  conditional finite-exponent bridge reproduced at
  `threads/06-dln-translation/reproduction-theorem2-finite-exponent-bridge-a6.md`;
  chart finite-certificate bridge reproduced at
  `threads/06-dln-translation/reproduction-theorem2-chart-finite-certificate-bridge-a6.md`;
  chart ratio-count bridge reproduced at
  `threads/06-dln-translation/reproduction-theorem2-chart-ratio-count-bridge-a6.md`;
  finite active-ratio terminal-order bridge reproduced at
  `threads/06-dln-translation/reproduction-theorem2-active-terminal-order-bridge-a6.md`;
  finite active chart-terminal-order bridge reproduced at
  `threads/06-dln-translation/reproduction-theorem2-active-chart-terminal-order-bridge-a6.md`;
  supplied final assembly boundary reproduced at
  `threads/06-dln-translation/reproduction-theorem2-final-assembly-a6.md`;
  displayed-ratio count terminal-order bridge reproduced at
  `threads/06-dln-translation/reproduction-theorem2-ratio-count-terminal-order-bridge-a6.md`;
  counted-datum classifier terminal-order bridge reproduced at
  `threads/06-dln-translation/reproduction-theorem2-countdatum-terminal-order-bridge-a6.md`;
  chart terminal-order bridge reproduced at
  `threads/06-dln-translation/reproduction-theorem2-chart-terminal-order-bridge-a6.md`;
  terminal-order equality bridge reproduced at
  `threads/06-dln-translation/reproduction-theorem2-terminal-order-equality-bridge-a6.md`;
  Eq5 terminal-order bridge reproduced at
  `threads/06-dln-translation/reproduction-theorem2-eq5-terminal-order-bridge-a6.md`;
  Definition 3 source-data Eq5 terminal-order bridge reproduced at
  `threads/06-dln-translation/reproduction-definition3-source-data-eq5-terminal-order-bridge-a6.md`;
  Case 2 finite-formula wrapper reproduced at
  `threads/06-dln-translation/reproduction-case2-theorem2-finite-formula-bridge-a6.md`;
  Case 2 ratio-count finite-formula wrapper reproduced at
  `threads/06-dln-translation/reproduction-case2-theorem2-ratio-count-finite-formula-bridge-a6.md`;
  Case 2 chart-final boundary wrapper reproduced at
  `threads/06-dln-translation/reproduction-case2-theorem2-chart-final-bridge-a6.md`;
  remaining source-obligations boundary map at
  `threads/06-dln-translation/boundary-map-theorem2-remaining-source-obligations-a6.md`.
- **Reproduction check.** xhigh source/API checks incorporated in
  `threads/06-dln-translation/review-final-formula-notation-a6.md`;
  source-data ceiling reviewed at
  `threads/06-dln-translation/review-definition3-source-data-ceil-a6.md`;
  source-data local wrappers reviewed at
  `threads/06-dln-translation/review-definition3-source-data-local-wrappers-a6.md`;
  source-data final-boundary handoff reviewed at
  `threads/06-dln-translation/review-definition3-source-data-final-boundary-a6.md`;
  conditional bridge reviewed at
  `threads/06-dln-translation/review-theorem2-finite-exponent-bridge-a6.md`;
  chart finite-certificate bridge reviewed at
  `threads/06-dln-translation/review-theorem2-chart-finite-certificate-bridge-a6.md`;
  chart ratio-count bridge reviewed at
  `threads/06-dln-translation/review-theorem2-chart-ratio-count-bridge-a6.md`;
  active-ratio terminal-order bridge reviewed at
  `threads/06-dln-translation/review-theorem2-active-terminal-order-bridge-a6.md`;
  active chart-terminal-order bridge reviewed at
  `threads/06-dln-translation/review-theorem2-active-chart-terminal-order-bridge-a6.md`;
  displayed-ratio count terminal-order bridge reviewed at
  `threads/06-dln-translation/review-theorem2-ratio-count-terminal-order-bridge-a6.md`;
  counted-datum classifier terminal-order bridge reviewed at
  `threads/06-dln-translation/review-theorem2-countdatum-terminal-order-bridge-a6.md`;
  chart terminal-order bridge reviewed at
  `threads/06-dln-translation/review-theorem2-chart-terminal-order-bridge-a6.md`;
  terminal-order equality bridge reviewed at
  `threads/06-dln-translation/review-theorem2-terminal-order-equality-bridge-a6.md`;
  Eq5 terminal-order bridge reviewed at
  `threads/06-dln-translation/review-theorem2-eq5-terminal-order-bridge-a6.md`;
  Definition 3 source-data Eq5 terminal-order bridge reviewed at
  `threads/06-dln-translation/review-definition3-source-data-eq5-terminal-order-bridge-a6.md`;
  Case 2 finite-formula wrapper reviewed at
  `threads/06-dln-translation/review-case2-theorem2-finite-formula-bridge-a6.md`;
  Case 2 ratio-count finite-formula wrapper reviewed at
  `threads/06-dln-translation/review-case2-theorem2-ratio-count-finite-formula-bridge-a6.md`;
  Case 2 chart-final boundary wrapper reviewed at
  `threads/06-dln-translation/review-case2-theorem2-chart-final-bridge-a6.md`;
  final assembly reviewed at
  `threads/06-dln-translation/review-theorem2-final-assembly-a6.md`.
- **Lean target.** final theorem TBD after A1-A5.  Current notation layer:
  `DLNFibre.DLN.Aoyagi.aoyagiReducedWidthInt`,
  `DLNFibre.DLN.Aoyagi.aoyagiReducedWidthInt_eq_natCast_sub_of_rank_le`,
  `DLNFibre.DLN.Aoyagi.aoyagiReducedWidthInt_nonneg_of_rank_le`,
  `DLNFibre.DLN.Aoyagi.aoyagiSelectedReducedWidths`,
  `DLNFibre.DLN.Aoyagi.aoyagiSelectedReducedWidths_apply`,
  `DLNFibre.DLN.Aoyagi.aoyagiSelectedReducedWidths_eq_natCast_sub_of_rank_le`,
  `DLNFibre.DLN.Aoyagi.aoyagiSelectedReducedWidths_nonneg_of_rank_le`,
  `DLNFibre.DLN.Aoyagi.aoyagiSelectedWidthNat_selectedReducedWidths_of_lt`,
  `DLNFibre.DLN.Aoyagi.aoyagiSelectedWidthNat_selectedReducedWidths_fin`,
  `DLNFibre.DLN.Aoyagi.aoyagiSelectedWidthNat_selectedReducedWidths_nonneg_of_rank_le`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.nonempty_of_ell_pos`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.theorem2OrderFormula`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_ceilData`,
  `DLNFibre.DLN.Aoyagi.aoyagiTheorem2Lambda_average`,
  `DLNFibre.DLN.Aoyagi.aoyagiTheorem2Lambda_ceil`,
  `DLNFibre.DLN.Aoyagi.aoyagiTheorem2Lambda_expanded`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.selectedWidthAverage_eq_ceil`,
  `DLNFibre.DLN.Aoyagi.aoyagiTheorem2Lambda_average_eq_fromCeilData`, and
  `DLNFibre.DLN.Aoyagi.aoyagiTheorem2Lambda_average_eq_expanded_ofCeilData`
  in `lean/DLNFibre/DLN/Aoyagi/FinalFormula.lean`; current Definition 3
  bridge:
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.one_le_ell`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.one_le_aParam`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.terminalEndpoint_eq_zero`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.htildeLowerChain_last_eq_zero`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.htildeUpperChain_last_eq_zero`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.htildeLowerNat_last_eq_zero`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.htildeUpperNat_last_eq_zero`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.htildeUpperNat_pred_eq_sub_lastWidth`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.Hlast_eq_zero_of_htildeChainBounds`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.intervalSize_excess_sum_Icc_eq_theorem2OrderFormula`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.htildeIntervalValueSetNat_excess_sum_Icc_eq_theorem2OrderFormula`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.htildeIntervalValueSetNat_terminal_eq_singleton_zero`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.suppliedTerminalZero_Eq5_offsets_eq_intervalValueSetNat`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.lemma4_twoValueCount_of_htildeChainBounds`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.selectedWidth_le_pred_of_sourceSelectedInequality`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.htildeLowerNat_add_one_labelBounds_of_sourceSelectedInequality`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.lemma5Eq4_localData_of_sourceSelectedInequality`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.lemma5Eq5_labelBounds_of_sourceSelectedInequality`,
  and
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.lemma5Eq3_localData_of_sourceSelectedInequality_and_slack`
  plus source-data local wrappers
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.selected_strict_selectedReducedWidths`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.selectedWidth_le_pred_of_ceilData`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.htildeLowerNat_add_one_labelBounds_of_ceilData`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.lemma5Eq4_localData_of_ceilData`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.lemma5Eq5_labelBounds_of_ceilData`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.lemma5Eq3_localData_of_ceilData_and_slack`,
  and
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_selectedReducedWidthCeilData_of_rankWidth`
  in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`; current conditional
  finite-exponent bridge:
  `DLNFibre.DLN.Aoyagi.AoyagiTheorem2FiniteExponentFormulaHypothesis`,
  `lambda_eq_theorem2Lambda_fromCeilData_of_extractionHypothesis`,
  `lambda_eq_theorem2Lambda_average_of_extractionHypothesis`,
  `lambda_eq_theorem2Lambda_expanded_of_extractionHypothesis`,
  `poleOrder_eq_theorem2OrderFormula_of_extractionHypothesis`, and
  `lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_extractionHypothesis`
  in `lean/DLNFibre/DLN/Aoyagi/Theorem2FiniteExponentBridge.lean`; current
  active-ratio terminal-order bridge:
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_terminalMinimumLabels_card`,
  and
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_activePair_terminalMinimumLabels_card`
  in `lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`; current
  active chart-terminal-order bridge:
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_chartCount_terminalMinimumLabels_card`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_chartCount_terminalMinimumLabels_card`,
  and
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_activePair_chartCount_terminalMinimumLabels_card`
  in `lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`; current
  displayed-ratio count terminal-order bridge:
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_terminalMinimumLabels_card`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_ratioCount_terminalMinimumLabels_card`,
  and
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_activePair_ratioCount_terminalMinimumLabels_card`
  in `lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`; current
  counted-datum classifier terminal-order bridge:
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_terminalMinimumLabels_card_of_classifier`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card_of_classifier`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_chartCount_classifier`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_classifier`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_terminalMinimumLabels_card_of_classifier`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_terminalMinimumLabels_card_of_classifier`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_chartCount_classifier`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_ratioCount_classifier`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_terminalMinimumLabels_card_of_classifier`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_activePair_terminalMinimumLabels_card_of_classifier`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_activePair_chartCount_classifier`, and
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_activePair_ratioCount_classifier`
  in `lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`; current
  chart terminal-order bridge:
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedChartFinalBoundary_of_activePair_chartCount_terminalMinimumLabels_card`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedChartFinalBoundary_of_activePair_ratioCount_terminalMinimumLabels_card`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedChartFinalBoundary_of_activePair_chartCount_classifier`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedChartFinalBoundary_of_activePair_ratioCount_classifier`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_chart_activePair_chartCount_terminalMinimumLabels_card`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_chart_activePair_ratioCount_terminalMinimumLabels_card`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_chart_activePair_chartCount_classifier`, and
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_chart_activePair_ratioCount_classifier`
  in `lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`; current
  terminal-order equality bridge:
  finite formula, supplied-final-boundary, chart-final, and pair-form wrappers
  accepting
  `TC.terminalMinimumLabels.card = data.theorem2OrderFormula` directly in
  `lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderEqualityBridge.lean`; current
  Eq5 terminal-order bridge:
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedEq5EndpointBlockWidthOrderPayload`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedEq5EndpointBlockWidthOrderPayload.terminalMinimumLabels_card_eq_theorem2OrderFormula`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload`,
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedChartFinalBoundary_of_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload`,
  and
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_chart_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload`
  in `lean/DLNFibre/DLN/Aoyagi/Theorem2Eq5TerminalOrderBridge.lean`; current
  Definition 3 source-data Eq5 terminal-order bridge:
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_rankWidth_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload`
  and
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload`
  in `lean/DLNFibre/DLN/Aoyagi/Theorem2Eq5TerminalOrderBridge.lean`; current
  supplied final boundary:
  `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary`,
  `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.selectedWidths_eq_natCast_sub`,
  `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.selectedWidths_nonneg`,
  `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.selectedWidthNat_nonneg`,
  `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.selectedWidth_le_pred`,
  `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.lambda_eq_theorem2Lambda_fromCeilData`,
  `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.lambda_eq_theorem2Lambda_average`,
  `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.lambda_eq_theorem2Lambda_expanded`,
  `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.poleOrder_eq_theorem2OrderFormula`,
  `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula`, and
  `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.lambda_and_poleOrder_eq_expanded_and_orderFormula`,
  `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.lambda_eq_theorem2Lambda_average_selectedReducedWidths`, and
  `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.lambda_eq_theorem2Lambda_expanded_selectedReducedWidths`
  plus
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_rankWidth`
  and
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth`
  in `lean/DLNFibre/DLN/Aoyagi/Theorem2FinalAssembly.lean`.
- **Proved.** formula-only arithmetic: integer reduced-width notation,
  pointwise rank-width conversion/nonnegativity for reduced widths and
  selected reduced widths under explicit rank-width hypotheses,
  Definition 3 selected-sum average rewrite, equality of the average and
  ceiling displayed lambda formulas under supplied ceiling data, and equality
  of the ceiling and expanded displayed lambda formulas when `0 < ell`.  Also
  proved Definition 3 positivity wrappers, selected-sum wrappers for Lemma 4
  terminal endpoint zero, lower/upper Htilde terminal zero, a
  chain-bounds-to-terminal-zero wrapper, finite interval-count/order-formula
  rewrites, terminal same-coordinate/Eq5 singleton bookkeeping, a Lemma 4
  two-value count wrapper under supplied chain bounds and supplied two-value
  increments, and source-selected-inequality wrappers for selected-width and
  local equation `(4)`/`(5)` data.  The local equation `(3)` wrapper also
  requires the explicit one-unit slack hypothesis.  Also proved the
  Definition 3 source-data ceiling constructor: supplied value-level selected
  cutpoint inequalities plus `0<ell` determine an
  `AoyagiDefinition3CeilData` by Euclidean division, while selected-cutpoint
  existence remains supplied.  Also proved source-data local wrappers that
  project the strict selected-width inequality from
  `AoyagiDefinition3SourceData` into the local Definition 3/Lemma 5 arithmetic
  APIs, and a finite provenance aggregator packaging the selected reduced
  widths, ceiling datum, natural-width rewrites, nonnegativity, strict
  selected inequality, selected upper bounds, and Nat-indexed selected-width
  nonnegativity under an explicit source-range rank-width hypothesis.
  Selected cutpoints and the rank-width hypothesis remain supplied.  Also
  proved a conditional finite-exponent
  bridge: from supplied equalities
  `D.exponentMinimum = aoyagiTheorem2Lambda_fromCeilData ...` and
  `D.exponentOrder = data.theorem2OrderFormula`, plus
  `AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder`, Lean derives
  the ceiling-data, average, and expanded displayed `lambda` formulas and the
  displayed order formula.  Also proved a supplied final boundary packaging
  selected-width provenance, A0 extraction, and finite exponent formula
  hypotheses; it projects the displayed lambda/order formulas and finite
  selected-width provenance consequences without constructing the missing
  certificate.  Also proved a Definition 3 source-data final-boundary handoff:
  supplied source data and an explicit source-range rank-width hypothesis
  existentially produce the selected-width family and ceiling datum used by
  `AoyagiTheorem2SuppliedFinalBoundary` and
  `AoyagiTheorem2SuppliedChartFinalBoundary`, while A0 extraction and finite
  exponent formula hypotheses remain supplied for the produced data.  Also
  proved an active-ratio terminal-order final-socket bridge:
  a supplied active coordinate realizing the displayed lambda and a supplied
  lower bound against every active ratio fill the exponent-minimum field,
  while the supplied chart/order equality and supplied Lemma 5 terminal-order
  obstruction fill the order field.  Also proved an active chart-terminal
  final-socket bridge: a supplied chart whose global-minimum coordinate count
  is `TC.terminalMinimumLabels.card`, plus an all-chart upper bound by that
  count, replaces the raw chart/order equality.  Also proved a displayed-ratio
  count bridge: chart counts may be supplied at the displayed Theorem 2 lambda
  value and are rewritten through the active-ratio minimum certificate to the
  `D.exponentMinimum` counts used by `D.exponentOrder`.  Also proved
  counted-datum classifier variants of the same terminal-order sockets, where
  a supplied `TC.TerminalMinimumCountDatumClassifier` replaces only the raw
  terminal upper-bound hypothesis.  Also proved chart-certificate variants of
  the active chart-count, displayed-ratio count, and counted-datum classifier
  terminal-order handoffs, preserving
  `AoyagiTheorem2SuppliedChartFinalBoundary` and the chart-level extraction
  hypothesis rather than forgetting to bare exponent data.  Selected rank-width
  hypotheses and the strict source-selected inequality remain explicit
  auxiliary theorem inputs where used.  Also proved terminal-order equality
  bridge variants: an exact equality
  `TC.terminalMinimumLabels.card = data.theorem2OrderFormula` now feeds the
  finite formula, supplied final-boundary, chart-final, and pair-form sockets
  directly.  This is only a finite downstream handoff; it does not prove the
  exact terminal count, A5 source exactness, chart production, pole order
  without A0, normal crossings, or RLCT.  Also proved an Eq5 terminal-order
  bridge that packages the supplied Eq5 endpoint block-width payload, extracts
  the exact terminal count, and feeds it into the displayed-ratio
  finite/final/chart-final A6 sockets; final-boundary wrappers use the same
  selected cutpoints carried by the supplied Eq5 payload.  This is not a
  source proof of Eq5 families, Lemma 5 exactness, active-ratio bounds, chart
  counts, chart production, pole order, or RLCT.  Also proved a Definition 3
  source-data Eq5 terminal-order bridge: source data and a source-range
  rank-width hypothesis existentially produce `m,data`, and a supplied Eq5
  payload/active-ratio/chart-count callback for that produced pair builds the
  supplied final-boundary and chart-final-boundary sockets.  The callback
  requires `P.cut = C`, so the Eq5 payload and Definition 3 source data use
  the same selected cutpoints.  This is not selected-cutpoint construction,
  rank-width from matrix data, Eq5 family construction, Lemma 5 exactness,
  active-ratio bounds, chart counts, chart production, pole order, or RLCT.
- **Assumed.** cited analytic interface A0 and source hypotheses.
- **Cited.** A0 only, if expedition succeeds as intended.
- **Deferred.** existence and uniqueness of the selected cutpoints and selected
  value set, source parameter provenance from concrete Aoyagi matrix data
  beyond the supplied rank-width/source-data package, proof of rank-width
  inequalities from concrete matrix dimensions and a rank-`r` product, the
  finite exponent formula equalities
  from a normal-crossing certificate, the Lemma 4 two-value increment proof,
  Lemma 5 chart-family construction/coverage and no-extra classifier,
  conversion of the finite count to pole order, normal crossings, final RLCT
  theorem, and formal analytic extraction theorem.

Latest A4/A0 Case 1 exponent-coordinate bridge:
`Case1FiniteExponentBridge.lean` now contains
`Case1SelectedEntryExponentCoordinateBridge`,
`Case1SelectedEntryA0ExponentCoordinateBridge`, and
`Case1SelectedOldUnitA0ExponentCoordinateBridge`.  These prove that a supplied
coordinate with Case 1 selected-entry exponents `lossExp = 1` and
`jacobianPriorExp = J1 * (n(S+1)-J)` is active and has ratio
`(1 + J1 * (n(S+1)-J)) / 2`; under a supplied all-active lower bound, this
ratio is the finite exponent minimum.  The selected-old source-moving wrapper
carries `Case1SelectedOldUnitSuppliedChartFamilyBoundary`; it does not
construct the A0 exponent data, the coordinate, a chart certificate, a global
lower bound, chart counts, pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case1-a0-exponent-coordinate-bridge-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-a0-case1-exponent-coordinate-bridge.md`.

Latest A6 Case 1 finite-formula and chart-final wrappers:
`Case1Theorem2FiniteExponentBridge.lean` now contains
`Case1SelectedOldUnitA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData`
and
`Case1SelectedOldUnitA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le`.
`Case1Theorem2ChartFinalBridge.lean` now contains
`Case1SelectedOldUnitA0ExponentCoordinateBridge.theorem2SuppliedChartFinalBoundary_of_forall_le_of_candidateRatio_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le`.
These consume supplied selected-old Case 1/A0 coordinate data, supplied
active-ratio lower bounds, supplied candidate-ratio/Theorem 2 lambda
identification, supplied order or chart-count facts, selected-width
provenance, and chart-level extraction.  They do not prove any of those
supplied obligations, chart production, pole order, or RLCT.  Reproductions:
`threads/06-dln-translation/reproduction-case1-theorem2-finite-formula-bridge-a6.md`
and
`threads/06-dln-translation/reproduction-case1-theorem2-chart-final-bridge-a6.md`.
Reviews:
`threads/06-dln-translation/review-case1-theorem2-finite-formula-bridge-a6.md`
and
`threads/06-dln-translation/review-case1-theorem2-chart-final-bridge-a6.md`.

Latest A4/A0 source-chart selected-entry microcertificate adapter:
`SelectedEntryNormalCrossing.lean` now contains source-point presentation
lemmas for `case2DisplayedCenterSqFormalJacobianChartCertificate`, including
`sourceChartPoint`, `chartMap_sourceChartPoint_eq`,
`loss_sourceChartPoint_eq_centerSq`, `lossUnit_sourceChartPoint_eq`,
`jacobianPrior_sourceChartPoint_eq_det`, `loss_monomial_sourceChartPoint`,
and `jacobianPrior_monomial_sourceChartPoint`.  These identify the existing
one-chart selected-entry microcertificate at the displayed continuing Case 2
source chart point.  They do not prove chart coverage, source production,
transition regularity, analytic unit neighbourhood control, an analytic
Jacobian/volume-form theorem, total DLN loss control, global A0 normal
crossings, pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-chart-selected-entry-microcertificate-adapter-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-chart-selected-entry-microcertificate-adapter.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-chart-selected-entry-microcertificate-adapter-a4.md`.

Latest A4/A0 Case 1 source-chart selected-entry microcertificate adapter:
`SelectedEntryNormalCrossing.lean` now contains generic source-point lemmas
under `selectedEntryCenterSqFormalJacobianChartCertificate` and Case 1
specializations under
`case1SelectedOldCenterSqFormalJacobianChartCertificate` and
`case1DisplayedRowStripCenterSqFormalJacobianChartCertificate`.  These
evaluate the finite selected-entry source chart points inside the local
one-chart microcertificates for the selected-old finite token and the
displayed row-strip pivot.  They are not source production of the hidden old
label, chart coverage, transition regularity, analytic Jacobian control,
total loss control, global A0 normal crossings, pole order, or RLCT.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case1-source-chart-selected-entry-microcertificate-adapter-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-source-chart-selected-entry-microcertificate-adapter.md`.
Review:
`threads/04-blow-up-certificate/review-case1-source-chart-selected-entry-microcertificate-adapter-a4.md`.

Latest A4/A0 selected-entry local ratio chart count:
`SelectedEntryNormalCrossing.lean` now proves local ratio-specific chart-count
facts for the generic selected-entry microcertificate, the displayed Case 2
microcertificate, and the two displayed Case 1 microcertificates.  The
chartwise count at the local selected-entry ratio is `1`, and the chartwise
minimum-coordinate count is also `1`.  This is only finite-local
`countInChartAtRatio` bookkeeping; it is not a global A0 chart family,
all-chart upper bound, global pole-order count, source production, chart
coverage, analytic Jacobian control, or RLCT extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-ratio-chart-count-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-ratio-chart-count.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-ratio-chart-count-a4.md`.

Latest A4/A0 Case 2 local chart-certificate contribution:
`SelectedEntryNormalCrossing.lean` now proves
`case2DisplayedCenterSqFormalJacobianChartCertificate.localChartCertificateContribution_summary`.
This bundles the existing generic source bridge for the local
microcertificate's own exponent data with the local ratio, finite minimum,
ratio-count, minimum-count, and finite order.  The ratio conjunct follows the
bridge projection and hence the source certificate's cardinality equality.
This is not global A0 data, chart coverage, a global lower bound, a full
chart-count theorem, pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-local-chart-certificate-contribution-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-local-chart-certificate-contribution.md`.
Review:
`threads/04-blow-up-certificate/review-case2-local-chart-certificate-contribution-a4.md`.

Latest A4/A0 Case 1 local chart-certificate contributions:
`Case1FiniteExponentBridge.lean` now proves
`case1SelectedOldCenterSqFormalJacobianChartCertificate.localChartCertificateContribution_summary`
and
`case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.localChartCertificateContribution_summary`.
These bundle the existing generic Case 1 selected-entry bridge for each local
microcertificate's own exponent data with the local ratio, finite minimum,
ratio-count, minimum-count, and finite order.  They do not construct global A0
data, the hidden selected-old source label, chart coverage, a global lower
bound, a full chart-count theorem, Theorem 2 pole order, `theta`, or RLCT.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case1-local-chart-certificate-contribution-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-local-chart-certificate-contribution.md`.
Review:
`threads/04-blow-up-certificate/review-case1-local-chart-certificate-contribution-a4.md`.

Latest A4/A0 Case 1/Case 2 selected-entry multi-chart specializations:
`SelectedEntryNormalCrossing.lean` now proves the finite all-pivot Case 2
certificate
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate`, its
rewritten ratio/minimum/count/order facts for the selected-coordinate count
`(prefixMinNat n S - J) * (n(S+1)-J)`, and its exponent-array bridge/summary
for arbitrary finite pivot charts.  `SelectedEntryNormalCrossing.lean` also
proves the finite all-pivot Case 1 certificate
`case1CenterSqFormalJacobianChartFamilyCertificate` and its rewritten
ratio/minimum/count/order facts for `1 + J1 * (n(S+1)-J)`;
`Case1FiniteExponentBridge.lean` adds the matching Case 1 exponent-array
bridge/summary.  These are finite certificate specializations only.  The Case
2 arbitrary-chart bridge uses equality of erased-center cardinalities with the
displayed pivot, not source identity of arbitrary pivots.  This checkpoint
does not prove arbitrary-pivot source formulas, `Q/P` source production, chart
coverage, transition regularity, analytic Jacobian data, global A0 lower
bounds, pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case1-case2-selected-entry-multi-chart-specializations-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-case2-selected-entry-multi-chart-specializations.md`.
Review:
`threads/04-blow-up-certificate/review-case1-case2-selected-entry-multi-chart-specializations-a4.md`.

Latest A4 selected-entry finite chart coverage:
`SelectedEntryNormalCrossing.lean` now proves finite map coverage for the
selected-entry chart maps.  The one-pivot chart covers any value with nonzero
selected pivot coordinate and covers the zero value by the zero source point.
The all-pivot chart family covers every value on a nonempty finite center by
choosing a nonzero coordinate as pivot, or an arbitrary pivot for the zero
value.  This is finite selected-entry map coverage only; it does not prove
analytic atlas coverage, transition regularity, arbitrary non-displayed
Aoyagi source-coordinate formulas, source production, analytic Jacobian data,
normal-crossing certificate production, pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-finite-chart-coverage-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-finite-chart-coverage.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-finite-chart-coverage-a4.md`.

Latest A4 Case 1/Case 2 selected-entry finite coverage:
`SelectedEntryNormalCrossing.lean` now specializes the generic finite
all-pivot coverage theorem to the existing Case 2 residual-block and Case 1
center-generator certificate wrappers:
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.exists_chartPoint_chartMap_eq_value`
and
`case1CenterSqFormalJacobianChartFamilyCertificate.exists_chartPoint_chartMap_eq_value`.
These wrappers prove finite chart-map coverage for the two Aoyagi finite
centers only.  They do not prove arbitrary-pivot source production, analytic
atlas coverage, transition regularity, source production of successors,
analytic Jacobian data, normal-crossing certificate production, pole order, or
RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case1-case2-selected-entry-finite-coverage-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-case2-selected-entry-finite-coverage.md`.
Review:
`threads/04-blow-up-certificate/review-case1-case2-selected-entry-finite-coverage-a4.md`.

Latest A4/A0 Case 2 selected-entry extraction handoff:
`SelectedEntryNormalCrossing.lean` now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.lambda_and_poleOrder_eq_selectedCoordinateCount_div_two_and_one_of_extractionHypothesis`.
It consumes a supplied chart-level extraction hypothesis for the concrete Case
2 residual-block all-pivot finite selected-entry certificate and rewrites the
reported `lambda` to
`(((prefixMinNat n S - J) * (n(S+1)-J)) : Q) / 2`, with local finite
`poleOrder = 1`.  This is not construction of the extraction hypothesis,
chart coverage, transition regularity, arbitrary-pivot source production,
global A0 data, Aoyagi Theorem 2 order data, or RLCT extraction.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-selected-entry-extraction-handoff-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-selected-entry-extraction-handoff.md`.
Review:
`threads/04-blow-up-certificate/review-case2-selected-entry-extraction-handoff-a4.md`.

Latest A4/A0 Case 2 all-pivot source-selected monomial/principalization adapter:
`SelectedEntryNormalCrossing.lean` now states the all-pivot finite
selected-entry certificate's center-ideal principalization, loss source-point
equality, loss-unit equality, formal Jacobian/prior determinant equality, and
loss/Jacobian monomial identities in the source-selected chart-map names for
the pivot enumerated by each chart.  This is finite selected-entry algebra in
source-selected names only; it is not arbitrary-pivot source production,
analytic chart coverage, transition regularity, analytic Jacobian/volume
control, global normal crossings, pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-all-pivot-source-selected-monomial-principalization-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-all-pivot-source-selected-monomial-principalization.md`.
Review:
`threads/04-blow-up-certificate/review-case2-all-pivot-source-selected-monomial-principalization-a4.md`.

Latest A4/A0 Case 2 chart-index source-selected boundary/QP bridge:
`SelectedEntryNormalCrossing.lean` now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelectedBoundary_of_chart_case2Succ_updateSelected`
and
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelectedQP_sourceChartMap_of_chart_case2Succ_updateSelected`.
For chart index `c`, the finite chart enumeration supplies a pivot
`p_c in case2ResidualBlockPivotEntries n S J`.  The boundary wrapper passes
`p_c.2` into the existing source-selected supplied-boundary constructor with
post-state `pre.case2Succ u` and corrected selected-label exponent updates.
The `Q/P` wrapper then applies the existing
`sourceSelectedQP_sourceChartMap` projection for that boundary.  This is only
a chart-index-to-supplied-boundary adapter plus projection of an existing
finite source-selected matrix identity.  It does not prove arbitrary-pivot
source production, that Aoyagi displays every non-top-left chart, chart or
transition regularity, chart coverage, chart-produced recurrence/exponent
data, analytic Jacobian/volume control, global normal crossings, pole order,
or RLCT extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-chart-index-source-selected-boundary-qp-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-chart-index-source-selected-boundary-qp.md`.
Review:
`threads/04-blow-up-certificate/review-case2-chart-index-source-selected-boundary-qp-a4.md`.

Latest A4 Case 2 source-selected finite chart production:
`SelectedEntryNormalCrossing.lean` now proves
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exists_sourceChartPoint_chartMap_eq_value`
and
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.exists_sourceSelectedChartMap_eq_value`.
The generic theorem upgrades the existing finite selected-entry chart coverage
to witnesses written as `sourceChartPoint` with ambient residual coordinates.
The Case 2 theorem specializes this to the residual-block center and rewrites
the produced chart map in `case2SourceSelectedChartMapOfMem` names for the
chart-selected pivot.  This is finite source-coordinate production for center
values only; it does not prove analytic atlas coverage, transition regularity,
source production of recurrence successors or suffixes, global normal
crossings, pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-selected-finite-chart-production-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-selected-finite-chart-production.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-selected-finite-chart-production-a4.md`.

Latest A4 Case 2 source-selected finite transition:
`BlowupArithmetic.lean` and `SelectedEntryNormalCrossing.lean` now prove
`selectedEntryChartMap_transition_eq_of_target_normalized_ne_zero`,
`case2SourceSelectedChartMapOfMem_transition_eq_of_target_normalized_ne_zero`,
and
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelected_transition_chartMap_eq_of_target_normalized_ne_zero`.
These are finite selected-entry overlap identities.  The denominator is the
target normalized coordinate, not the finite center value `u` times that
coordinate, so the statement does not exclude exceptional-divisor overlap
points.  This is not analytic transition regularity, chart coverage, Q/P
reduced-block transition, successor/suffix production, global normal
crossings, pole order, or RLCT extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-selected-finite-transition-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-selected-finite-transition.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-selected-finite-transition-a4.md`.

Latest A4 Case 2 source-selected Schur complement:
`BlowupArithmetic.lean` now proves
`pivotFirstSchurComplement_apply`,
`selectedEntryNormalizedMap_schurComplement_transition_mul_sq`, and
`case2SourceSelectedNormalizedBlockOfMem_schurComplement_apply`.
The first theorem is the finite ring-level scalar identity for the
lower-right block `D - x*y` after selected-pivot `Q` normalisation.  The second
formalises the denominator-cleared overlap calculation
`x_ab^2 * z_ij = x_ab*x_ij - x_ib*x_aj` under the normalized-coordinate
condition `x_ab != 0`.  The third is the Case 2 source-coordinate wrapper for
a supplied residual-block pivot.  This is finite matrix/field algebra only:
it does not prove analytic transition regularity, chart coverage, source
production of successor matrices or suffixes, global normal crossings, pole
order, or RLCT extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-selected-schur-complement-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-selected-schur-complement.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-selected-schur-complement-a4.md`.

Latest A4 Case 2 chart-index Schur transition:
`BlowupArithmetic.lean` now proves
`case2SourceSelectedNormalizedMapOfMem_schurComplement_transition_mul_sq`,
and `SelectedEntryNormalCrossing.lean` exposes the chart-indexed adapter
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelected_schurComplement_transition_mul_sq`.
These are supplied-pivot and chart-indexed wrappers for the denominator-cleared
finite identity `x_ab^2*z_ij = x_ab*x_ij - x_ib*x_aj` under the normalized
coordinate hypothesis `x_ab != 0`.  The chart-indexed form gets both pivot
memberships from `finsetSubtypeChartEquiv`.  Its off-pivot row/column indices
are ambient `ℕ` complements, not residual-row/residual-column subtype
complements.  This is finite selected-entry algebra only: no analytic
transition regularity, chart coverage, successor/following-factor production,
global normal crossings, pole order, or RLCT extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-chart-index-schur-transition-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-chart-index-schur-transition.md`.
Review:
`threads/04-blow-up-certificate/review-case2-chart-index-schur-transition-a4.md`.

Latest A4 Case 2 residual-subtype Schur transition:
`BlowupArithmetic.lean` now proves
`case2SourceSelectedNormalizedBlockOfMem_schurComplement_transition_mul_sq`.
It adapts the denominator-cleared Schur-overlap identity
`x_ab^2*z_ij = x_ab*x_ij - x_ib*x_aj` from ambient off-pivot complements to
the residual-row/residual-column subtype complements used by the
source-selected lower-right `Q/P` block.  The proof is only a finite adapter:
it reads the source labels as `i.1.1` and `j.1.1` and invokes the
supplied-pivot source-coordinate theorem.  The denominator is still the
normalized target coordinate `x_ab`, not `u*x_ab`.  This is not
successor/following-factor production, analytic transition regularity, chart
coverage, normal crossings, pole order, or RLCT extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-residual-subtype-schur-transition-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-residual-subtype-schur-transition.md`.
Review:
`threads/04-blow-up-certificate/review-case2-residual-subtype-schur-transition-a4.md`.

Latest A4 selected-entry transition point:
`SelectedEntryNormalCrossing.lean` now defines
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint`
and the Case 2 wrapper
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint`,
with chart-map equality theorems under the normalized target-coordinate
nonzero hypothesis.  The construction sends source chart coordinates
`d_e = u*x_e` to target coordinates `u_q = u*x_q` and `y_e = x_e/x_q`, and
proves equality of finite chart maps.  This is finite selected-entry
transition-point algebra only: no analytic atlas coverage, transition
regularity, source production of `Csucc` or `C'^(S+1)`, suffix production,
normal crossings, pole order, or RLCT extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-transition-point-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-transition-point.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-transition-point-a4.md`.

Latest A4 chart-index residual-subtype Schur transition:
`SelectedEntryNormalCrossing.lean` now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelectedBlock_schurComplement_transition_mul_sq`.
This is the chart-indexed residual-row/residual-column subtype version of the
Case 2 denominator-cleared selected-entry Schur transition, reading target
lower-right `Q/P` block indices through source labels `i.1.1` and `j.1.1`.
It remains finite coordinate algebra only: no analytic transition regularity,
chart coverage, source-displayed all-pivot atlas, successor/following-factor
production, normal crossings, pole order, or RLCT extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-chart-index-residual-subtype-schur-transition-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-chart-index-residual-subtype-schur-transition.md`.
Review:
`threads/04-blow-up-certificate/review-case2-chart-index-residual-subtype-schur-transition-a4.md`.

Latest A4 selected-entry transition inverse:
`BlowupArithmetic.lean` now proves
`selectedEntryNormalizedMap_transition_eq_div_of_target_normalized_ne_zero`,
and `SelectedEntryNormalCrossing.lean` proves generic and Case 2 chart-point
self/inverse laws for `sourceChartTransitionPoint`.  The inverse theorem keeps
the denominator as the normalized target coordinate `x_q != 0` and returns the
source chart point, avoiding any raw ambient residual-function equality claim.
This is finite coordinate algebra only: no analytic transition regularity,
chart coverage, source-displayed all-pivot atlas, successor/following-factor
production, normal crossings, pole order, or RLCT extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-transition-inverse-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-transition-inverse.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-transition-inverse-a4.md`.

Latest A4 selected-entry transition cocycle:
`BlowupArithmetic.lean` now proves
`selectedEntryNormalizedMap_transition_target_ne_zero_of_source_ne_zero` and
`selectedEntryNormalizedMap_transition_transition_eq_div_of_ne_zero`.
`SelectedEntryNormalCrossing.lean` proves the generic and Case 2 chart-point
cocycle laws
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_cocycle_of_target_normalized_ne_zero`
and
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_cocycle_of_target_normalized_ne_zero`.
The hypotheses are the source normalized nonzero coordinates for the middle
and target pivots, and the conclusion is a target chart-point identity for
source-to-middle-to-target versus source-to-target.  This is finite
selected-entry coordinate algebra only: no analytic transition regularity,
chart coverage, open-neighbourhood gluing, source-displayed all-pivot atlas,
successor/following-factor production, normal crossings, pole order, or RLCT
extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-transition-cocycle-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-transition-cocycle.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-transition-cocycle-a4.md`.

Latest A4 selected-entry Schur transition cocycle:
`BlowupArithmetic.lean` now proves
`selectedEntryNormalizedMap_schurComplement_transition_cocycle`,
`case2SourceSelectedNormalizedMapOfMem_schurComplement_transition_cocycle`,
and
`case2SourceSelectedNormalizedBlockOfMem_schurComplement_transition_cocycle`.
`SelectedEntryNormalCrossing.lean` proves the chart-indexed residual-subtype
wrapper
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelectedBlock_schurComplement_transition_cocycle`.
These theorems say that the target lower-right Schur entry in the finite
selected-pivot `Q/P` block is route-independent on normalized triple overlaps:
source-to-middle-to-target and source-to-target give the same target Schur
entry.  This is finite selected-entry coordinate algebra only, not analytic
transition regularity, chart coverage, source production of successor
residual/following factors, normal crossings, pole order, or RLCT extraction.
Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-schur-transition-cocycle-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-schur-transition-cocycle.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-schur-transition-cocycle-a4.md`.

Latest A5 base-value interval-membership cleanup:
`Lemma5SuppliedFamily.lean` now proves
`aoyagiLemma5BaseValue_mem_intervalValueSetNat_of_baseChainBounds`.
It replaces a bare `baseValue_mem` assumption by explicit supplied
base-chain bounds and a supplied equality identifying the interior base-chain
coordinates with `baseValue`.  This remains finite interval bookkeeping only:
no base branch construction from Eq3/Eq4/Eq5, source-label legality, no-extra
coverage, injectivity, back-to-label coverage, terminal exactness, pole order,
normal crossings, or RLCT extraction.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-base-value-interval-membership-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-base-value-interval-membership.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-base-value-interval-membership-a5.md`.

Latest A4 Case 2 transition-generated Q/P package:
`SelectedEntryNormalCrossing.lean` now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_sourceSelectedQP_package_of_target_normalized_ne_zero`.
For a source-to-target finite selected-entry transition with normalized target
coordinate `d != 0`, it uses the transition-generated target data
`targetU = u*d` and `targetResidual r = x_r/d` to package three facts:
chart-map equality with the source chart point, the existing supplied
target-pivot source-selected `Q/P` identity, and the denominator-cleared
target lower-right Schur formula.  This is finite selected-entry and
residual-block coordinate algebra only: no analytic transition regularity,
chart coverage, source-displayed all-pivot atlas, chart-produced post-data,
successor/following-factor production, normal crossings, pole order, or RLCT.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-transition-generated-qp-package-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-transition-generated-qp-package.md`.
Review:
`threads/04-blow-up-certificate/review-case2-transition-generated-qp-package-a4.md`.

Latest A4 Case 2 transition-generated displayed frontier:
`SelectedEntryNormalCrossing.lean` now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.displayedChartIndex`,
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.finsetSubtypeChartEquiv_displayedChartIndex`,
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_frontierBoundaryPackages_of_displayed_normalized_ne_zero`,
and
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_continuingCertificate_of_displayed_normalized_ne_zero`.
On the displayed-pivot overlap `x_(J+1,J+1) != 0`, an arbitrary all-pivot
source chart is rewritten as displayed top-left selected-entry data
`targetU = u*x` and `targetResidual = x_-/x`; those transition-generated
displayed data satisfy the existing displayed source-chart frontier package,
and under the continuing guard they satisfy the displayed continuing
reindexed source-chart certificate.  This is finite selected-entry/source-
frontier algebra only: no analytic atlas transition, coverage, source-produced
successor or suffix data, normal crossings, pole order, or RLCT.  It does not
prove the separate transition-generated substitution-block rewrite.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-transition-generated-displayed-frontier-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-transition-generated-displayed-frontier.md`.
Review:
`threads/04-blow-up-certificate/review-case2-transition-generated-displayed-frontier-a4.md`.

Latest A4 Case 2 transition-generated substitution-block rewrite:
`BlowupArithmetic.lean` now proves
`case2SourceSelectedSubstitutionBlockOfMem_transition_eq_of_target_normalized_ne_zero`,
and `SelectedEntryNormalCrossing.lean` proves the chart-indexed wrapper
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_sourceSelectedSubstitutionBlock_eq_of_target_normalized_ne_zero`.
On the overlap where the target normalized coordinate `d = x_q` is nonzero,
the transition-generated target data `targetU = u*d` and
`targetResidual r = x_r/d` have the same finite residual-block substitution
matrix as the original source chart: `Sub_q(u*d,x/d) = Sub_p(u,x)`.  This is
finite selected-entry substitution-block algebra only: no normalized-block
equality, target Schur-complement rewrite, analytic transition regularity,
chart coverage, source production, normal crossings, pole order, or RLCT.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-transition-generated-substitution-block-rewrite-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-transition-generated-substitution-block-rewrite.md`.
Review:
`threads/04-blow-up-certificate/review-case2-transition-generated-substitution-block-rewrite-a4.md`.

Latest A4 Case 2 transition-generated `Q/P` source-substitution package:
`SelectedEntryNormalCrossing.lean` now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_sourceSelectedQP_sourceSubstitution_package_of_target_normalized_ne_zero`.
On a normalized source-to-target selected-entry overlap, it records chart-map
equality, the substitution-block equality, the target-pivot `Q/P` identity
with only its left substituted residual block rewritten to the original source
substitution block, and the denominator-cleared target Schur formula.  The
normalized block, target Schur block, target successor weights, and
transported following factor remain target-pivot data.  This is finite
coordinate algebra only: no source production, analytic transition regularity,
chart coverage, normal crossings, pole order, or RLCT.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-transition-generated-qp-source-substitution-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-transition-generated-qp-source-substitution.md`.
Review:
`threads/04-blow-up-certificate/review-case2-transition-generated-qp-source-substitution-a4.md`.

Latest A4 Case 2 displayed `Q/P` source-substitution continuing handoff:
`SelectedEntryNormalCrossing.lean` now specializes the transition-generated
target-pivot `Q/P` source-substitution package to the displayed chart
`(J+1,J+1)` and bundles it with the displayed frontier package and, under the
continuing guard, the displayed continuing reindexed source-chart certificate.
Only the left substituted residual block in the `Q/P` identity is rewritten to
the original source selected substitution block; the normalized block, Schur
block, successor weights, transported following factor, and continuing
certificate remain displayed target data.  The deeper displayed reindexed
next-source product with the source-side substitution block is not proved in
this slice.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-transition-generated-displayed-qp-source-substitution-continuing-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-transition-generated-displayed-qp-source-substitution-continuing.md`.
Review:
`threads/04-blow-up-certificate/review-case2-transition-generated-displayed-qp-source-substitution-continuing-a4.md`.

Latest A4 Case 2 displayed reindexed product source-substitution:
`BlowupArithmetic.lean` now provides a supplied-block variant of the displayed
reindexed next-source product, and `SelectedEntryNormalCrossing.lean` applies
it to transition-generated displayed data on the overlap
`x_(J+1,J+1) != 0`.  The resulting theorem rewrites only the left
substitution block to the original source selected-entry block.  The right
side remains displayed transition-generated data with formula-level successor
following factor; this is not source production of `Csucc`, suffixes,
successor charts, transition regularity, chart coverage, normal crossings,
pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-displayed-reindexed-product-source-substitution-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-reindexed-product-source-substitution.md`.
Review:
`threads/04-blow-up-certificate/review-case2-displayed-reindexed-product-source-substitution-a4.md`.

Latest A4 selected-entry transition microcertificate evaluation:
`SelectedEntryNormalCrossing.lean` now evaluates the finite selected-entry
normal-crossing microcertificate at transition-generated target chart points.
The generic selected-entry family proves source-facing loss, target loss-unit,
target formal-Jacobian, and monomial adapters for `sourceChartTransitionPoint`;
the Case 2 residual-block namespace exposes the same facts in
source-selected names.  The denominator remains the normalized target
coordinate `x_q`, and the target unit/formal determinant are not rewritten to
source-chart data.  This is finite selected-entry chart algebra only: no
source-target unit equality, analytic transition regularity, chart coverage,
source production, global A0 normal crossings, pole order, or RLCT.
Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-transition-microcertificate-evaluation-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-transition-microcertificate-evaluation.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-transition-microcertificate-evaluation-a4.md`.

Latest A4 Case 2 supplied-successor reindexed product:
`BlowupArithmetic.lean` now adds
`Case2DisplayedReindexedNextSourceProductEqWithSubstitutionBlockAndCsucc`,
`sourceChartMap_reindexedNextSourceProduct_fromCase2SuccCorrectedPostData_of_substitutionBlock_eq_of_Csucc_eq`,
and
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.reindexedNextSourceProduct_of_substitutionBlock_eq`.
These consume an explicit equality
`Csucc = case2DisplayedSourceSuccessorFollowingFactor ... C` and restate the
already-proved displayed reindexed product with the supplied successor
following object on the right-hand side.  The same row-operation witness and
corrected post-data are reused.  This is finite congruence only: it does not
construct `Csucc`, suffix/following-product data, successor chart families,
transition regularity, chart coverage, normal crossings, pole order, or RLCT.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-supplied-successor-reindexed-product-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-supplied-successor-reindexed-product.md`.
Review:
`threads/04-blow-up-certificate/review-case2-supplied-successor-reindexed-product-a4.md`.

Latest A4 Case 2 displayed transition microcertificate contribution:
`SelectedEntryNormalCrossing.lean` now adds
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_microcertificateContribution_summary_of_displayed_normalized_ne_zero`.
It packages the transition from a chart in the finite all-pivot selected-entry
wrapper to Aoyagi's displayed Case 2 chart, constructs the displayed
continuing finite center-square/formal-Jacobian certificate for the
transition-generated displayed data, and records finite loss/unit/formal
Jacobian-prior identities plus local finite ratio/minimum/count/order facts.
This is finite chart-certificate plumbing; it does not claim that Aoyagi
printed the all-pivot atlas, and it does not prove source production, analytic
transition regularity, chart coverage, global A0 normal crossings, pole order,
or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-displayed-transition-microcertificate-contribution-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-transition-microcertificate-contribution.md`.
Review:
`threads/04-blow-up-certificate/review-case2-displayed-transition-microcertificate-contribution-a4.md`.
