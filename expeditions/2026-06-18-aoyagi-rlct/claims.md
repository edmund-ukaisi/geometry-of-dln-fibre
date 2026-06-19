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
  edges is proved. The full source Theorem 3 claim remains blocked.
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
  `DLNFibre.DLN.Aoyagi.identityCornerForm`,
  `DLNFibre.DLN.Aoyagi.identityCornerDetChart`,
  `DLNFibre.DLN.Aoyagi.identityCornerDetChart_of_identityCornerForm`, and
  `DLNFibre.DLN.Aoyagi.identityCornerForm_upperUnitriangular_mul`, plus
  one-edge elimination theorems
  `DLNFibre.DLN.Aoyagi.productReduction_blockDiagonal_mul_fromBlocks_one_zero_rightElim_indexed`,
  `DLNFibre.DLN.Aoyagi.productReduction_blockDiagonal_mul_eq_fromBlocks_one_zero_rightElim_indexed`, and
  `DLNFibre.DLN.Aoyagi.productReduction_blockDiagonal_mul_identityCornerForm_rightElim`
  in the same file; entry-ideal transport lemmas in
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
  plus endpoint total-product theorem
  `DLNFibre.DLN.Aoyagi.toMatrix_chainMap_zero_last_ker_basisOfIsCompl_eq_fromBlocks_one_zero_zero`
  and finite-dimensional endpoint theorem
  `DLNFibre.DLN.Aoyagi.toMatrix_chainMap_zero_last_ker_finiteDimensional_eq_fromBlocks_one_zero_zero`
  plus finite chart-data existence theorems
  `DLNFibre.DLN.Aoyagi.throughSubspaceChartDataOfFiniteDimensional`,
  `DLNFibre.DLN.Aoyagi.nonempty_throughSubspaceChartDataOfFiniteDimensional`,
  `DLNFibre.DLN.Aoyagi.exists_toMatrix_throughSubspaceEdge_finiteDimensional_eq_fromBlocks_one_zero`,
  `DLNFibre.DLN.Aoyagi.exists_unitriangular_toMatrix_throughSubspaceEdge_finiteDimensional_eq_fromBlocks_one_zero`,
  `DLNFibre.DLN.Aoyagi.disjoint_ker_reverse_total_of_disjoint_ker_paperChainMap`,
  `DLNFibre.DLN.Aoyagi.isCompl_ker_reverse_total_of_isCompl_ker_paperChainMap`,
  `DLNFibre.DLN.Aoyagi.paperAdaptedReverseEdgeMatrix`,
  `DLNFibre.DLN.Aoyagi.paperUnitriangularLeft`,
  `DLNFibre.DLN.Aoyagi.identityCornerForm_paperAdaptedReverseEdgeMatrix`,
  `DLNFibre.DLN.Aoyagi.identityCornerDetChart_paperAdaptedReverseEdgeMatrix`,
  `DLNFibre.DLN.Aoyagi.identityCornerDetChart_unitriangular_paperAdaptedReverseEdgeMatrix`,
  `DLNFibre.DLN.Aoyagi.productReduction_paperAdaptedReverseEdgeMatrix_rightElim`,
  `DLNFibre.DLN.Aoyagi.exists_toMatrix_reverseEdge_finiteDimensional_eq_fromBlocks_one_zero`,
  `DLNFibre.DLN.Aoyagi.exists_unitriangular_toMatrix_reverseEdge_finiteDimensional_eq_fromBlocks_one_zero`,
  `DLNFibre.DLN.Aoyagi.toMatrix_paperChainMap_ker_finiteDimensional_eq_fromBlocks_one_zero_zero`,
  and
  `DLNFibre.DLN.Aoyagi.exists_isCompl_ker_throughSubspaceChartDataOfFiniteDimensional`
  in `lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`; full Theorem 3 target
  blocked.
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
  corollary in the reversed Aoyagi order.
- **Assumed.** matrix dimensions encoded by types; determinant-unit chart
  hypotheses `IsUnit C1.det` and `IsUnit A1.det`; finite-dimensional layer
  hypotheses for the chart-data existence theorem. The full product-reduction
  theorem would additionally need the paper-side rank parameter/open-neighborhood
  bridge, endpoint-compatible shared adapted bases, and product-reduction
  induction assembly, not yet proved.
- **Cited.** none for the chart-local algebraic theorem. Analytic invariance
  may only enter through the allowed analytic interface after it is fixed.
- **Deferred.** post-Theorem-3 RLCT reduction and regular-coordinate additivity
  as analytic theorems; instead, prove the elementary entry-ideal algebra and
  later build a full regular-suspension normal-crossing certificate. Full
  Theorem 3 assembly from source hypotheses, target-product normalization, and
  local analytic/certificate transport remain open. The concrete finite edge
  wrappers do not yet compose definitionally with the endpoint theorem, because
  the endpoint theorem uses the total kernel as the source complement while the
  concrete finite edge wrappers use automatically chosen complements at every
  vertex. The through-subspace/chart data layer still needs a shared adapted
  basis family and connection to the chart-local product-reduction induction,
  and any topological open-neighborhood statement remains separate; see
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
- **Tier.** New Lean packaging of established Aoyagi proof.
- **Status.** blocked after independent reproduction check; draft has a
  source-fidelity error in width bookkeeping and unresolved chart,
  regularity/divisibility, termination, and boundary-case gaps.
- **Kill-condition.** The transition system misses a source chart or permits a
  terminal state not covered by Aoyagi's proof.
- **Evidence/source.** Aoyagi blow-up section, PDF pp. 14-23.
- **Pen-and-paper reproduction.** draft at
  `threads/04-blow-up-certificate/reproduction-draft.md`.
- **Reproduction check.** failed/blocked at
  `threads/04-blow-up-certificate/reproduction-check.md`.
- **Lean target.** TBD by thread 04.
- **Proved.** pending.
- **Assumed.** finite dimension/rank hypotheses; no transition invariant is
  accepted yet.
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
