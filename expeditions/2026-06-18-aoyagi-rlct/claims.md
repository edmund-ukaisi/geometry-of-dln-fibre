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
- **Current status addendum, passive theta source-image Jacobian bridge,
  2026-06-30.** Lean now proves a downstream source-image consumer theorem in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge.lean`.
  The public theorem
  `exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_ae_le_const_globalWithDensity_jacobian_passiveProductMeasure_finiteMass`
  takes a locally bounded density on
  `Measure.map sourceChart (baseJ.restrict W)` and proves local-source support,
  a.e. residual square-sum positivity, and `residualNegPowerIntegrableOn` for
  the source-image `withDensity` measure.  The companion finite-integral
  theorem
  `exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_ae_le_const_globalWithDensity_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds`
  gives the existing p.13 regular-coordinate finite-integral conclusion for
  the same source-image measure.  The proof reduces to the existing
  theta-domain Jacobian bounded-density theorems using `ae_of_ae_map`,
  `restrict_withDensity`, and the map-with-density composition identity.
  Reproduction, statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-passive-theta-source-image-jacobian-bridge.md`,
  `threads/03-block-product-reduction/statement-card-a2-passive-theta-source-image-jacobian-bridge.md`,
  and
  `threads/03-block-product-reduction/review-a2-passive-theta-source-image-jacobian-bridge.md`.
  Nonclaims: no original/source prior density identity, no arbitrary
  external-measure domination, no passive-theta-only full p.13 prior transport,
  no Haar transport, no source-rank coverage, normal crossings, pole order, or
  RLCT extraction.
- **Current status addendum, Case 2 passive theta global Jacobian-weighted
  single-open wrapper, 2026-06-30.** Lean now repackages the Jacobian-weighted
  residual-source theorem with a single open neighborhood in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean`.
  The public theorem
  `exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_passiveProductMeasure_globalWithDensity_jacobian_finiteMass`
  uses `sourceMeasure = passiveSource.withDensity jacobianDensity` and proves
  retained-passive local-source support, a.e. residual square-sum positivity,
  and `residualNegPowerIntegrableOn` for
  `Measure.map sourceChart (sourceMeasure.restrict W)` on one open
  neighborhood `W`.  The proof calls the previous two-open theorem, takes
  `W = U ∩ V`, and rewrites restrictions using `restrict_withDensity` and
  `Measure.restrict_restrict`.  Reproduction, statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-theta-jacobian-global-weighted-single-open.md`,
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-theta-jacobian-global-weighted-single-open.md`,
  and
  `threads/03-block-product-reduction/review-a2-case2-passive-theta-jacobian-global-weighted-single-open.md`.
  Focused direct warning check, focused module build, full local build,
  aggregator direct warning check, `scripts/sorries`, `git diff --check`, and
  direct axiom probe passed; the theorem reports only `[propext,
  Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer `Leibniz` and
  xhigh Lean/API reviewer `Locke` returned PASS.  This proves no
  determinant-chart Haar transport, raw-order Haar transport, source-prior
  transport, exact passive-sector pushforward, source-image equality,
  source-rank coverage, global usefulness of the Jacobian density, normal
  crossings, pole order, or RLCT.
- **Current status addendum, Case 2 passive theta Jacobian-weighted
  residual-source adapter, 2026-06-30.** Lean now combines the concrete
  passive-theta raw-order Jacobian sandwich with the concrete passive-theta
  local-domination residual-source socket in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean`.
  The public theorem
  `exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_passiveProductMeasure_withDensity_jacobian_finiteMass`
  first chooses an open Jacobian-unit neighborhood `U`, then defines the source
  measure as the `jacobianDensity` weighting of
  `(passiveMeasure.prod weightedBox).restrict U`, where `jacobianDensity` is
  the retained-passive raw-order Jacobian product read through
  `case2PassiveThetaEndpointTopologyTuple`.  The upper Jacobian sandwich gives
  finite scalar domination by
  `passiveMeasure.prod weightedBox`, and the residual-source socket returns a
  second open neighborhood `V`.  The resulting chart-produced measure
  `Measure.map sourceChart (sourceMeasure.restrict V)` is supported on the
  retained-passive p.13 local source and satisfies a.e. residual square-sum
  positivity plus `residualNegPowerIntegrableOn`.  Reproduction, statement
  card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-theta-jacobian-weighted-residual-source.md`,
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-theta-jacobian-weighted-residual-source.md`,
  and
  `threads/03-block-product-reduction/review-a2-case2-passive-theta-jacobian-weighted-residual-source.md`.
  Focused direct warning check, focused module build, full local build,
  aggregator direct warning check, `scripts/sorries`, `git diff --check`, and
  direct axiom probe passed; the theorem reports only `[propext,
  Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer `Meitner` and
  xhigh Lean/API reviewer `Hubble` returned PASS.  This proves no
  determinant-chart Haar transport, raw-order Haar transport, source-prior
  transport, exact passive-sector pushforward, source-image equality,
  source-rank coverage, normal crossings, pole order, or RLCT.
- **Current status addendum, Case 2 passive theta Jacobian sandwich,
  2026-06-30.** Lean now specializes the generic passive-parameter
  retained-passive raw-order Jacobian sandwich to the concrete full theta
  coordinate domain in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean`.
  The public theorem
  `exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2PassiveThetaEndpointTopologyTuple_passiveProductMeasure`
  works over `sourceMeasure = passiveMeasure.prod weightedBox` and
  `Y z = case2PassiveThetaEndpointTopologyTuple z`.  It returns positive
  constants `epsilon`, `K`, and an open neighborhood `U` of a passive
  determinant-sector base point such that weighting `sourceMeasure.restrict U`
  by `ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z))` is
  sandwiched between `ofReal epsilon` and `ofReal K` scalar multiples of the
  unweighted local measure.  Reproduction, statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-theta-jacobian-sandwich.md`,
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-theta-jacobian-sandwich.md`,
  and
  `threads/03-block-product-reduction/review-a2-case2-passive-theta-jacobian-sandwich.md`.
  Focused direct warning check, focused module build, full local build,
  aggregator direct warning check, `scripts/sorries`, `git diff --check`, and
  direct axiom probe passed; the theorem reports only `[propext,
  Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer `Aristotle`
  returned PASS.  Xhigh Lean/API reviewer `Copernicus` found and the
  controller repaired one minor API restriction by removing unnecessary
  `[Fintype tau] [DecidableEq tau]` assumptions.  This proves no
  determinant-chart Haar transport, raw-order Haar transport, source-prior
  transport, exact passive-sector pushforward, source-image equality,
  source-rank coverage, normal crossings, pole order, or RLCT.
- **Current status addendum, Case 2 passive theta bounded-density residual-source
  adapter, 2026-06-30.** Lean now specializes the generic bounded-density
  passive-product residual-source handoff to the concrete full theta coordinate
  domain in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaProductMeasure.lean`.
  The public theorem
  `exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_withDensity_ae_le_const_passiveProductMeasure_finiteMass`
  uses
  `sourceMeasure = (passiveMeasure.prod weightedBox).withDensity sourceDensity`.
  It returns a local punctured determinant-sector `V`; after `V` is chosen, any
  finite a.e. bound of `sourceDensity` with respect to
  `(passiveMeasure.prod weightedBox).restrict V` implies retained-passive
  local-source support, a.e. residual square-sum positivity, and
  `residualNegPowerIntegrableOn` for the chart-produced measure.  Reproduction,
  statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-theta-bounded-density-residual-source.md`,
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-theta-bounded-density-residual-source.md`,
  and
  `threads/03-block-product-reduction/review-a2-case2-passive-theta-bounded-density-residual-source.md`.
  Focused direct warning check, focused module build, full local build,
  `scripts/sorries`, `git diff --check`, aggregator direct warning check, and
  direct axiom probe passed; the theorem reports only `[propext,
  Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer `Fermat` and
  xhigh Lean/API reviewer `Pauli` returned PASS.  This proves no original
  source-prior density construction, no proof that an original source prior
  satisfies the local bound, no exact restricted `yNext` marginal equality,
  determinant-chart Haar transport, raw-order Haar transport, source-prior
  transport, exact passive-sector pushforward, source-image equality,
  source-rank coverage, normal crossings, pole order, or RLCT.
- **Current status addendum, Case 2 passive theta product-measure residual-source
  adapter, 2026-06-30.** Lean now specializes the generic passive-product and
  local-domination residual-source handoffs to the concrete full theta
  coordinate domain in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaProductMeasure.lean`.
  The concrete product-measure theorem
  `exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_passiveProductMeasure_finiteMass`
  consumes `sourceMeasure = passiveMeasure.prod weightedBox`, finite passive
  mass, positive selected-entry radii, `0 <= t`, and the selected-entry critical
  inequality.  The arbitrary-source theorem
  `exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_restrict_le_smul_passiveProductMeasure_finiteMass`
  returns the same kind of sector but keeps
  `sourceMeasure.restrict V <= c • passiveSource` and `c < ∞` as explicit local
  hypotheses.  Both prove only retained-passive local-source support, a.e.
  residual square-sum positivity, and `residualNegPowerIntegrableOn` for the
  chart-produced measure.  Reproduction, statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-theta-product-measure-residual-source.md`,
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-theta-product-measure-residual-source.md`,
  and
  `threads/03-block-product-reduction/review-a2-case2-passive-theta-product-measure-residual-source.md`.
  Focused direct warning check, focused module build, full local build,
  `scripts/sorries`, `git diff --check`, aggregator direct warning check, and
  direct axiom probes passed; both theorems report only `[propext,
  Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer `Parfit` and
  xhigh Lean/API reviewer `Averroes` returned PASS.  This proves no exact
  restricted `yNext` marginal equality, determinant-chart Haar transport,
  raw-order Haar transport, source-prior transport, exact passive-sector
  pushforward, source-image equality, source-rank coverage, finite-integral
  transfer for the original source prior, normal crossings, pole order, or
  RLCT.
- **Current status addendum, Case 2 passive theta source-measure adapter,
  2026-06-30.** Lean now specializes the generic passive selected-entry
  source-measure theorem to the concrete full theta coordinate domain in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean`.
  It defines
  `case2PassiveThetaEndpointSourceChart`,
  `case2PassiveThetaEndpointResidualCoordEquiv`, and
  `case2PassiveThetaEndpointInverseReadout`, and proves
  `exists_open_measure_map_case2PassiveThetaEndpointSourceChart_puncturedSector_inverseReadout_eq_yNext`.
  The theorem consumes an arbitrary theta-domain `sourceMeasure` and returns an
  open punctured determinant-sector neighborhood `V` such that the chart-produced
  source measure is supported on the retained-passive p.13 local source and its
  selected residual inverse readout pushes forward to the
  `Case2PassiveTheta.yNext` marginal of `sourceMeasure.restrict V`.
  The passive-fields `MeasurableSpace` and `OpensMeasurableSpace` hypotheses
  are explicit.  Reproduction, statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-theta-source-measure-adapter.md`,
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-theta-source-measure-adapter.md`,
  and
  `threads/03-block-product-reduction/review-a2-case2-passive-theta-source-measure-adapter.md`.
  Focused direct warning check, focused module build, full local build,
  `scripts/sorries`, `git diff --check`, aggregator direct warning check, and
  direct axiom probe passed; the theorem reports only `[propext,
  Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer `Banach` and
  xhigh Lean/API reviewer `Popper` returned PASS.  This proves no
  determinant-chart Haar transport, raw-order Haar transport, source-prior
  transport, exact passive-sector pushforward, dominated passive-sector
  comparison, finite-integral transfer, source-image equality, source-rank
  coverage, normal crossings, pole order, or RLCT.
- **Current status addendum, Case 2 passive theta coordinate domain,
  2026-06-30.** Lean now proves the first full passive-sector coordinate-domain
  slice in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSector.lean`.  It defines
  the product coordinate type
  `Case2PassiveTheta = (A1passive, F2, A3passive, Ctop, F3, yNext)`, the
  determinant sector, punctured determinant sector, pre- and post-endpoint
  retained-data maps, pre- and post-endpoint topology-tuple maps, continuity
  lemmas, and determinant/topology-tuple determinant-chart membership lemmas.
  The determinant sector is only the passive unit condition on `Ctop.det` and
  the passive `A1passive.det` fields; selected pivot nonzero is separate.
  Reproduction, statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-theta-coordinate-domain.md`,
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-theta-coordinate-domain.md`,
  and
  `threads/03-block-product-reduction/review-a2-case2-passive-theta-coordinate-domain.md`.
  Focused direct warning check, focused module build, full local build,
  `scripts/sorries`, `git diff --check`, and direct axiom probes passed; full
  build warning noise was pre-existing.  Xhigh source/scope reviewer `Socrates`
  and xhigh Lean/API reviewer `Chandrasekhar` returned PASS.  This proves no
  determinant-chart Haar transport, source-prior transport, exact/dominated
  passive-sector measure theorem, finite-integral transfer, source-image
  equality, source-rank coverage, normal crossings, pole order, or RLCT.
- **Current status addendum, retained-passive passive-sector construction
  frontier, 2026-06-30.** The next source-prior step is a pen-and-paper
  construction target, not a Lean wrapper.  The live Case 2 retained-passive
  local-jacobian lane keeps the full determinant-chart pushforward hypothesis
  `m.restrict Sdet = Measure.map chart weightedBox`.  The reduced selected-entry
  signed-box chart varies only residual center coordinates and should not be
  used to prove that full retained-passive determinant-chart Haar statement.
  The next source-moving theorem must add the suppressed retained p.13 passive
  coordinates and prove an exact or finite-scalar/bounded-density dominated
  passive-sector measure theorem, provisionally
  `measure_map_case2PassiveThetaTopologyTuple_eq_restrict_sectorSet`, in a
  future passive-sector module.  Reproduction and statement card are at
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-passive-sector-construction.md`
  and
  `threads/03-block-product-reduction/statement-card-a2-retained-passive-passive-sector-construction.md`.
  No Lean theorem is claimed.  Xhigh reviewer `Raman` returned findings that
  were repaired: bare mutual absolute continuity was removed as too weak, and
  the passive-coordinate list now includes `A3passive`.  Review is recorded at
  `threads/03-block-product-reduction/review-a2-retained-passive-passive-sector-construction.md`.
  This asserts no original source prior, source-rank coverage,
  determinant-chart Haar transport from the reduced selected-entry section,
  normal crossings, pole order, or RLCT.
- **Current status addendum, Case 2 passive-sector source-stratum-bounds
  finite-integral handoff, 2026-06-29.** Lean now proves the source-stratum-bound
  sibling
  `exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_withPassive_puncturedSector_passiveProductMeasure_finiteMass_sourceStratum_bounds`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean`.
  The theorem keeps the passive/selected-entry coordinate-domain sector `V` and
  chart-produced measure `mu = Measure.map sourceChart (sourceMeasure.restrict V)`
  from the passive-sector handoff, but moves the loss lower bound and density
  hypotheses to `nhdsWithin base sourceStratum`.  The proof uses the
  passive-product residual-source handoff, source-stratum measurability, and only
  the self-base retained-passive local inclusion
  `Ulocal ∩ sourceStratum ⊆ Ulocal ∩ localSource`; it does not assert
  source-rank coverage.  Reproduction, statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-sector-source-stratum-bounds-finite-integral.md`,
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-sector-source-stratum-bounds-finite-integral.md`,
  and
  `threads/03-block-product-reduction/review-a2-case2-passive-sector-source-stratum-bounds-finite-integral.md`.
  Focused local `lake build`, direct `lake env lean -E warning`, full local
  `lake build DLNFibre`, `lean/scripts/sorries`, `git diff --check`, and a direct
  axiom probe passed; the theorem reports only `[propext, Classical.choice,
  Quot.sound]`.  Xhigh source/scope reviewer `Mencius the 4th` and xhigh
  Lean/API reviewer `Dalton the 4th` returned PASS.  This proves no
  determinant-chart Haar transport, source-prior transport, passive/source
  Jacobian transport, source-image equality, source-rank coverage, exact
  localized residual marginal equality, normal crossings, pole order, or RLCT.
- **Current status addendum, selected-entry all-pivot producer shell,
  2026-06-29.** Lean now assembles all proved all-pivot analytic fields over
  the shared universal-domain context into
  `SelectedEntrySuppliedAnalyticAtlasProducer` in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotProducerShell.lean`.  The new
  declaration
  `SelectedEntrySignedBox.CenterCoord.selectedEntryAllPivotSuppliedAnalyticAtlasProducer`
  takes as explicit inputs a branch-state type, a
  `SelectedEntryAtlasProducedBranchData` over
  `selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv`, and a
  `SelectedEntryBranchTerminationData` for the same selected-entry all-pivot
  chart certificate.  It fills source coverage, chart regularity, transition
  regularity, unit regularity, and Jacobian/volume compatibility from the
  already proved all-pivot data.  Reproduction, statement card, and review are
  at
  `threads/03-block-product-reduction/reproduction-a2-selected-entry-all-pivot-producer-shell.md`,
  `threads/03-block-product-reduction/statement-card-a2-selected-entry-all-pivot-producer-shell.md`,
  and
  `threads/03-block-product-reduction/review-a2-selected-entry-all-pivot-producer-shell.md`.
  Focused local `lake build`, direct `lake env lean -E warning`, full local
  `lake build DLNFibre`, `lean/scripts/sorries`, `git diff --check`, and direct
  axiom probe passed; the declaration reports only `[propext,
  Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer `Darwin the
  4th` and xhigh Lean/API reviewer `James the 4th` returned PASS.  This proves
  no source production, branch termination, branch guard exhaustiveness,
  branch-state transition semantics, normal-crossing extraction, pole order, or
  RLCT.
- **Current status addendum, Case 2 passive-sector finite-integral handoff,
  2026-06-29.** Lean now proves the passive selected-entry punctured-sector
  finite-integral wrapper
  `exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_withPassive_puncturedSector_passiveProductMeasure_finiteMass`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean`.
  The theorem returns an open passive/selected-entry coordinate-domain sector
  `V` around `z0`; for `mu = Measure.map sourceChart
  (sourceMeasure.restrict V)` it returns an open edge-family neighborhood `U`
  around the fixed-base source family and proves the p.13 regular-coordinate
  finite integral over `(mu.restrict (U ∩ sourceStratum)).prod nu`.  It
  composes the existing punctured-sector residual-source theorem with the
  retained-passive local finite-integral consumer.  Reproduction, statement
  card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-sector-finite-integral-handoff.md`,
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-sector-finite-integral-handoff.md`,
  and
  `threads/03-block-product-reduction/review-a2-case2-passive-sector-finite-integral-handoff.md`.
  Focused local `lake build`, direct `lake env lean -E warning`,
  `scripts/sorries`, `git diff --check`, and direct axiom probe passed; the
  theorem reports only `[propext, Classical.choice, Quot.sound]`.  Xhigh
  source/scope reviewer `Fermat the 4th` returned PASS after documentation
  wording was repaired from "source-rank coverage" to the actual local-source
  inclusion, and xhigh Lean/API reviewer `Curie the 4th` returned PASS.  This
  proves no determinant-chart Haar transport, source-prior transport,
  passive/source Jacobian transport, source-image equality, source-rank
  coverage, exact localized residual marginal equality, normal crossings, pole
  order, or RLCT.
- **Current status addendum, selected-entry all-pivot transition regular data,
  2026-06-29.** Lean now packages the finite selected-entry normalized overlap
  formula as transition regularity over the all-pivot selected-entry shared
  universal-domain context in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotTransitionRegularData.lean`.
  It defines/proves `allPivotTransitionDenom`, `allPivotTransitionDomain`,
  `allPivotTransitionPoint`, `continuous_allPivotTransitionDenom`,
  `continuous_allPivotTransitionNumerator`,
  `continuousOn_allPivotTransitionPoint`,
  `selectedEntryAllPivotAnalyticTransitionRegularData`, and
  `selectedEntryAllPivotAnalyticTransitionRegular`.  The transition domain
  from source chart `source` to target chart `target` is exactly the
  normalized target-coordinate nonzero locus `{x | denom x != 0}`; on that
  domain the division formula is continuous and preserves the represented
  center point by the finite theorem
  `chartMap_sourceChartTransitionPoint_eq_of_target_normalized_ne_zero`.
  Reproduction, statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-selected-entry-all-pivot-transition-regular-data.md`,
  `threads/03-block-product-reduction/statement-card-a2-selected-entry-all-pivot-transition-regular-data.md`,
  and
  `threads/03-block-product-reduction/review-a2-selected-entry-all-pivot-transition-regular-data.md`.
  Focused local `lake build`, direct `lake env lean -E warning`, full local
  `lake build DLNFibre`, `lean/scripts/sorries`, `git diff --check`, and direct
  axiom probes passed; the two new public declarations report only `[propext,
  Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer `Erdos the 4th`
  returned PASS after documentation attribution was repaired, and xhigh
  Lean/API reviewer `Confucius the 4th` returned PASS.  This proves no source
  production, branch termination, original/source-prior transport,
  determinant-chart Haar transport, full supplied analytic atlas producer,
  normal-crossing extraction, pole order, or RLCT.
- **Current status addendum, selected-entry all-pivot Jacobian/volume data,
  2026-06-29.** Lean now lifts the one-pivot selected-entry chart-point
  product-measure pushforward to the all-pivot selected-entry shared
  universal-domain context in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotJacobianVolumeData.lean`.
  It defines/proves `selectedEntryAllPivotAnalyticJacobianVolumeData` and
  `selectedEntryAllPivotAnalyticJacobianVolumeCompatible`.  For each chart
  index `c`, the proof applies the one-pivot Jacobian/volume data at
  `chartEquiv c`; the chart measure is
  `chartPointProductMeasure (chartEquiv c) R`, the density is
  `ofReal (chartPointDensity (chartEquiv c) x)`, and the target is
  `chartMap (chartEquiv c) '' signedBoxSet R`.  Reproduction, statement card,
  and review are at
  `threads/03-block-product-reduction/reproduction-a2-selected-entry-all-pivot-jacobian-volume-data.md`,
  `threads/03-block-product-reduction/statement-card-a2-selected-entry-all-pivot-jacobian-volume-data.md`,
  and
  `threads/03-block-product-reduction/review-a2-selected-entry-all-pivot-jacobian-volume-data.md`.
  Focused local `lake build`, direct `lake env lean -E warning`, full local
  `lake build DLNFibre`, `lean/scripts/sorries`, `git diff --check`, and direct
  axiom probes passed; the two new declarations report only `[propext,
  Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer `Arendt the
  4th` and xhigh Lean/API reviewer `Mendel the 4th` returned PASS.  This proves
  no transition regularity between distinct selected-entry pivots, no source
  production, no branch termination, no original/source-prior transport, no
  determinant-chart Haar transport, no full supplied analytic atlas producer,
  no normal-crossing extraction, no pole order, and no RLCT.
- **Current status addendum, selected-entry all-pivot regular data,
  2026-06-29.** Lean now lifts the one-pivot selected-entry chart and unit
  regularity facts to the all-pivot selected-entry shared universal-domain
  context in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotRegularData.lean`.  It
  defines/proves `selectedEntryAllPivotAnalyticChartRegularData`,
  `selectedEntryAllPivotAnalyticUnitRegularData`,
  `selectedEntryAllPivotAnalyticChartRegular`, and
  `selectedEntryAllPivotAnalyticUnitRegular`.  For each chart index `c`, the
  proof applies the one-pivot continuity/unit facts at `chartEquiv c`; the
  chart map is `x_p = u`, `x_i = u r_i`, the coordinate is `u`, the loss unit
  is `1 + sum r_i^2`, and the formal Jacobian/prior unit is `1`.
  Reproduction, statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-selected-entry-all-pivot-regular-data.md`,
  `threads/03-block-product-reduction/statement-card-a2-selected-entry-all-pivot-regular-data.md`,
  and
  `threads/03-block-product-reduction/review-a2-selected-entry-all-pivot-regular-data.md`.
  Focused and full local `lake build` gates passed, and a direct Lean check of
  the new file passed.  The direct axiom probe for the four new declarations
  reported only `[propext, Classical.choice, Quot.sound]`.  Xhigh source/scope
  reviewer `Maxwell the 4th` and xhigh Lean/API reviewer `Sartre the 4th`
  returned PASS.  This proves no transition regularity between distinct
  selected-entry pivots, no Jacobian/volume compatibility, no full supplied
  analytic atlas producer, no source production, no branch termination, no
  original/source-prior transport, no determinant-chart Haar transport, no
  source-rank coverage, no normal-crossing extraction, no pole order, and no
  RLCT.
- **Current status addendum, Case 2 source chart-point coverage,
  2026-06-29.** Lean now specializes the generic all-pivot selected-entry
  source chart-point coverage theorem to the Case 2 residual-block certificate
  in `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`.  It proves
  `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.exists_sourceChartPoint_chartMap_eq_value`
  and
  `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.exists_sourceChartPoint_chartMap_eq_value_and_coord_zero_eq_sourceSelected`.
  For every finite residual-block center value, the first theorem chooses a
  chart index, source selected variable `u`, and residual function whose
  `sourceChartPoint` maps to that value; the second also records that the
  unique certificate coordinate of the chosen witness is `u`.  Reproduction,
  statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-case2-source-chart-point-coverage.md`,
  `threads/03-block-product-reduction/statement-card-a2-case2-source-chart-point-coverage.md`,
  and
  `threads/03-block-product-reduction/review-a2-case2-source-chart-point-coverage.md`.
  Aoyagi PDF pp. 19-22 are used only for the displayed selected-entry
  substitution `x_p = u`, `x_i = u r_i`; the all-pivot residual-block version
  is expedition-built finite coordinate bookkeeping.  The full `DLNFibre`
  build passed via local `lake build` fallback after environment policy
  rejected escalated `scripts/lb` access to `$HOME/.lake-shared`; after a
  docstring wording repair, the focused `SelectedEntryNormalCrossing` build
  passed.  `scripts/sorries`, `git diff --check`, touched Lean-file
  forbidden-marker scan, and direct axiom probes passed with `[propext,
  Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer `Euclid the
  4th` and xhigh Lean/API reviewer `Feynman the 4th` returned PASS.  This
  proves no analytic atlas coverage, transition regularity, source production
  of successor matrices or suffixes, source-prior transport, determinant-chart
  Haar transport, source-rank coverage, normal-crossing extraction, pole order,
  or RLCT.
- **Current status addendum, selected-entry all-pivot source coverage data,
  2026-06-29.** Lean now packages the all-pivot selected-entry finite chart
  family coverage theorem as `SelectedEntryAnalyticSourceCoverageData` for a
  shared universal-domain context in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotSourceCoverageData.lean`.
  It defines/proves `selectedEntryAllPivotAnalyticAtlasContext`,
  `selectedEntryAllPivotAnalyticSourceCoverageData`, and
  `selectedEntryAllPivotAnalyticSourceCoverage`, reusing the existing finite
  coverage theorem
  `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exists_chartPoint_chartMap_eq_value`.
  The reproduction and statement card are at
  `threads/03-block-product-reduction/reproduction-a2-selected-entry-all-pivot-source-coverage-data.md`
  and
  `threads/03-block-product-reduction/statement-card-a2-selected-entry-all-pivot-source-coverage-data.md`.
  Focused build and full `DLNFibre` build passed; `scripts/sorries`,
  `git diff --check`, touched Lean-file forbidden-marker scan, and direct
  axiom probes passed with `[propext, Classical.choice, Quot.sound]`.
  Review is recorded at
  `threads/03-block-product-reduction/review-a2-selected-entry-all-pivot-source-coverage-data.md`;
  xhigh source/scope reviewer `Wegener the 4th` returned PASS after
  documentation repairs and xhigh Lean/API reviewer `Nash the 4th` returned
  PASS.  Aoyagi prints the
  displayed top-left selected-entry chart, not this all-pivot analytic atlas as
  a source theorem; this is expedition-built finite coordinate coverage for the
  all-pivot certificate only.  It proves no chart regularity, transition
  regularity, unit regularity, Jacobian/volume compatibility, full supplied
  analytic atlas producer, source production, branch termination,
  original/source-prior transport, determinant-chart Haar transport,
  normal-crossing extraction, pole order, or RLCT.
- **Current status addendum, selected-entry one-chart source-coverage
  obstruction, 2026-06-29.** Lean now proves that the exact one-chart
  selected-entry context with `sourceDomain = Set.univ` cannot provide
  `SelectedEntryAnalyticSourceCoverageData` when the center has a non-pivot
  coordinate, in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryOneChartSourceCoverageObstruction.lean`.
  The helper theorems are `formalChartMap_pivot` and
  `formalChartMap_eq_zero_of_fst_eq_zero`; the obstruction theorem is
  `not_selectedEntryOneChartAnalyticSourceCoverageData_of_ne`.  Reproduction
  and statement card are at
  `threads/03-block-product-reduction/reproduction-a2-selected-entry-one-chart-source-coverage-obstruction.md`
  and
  `threads/03-block-product-reduction/statement-card-a2-selected-entry-one-chart-source-coverage-obstruction.md`.
  Review is at
  `threads/03-block-product-reduction/review-a2-selected-entry-one-chart-source-coverage-obstruction.md`.
  Focused build and full `DLNFibre` build passed.  `scripts/sorries`,
  `git diff --check`, touched Lean-file forbidden-marker scan, and direct
  axiom probe passed with `[propext, Classical.choice, Quot.sound]`.  Xhigh
  source/scope reviewer `Epicurus the 4th` and xhigh Lean/API reviewer
  `Nietzsche the 4th` returned PASS.  This is not an obstruction to source
  coverage for a smaller source domain, a multi-pivot atlas, or a supplied
  analytic atlas producer, and it proves no source production, branch
  termination, original/source-prior transport, determinant-chart Haar
  transport, source-rank coverage, normal-crossing extraction, pole order, or
  RLCT.
- **Current status addendum, selected-entry one-chart analytic predicate data,
  2026-06-29.** Lean now wraps the selected-entry one-chart records into the
  forgetful analytic predicate interface in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryOneChartAnalyticPredicateData.lean`.
  It proves `selectedEntryOneChartAnalyticChartRegular`,
  `selectedEntryOneChartAnalyticTransitionRegular`,
  `selectedEntryOneChartAnalyticUnitRegular`, and
  `selectedEntryOneChartAnalyticJacobianVolumeCompatible`.  The witnesses use
  `selectedEntryOneChartAnalyticAtlasContext pivot` and the already proved
  one-chart data records; the Jacobian/volume-compatible theorem inherits
  positive radii from `selectedEntryOneChartAnalyticJacobianVolumeData`.
  Reproduction and statement card are at
  `threads/03-block-product-reduction/reproduction-a2-selected-entry-one-chart-analytic-predicate-data.md`
  and
  `threads/03-block-product-reduction/statement-card-a2-selected-entry-one-chart-analytic-predicate-data.md`.
  Review is at
  `threads/03-block-product-reduction/review-a2-selected-entry-one-chart-analytic-predicate-data.md`.
  Focused build and full `DLNFibre` build passed.  `scripts/sorries`,
  `git diff --check`, touched Lean-file forbidden-marker scan, and direct
  axiom probe passed with `[propext, Classical.choice, Quot.sound]`.  Xhigh
  source/scope reviewer `Lorentz the 4th` and xhigh Lean/API reviewer `Harvey
  the 4th` returned PASS.  This proves no source-domain coverage, no full
  supplied analytic atlas producer, no source production, no branch
  termination, no original/source-prior transport, no determinant-chart Haar
  transport, no source-rank coverage, no
  normal-crossing extraction, no pole order, and no RLCT.
- **Current status addendum, selected-entry one-chart regular data,
  2026-06-29.** Lean now packages chart regularity, identity transition
  regularity, and unit regularity for the selected-entry one-chart context in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryOneChartRegularData.lean`.  It proves
  `continuous_chartPointCoord`, `continuous_chartPointLossUnit`, and
  `continuous_chartPointJacobianPriorUnit`, then defines
  `selectedEntryOneChartAnalyticChartRegularData`,
  `selectedEntryOneChartAnalyticTransitionRegularData`, and
  `selectedEntryOneChartAnalyticUnitRegularData`.  The chart map is the
  continuous map `(u, r) |-> (x_p = u, x_i = u r_i)`, the unique certificate
  coordinate is `u`, the single one-chart transition is identity on `Set.univ`,
  the loss unit is `1 + sum r_i^2`, and the Jacobian/prior unit is constant
  `1`.  Reproduction and statement card are at
  `threads/03-block-product-reduction/reproduction-a2-selected-entry-one-chart-regular-data.md`
  and
  `threads/03-block-product-reduction/statement-card-a2-selected-entry-one-chart-regular-data.md`.
  Review is at
  `threads/03-block-product-reduction/review-a2-selected-entry-one-chart-regular-data.md`.
  Focused build and full `DLNFibre` build passed.  `scripts/sorries`,
  `git diff --check`, touched Lean-file forbidden-marker scan, and direct
  axiom probe passed with `[propext, Classical.choice, Quot.sound]`.  Xhigh
  route scout `Dirac the 4th` confirmed the target is faithful under the
  narrow one-chart label; xhigh implementation reviewer `Mill the 4th`
  returned PASS after documentation repairs.  This proves no source-domain
  coverage, no multi-pivot analytic
  transition regularity, no full analytic atlas producer, no source
  production, no branch termination, no original/source-prior transport, no
  determinant-chart Haar transport, no source-rank coverage, no
  normal-crossing extraction, no pole order, and no RLCT.
- **Current status addendum, selected-entry one-chart Jacobian/volume data,
  2026-06-29.** Lean now proves the finite chart-point volume-form pushforward
  `map_formalChartMap_chartPointProductMeasure_withDensity_eq_restrict_image`
  in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryChartPointMeasureBridge.lean` and
  packages it as one `SelectedEntryAnalyticJacobianVolumeData` record in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryOneChartJacobianVolumeData.lean`.
  The context uses the single selected-entry normal-crossing certificate chart,
  `sourceDomain = Set.univ`, and `chartDomain = Set.univ`; the data uses
  source measure `volume`, chart measure `chartPointProductMeasure pivot R`,
  density `ofReal (chartPointDensity pivot x)`, and target
  `chartMap pivot '' signedBoxSet R`.  Positive radii `forall i, 0 < R i`
  are required for target nonemptiness and nonzero restricted source measure,
  but not for the pushforward equality itself.  Reproduction, statement card,
  and review are at
  `threads/03-block-product-reduction/reproduction-a2-selected-entry-one-chart-jacobian-volume-data.md`,
  `threads/03-block-product-reduction/statement-card-a2-selected-entry-one-chart-jacobian-volume-data.md`,
  and
  `threads/03-block-product-reduction/review-a2-selected-entry-one-chart-jacobian-volume-data.md`.
  Focused builds and full `DLNFibre` build passed; `scripts/sorries`,
  `git diff --check`, touched Lean-file marker scan, and direct axiom probes
  passed with `[propext, Classical.choice, Quot.sound]`.  Xhigh implementation
  review by `Tesla the 4th` returned PASS.  This proves no full analytic atlas producer,
  source coverage, chart/transition/unit regularity as full analytic data,
  source production, branch termination, source-prior transport,
  determinant-chart Haar transport, source-rank coverage, normal-crossing
  extraction, pole order, or RLCT.
- **Current status addendum, selected-entry chart-point weighted product
  measure, 2026-06-29.** Lean now proves the finite weighted product-measure
  transport for the selected-entry `chartPointAdapter` in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryChartPointMeasureBridge.lean`.
  It defines
  `chartPointDensity pivot x = |x.1| ^ ((center.erase pivot.1).card : R)`,
  proves `chartPointDensity_chartPointAdapter_eq_sourceDensity` and
  `aemeasurable_chartPointDensity`, and combines these with the banked
  unweighted product-measure split to prove
  `map_chartPointAdapter_withDensity_sourceDensity_eq_chartPointProductMeasure_withDensity`.
  No positivity hypothesis on radii and no pivot-nonzero hypothesis are needed
  for this equality.  Reproduction and statement card are at
  `threads/03-block-product-reduction/reproduction-a2-selected-entry-chart-point-weighted-product-measure.md`
  and
  `threads/03-block-product-reduction/statement-card-a2-selected-entry-chart-point-weighted-product-measure.md`.
  Focused build of
  `DLNFibre.DLN.Aoyagi.SelectedEntryChartPointMeasureBridge` and full
  `DLNFibre` build passed via `scripts/lb`; only pre-existing replay warnings
  appeared.  Xhigh source-scope, Lean/API, and implementation reviews returned
  PASS; `scripts/sorries`, `git diff --check`, touched Lean-file marker scan,
  and direct axiom probes passed with
  `[propext, Classical.choice, Quot.sound]`.  This proves no
  analytic atlas construction, no `SelectedEntryAnalyticJacobianVolumeData`,
  no original/source-prior transport, no determinant-chart Haar transport, no
  source coverage, no source-rank coverage, no transition regularity, no
  normal-crossing extraction, no pole order, and no RLCT.
- **Current status addendum, selected-entry chart-target nonzero measure,
  2026-06-29.** Lean now proves a finite fixed-pivot nonzero target/source
  measure brick for selected-entry signed-box charts in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean` and
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryChartPointMeasureBridge.lean`.
  Under positive radii `forall i, 0 < R i`, the proof defines the concrete
  inner target box `chartMapTargetInnerBox pivot R` with pivot interval
  `(R pivot / 2, R pivot)` and non-pivot intervals
  `(-(R pivot * R i / 4), R pivot * R i / 4)`.  It proves this box is open,
  nonempty, and contained in `chartMap pivot '' signedBoxSet R`, using the
  existing horn membership criterion for the substitution `x_p = u`,
  `x_i = u r_i`.  Hence it proves
  `volume_chartMap_image_signedBoxSet_ne_zero` and
  `volume_restrict_chartMap_image_signedBoxSet_ne_zero`, plus the punctured
  target variants
  `volume_chartMap_image_signedBoxSet_inter_pivot_ne_zero_ne_zero` and
  `volume_restrict_chartMap_image_signedBoxSet_inter_pivot_ne_zero_ne_zero`.
  The existing Jacobian pushforward theorem then gives
  `signedBoxMeasure_withDensity_sourceDensity_ne_zero` and
  `restrict_nonzeroSignedBox_withDensity_sourceDensity_ne_zero`.  The
  chart-point bridge adds `map_chartPointAdapter_weightedSignedBox_ne_zero`
  and
  `map_formalChartMap_map_chartPointAdapter_weightedSignedBox_ne_zero`.
  Reproduction, statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-selected-entry-chart-target-nonzero.md`,
  `threads/03-block-product-reduction/statement-card-a2-selected-entry-chart-target-nonzero.md`,
  and
  `threads/03-block-product-reduction/review-a2-selected-entry-chart-target-nonzero.md`.
  Focused builds of both touched modules passed via `scripts/lb`; xhigh
  source-scope, Lean/API, and implementation reviews returned PASS; full
  `DLNFibre` build, `scripts/sorries`, `git diff --check`, touched Lean-file
  marker scan, and direct axiom probes passed with
  `[propext, Classical.choice, Quot.sound]`.  This proves no analytic atlas construction,
  `SelectedEntryAnalyticJacobianVolumeData`, natural chart-point product
  measure theorem, original/source-prior transport, determinant-chart Haar
  transport, raw/source Haar theorem, source coverage, source-rank coverage,
  transition regularity, source production, branch termination,
  normal-crossing extraction, pole order, or RLCT.
- **Current status addendum, selected-entry chart-point product measure,
  2026-06-29.** Lean now proves the natural finite product-measure split for
  the selected-entry `chartPointAdapter` in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryChartPointMeasureBridge.lean`.
  It defines `erasePivotEquivCompl`, `chartPointProductMeasure`, and
  `chartPointSplitEquiv`; proves the split equivalence has coordinates
  `(y pivot, y|center.erase pivot.1)` and is equal to `chartPointAdapter`;
  and proves
  `measurePreserving_chartPointSplitEquiv_signedBoxMeasure` plus
  `map_chartPointAdapter_signedBoxMeasure_eq_chartPointProductMeasure`.
  This theorem has no positivity hypothesis on the radii.  It is finite
  product-measure bookkeeping for the adapter only.  It proves no analytic
  atlas construction, no `SelectedEntryAnalyticJacobianVolumeData`, no
  original/source-prior transport, no determinant-chart Haar transport, no
  source coverage, no source-rank coverage, no transition regularity, no
  normal-crossing extraction, no pole order, and no RLCT.
- **Current status addendum, selected-entry chart-point measure bridge,
  2026-06-29.** Lean now proves the selected-entry finite chart-point bridge in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryChartPointMeasureBridge.lean`.  The
  module defines `FormalChartPoint pivot = ℝ × (center.erase pivot → ℝ)`,
  `chartPointAdapter pivot y = (y pivot, y|center.erase pivot)`, and
  `formalChartMap pivot`, the one-chart normal-crossing certificate chart map
  with product chart-point type exposed.  It proves continuity/measurability
  of the adapter and chart map, the pointwise equality
  `formalChartMap pivot (chartPointAdapter pivot y) =
  SelectedEntrySignedBox.CenterCoord.chartMap pivot y`, and adapter
  compatibility for the certificate coordinate, loss unit, and absolute
  Jacobian/prior density:
  `coord_chartPointAdapter_eq`,
  `lossUnit_chartPointAdapter_eq_residualUnit`, and
  `abs_jacobianPrior_chartPointAdapter_eq_sourceDensity`.  The measure
  theorems
  `map_formalChartMap_comp_chartPointAdapter_weightedSignedBox_eq_restrict_image`
  and
  `map_formalChartMap_map_chartPointAdapter_weightedSignedBox_eq_restrict_image`
  restate the existing signed-box weighted pushforward through the adapter;
  the two-stage version uses global measurability and `Measure.map_map`.
  Reproduction, statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-selected-entry-chart-point-measure-bridge.md`,
  `threads/03-block-product-reduction/statement-card-a2-selected-entry-chart-point-measure-bridge.md`,
  and
  `threads/03-block-product-reduction/review-a2-selected-entry-chart-point-measure-bridge.md`.
  Focused build and full `DLNFibre` build passed via `scripts/lb`;
  `scripts/sorries`, `git diff --check`, touched Lean-file forbidden-marker
  scan, and direct axiom probes passed with
  `[propext, Classical.choice, Quot.sound]`.  Xhigh source-scope, Lean/API,
  and implementation reviews returned PASS.  This proves no analytic atlas
  construction,
  `SelectedEntryAnalyticJacobianVolumeData`, natural product-measure theorem
  on chart-point space, original source-prior transport, determinant-chart
  Haar theorem, raw/source Haar theorem, retained-passive passive Jacobian,
  source-image or source-rank coverage, transition regularity, source
  production, branch termination, normal-crossing extraction, pole order, or
  RLCT.
- **Current status addendum, retained-passive raw-order two-stage pushforward,
  2026-06-29.** Lean now proves
  `exists_open_measure_map_case2EndpointTransport_withPassive_puncturedSector_rawOrderMap_twoStage_eq_sourceChart_inverseReadout_eq_snd`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasure.lean`.
  This is repo-local measure functoriality and local a.e. measurability around
  the already banked topology-tuple sector bridge.  It returns an open
  punctured sector `V`, proves the same pointwise raw-order chart membership,
  source-chart equality, local-source membership, source-readback recovery, and
  selected-entry inverse readout as the one-stage theorem, and under Borel
  measurable structures on the raw-order topology-tuple target and edge-family
  target proves both
  `Measure.map (fun z => rawChart (rawMap z)) (sourceMeasure.restrict V) =
  Measure.map sourceChart (sourceMeasure.restrict V)` and
  `Measure.map rawChart (Measure.map rawMap (sourceMeasure.restrict V)) =
  Measure.map sourceChart (sourceMeasure.restrict V)`.  Reproduction,
  statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-raw-order-two-stage-pushforward.md`,
  `threads/03-block-product-reduction/statement-card-a2-retained-passive-raw-order-two-stage-pushforward.md`,
  and
  `threads/03-block-product-reduction/review-a2-retained-passive-raw-order-two-stage-pushforward.md`.
  Focused build and full `DLNFibre` build passed via `scripts/lb`;
  `scripts/sorries`, `git diff --check`, touched Lean-file forbidden-marker scan,
  and direct axiom probe passed with `[propext, Classical.choice, Quot.sound]`.
  Xhigh source-scope and Lean/API reviews returned PASS.  This is API hardening
  for future intermediate-measure consumers, not a new Aoyagi source calculation
  or a source-prior frontier removal.  It proves no determinant-chart Haar
  transport, raw/source Haar theorem, external/original source-prior comparison,
  passive Jacobian formula, density identity, local domination for arbitrary
  `sourceMeasure`, source-image equality, source-rank coverage, normal
  crossings, pole order, or RLCT.
- **Current status addendum, retained-passive raw-order composite measure
  factorization, 2026-06-29.** Lean now proves
  `exists_open_measure_map_case2EndpointTransport_withPassive_puncturedSector_rawOrderMap_comp_eq_sourceChart_inverseReadout_eq_snd`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasure.lean`.
  This is repo-local measure functoriality around the already banked topology-
  tuple sector bridge.  It returns an open punctured sector `V`, proves
  pointwise raw-order chart membership, equality of
  `rawChart (rawMap z)` with `sourceChart z`, local-source membership,
  source-readback recovery of `retainedData z`, and
  `inverseReadout (sourceChart z) = z.2` on `V`, and proves the one-stage
  pushforward equality
  `Measure.map (fun z => rawChart (rawMap z)) (sourceMeasure.restrict V) =
  Measure.map sourceChart (sourceMeasure.restrict V)`.  Reproduction,
  statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-raw-order-map-factorization.md`,
  `threads/03-block-product-reduction/statement-card-a2-retained-passive-raw-order-map-factorization.md`,
  and
  `threads/03-block-product-reduction/review-a2-retained-passive-raw-order-map-factorization.md`.
  Focused build and full `DLNFibre` build passed via `scripts/lb`;
  `scripts/sorries`, `git diff --check`, touched-file forbidden-marker scan,
  and direct axiom probe passed with `[propext, Classical.choice, Quot.sound]`.
  Xhigh source-scope and Lean/API reviews returned PASS; xhigh implementation
  review returned PASS after documentation scope repair.  This is not a
  two-stage raw-order pushforward theorem and does not include the earlier
  local-source support or inverse-readout pushforward fields.  It proves no
  determinant-chart Haar transport, raw/source Haar theorem, external/original
  source-prior comparison, passive Jacobian formula, density identity,
  source-image equality, source-rank coverage, normal crossings, pole order,
  or RLCT.
- **Current status addendum, retained-passive topology-tuple punctured-sector
  transport, 2026-06-29.** Lean now proves
  `exists_open_case2EndpointTransport_withPassive_topologyTuple_rawOrderSourceChart_eq_sourceChart_puncturedSector_inverseReadout_eq`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySource.lean`.
  This is repo-local topology/raw-order source-chart packaging around already
  reproduced Aoyagi p.13 and Case 2 selected-entry formulas.  It returns an
  open determinant-and-pivot-nonzero sector `V` and proves topology tuple
  determinant membership, raw-order source-recursive determinant membership,
  equality of the raw-order p.13 source chart with the direct chart-produced
  source family, source-readback recovery of `retainedData z`, and
  `inverseReadout (sourceChart z) = z.2` on `V`.  Reproduction, statement
  card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-topology-tuple-punctured-sector-transport.md`,
  `threads/03-block-product-reduction/statement-card-a2-retained-passive-topology-tuple-punctured-sector-transport.md`,
  and
  `threads/03-block-product-reduction/review-a2-retained-passive-topology-tuple-punctured-sector-transport.md`.
  Focused build passed via `scripts/lb`; `scripts/sorries`,
  `git diff --check`, touched Lean-file forbidden-marker scan, and direct
  axiom probe passed with `[propext, Classical.choice, Quot.sound]`.  Xhigh
  source-scope, Lean/API, and implementation reviews returned PASS.  This
  proves no source-image equality, source-rank coverage, determinant-chart
  Haar transport, raw/source Haar theorem, external/original source-prior
  comparison, measure pushforward theorem, Jacobian formula, normal crossings,
  pole order, or RLCT.
- **Current status addendum, retained-passive chart-produced punctured-sector
  bounded-density residual source, 2026-06-29.** Lean now proves the helper
  `restrict_withDensity_le_smul_of_ae_le` in
  `lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean`, and proves
  `exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_of_withDensity_ae_le_const_passiveProductMeasure_finiteMass`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean`.
  The theorem sets `sourceMeasure = passiveSource.withDensity sourceDensity`.
  After the local-domination socket chooses an open determinant-and-pivot-
  nonzero sector `V`, support of
  `mu = Measure.map sourceChart ((passiveSource.withDensity sourceDensity).restrict V)`
  on the retained-passive p.13 local source is unconditional, and residual
  positivity plus `residualNegPowerIntegrableOn` follow under a finite scalar
  `c` and the explicit local a.e. bound `sourceDensity <= c` with respect to
  `passiveSource.restrict V`.  Reproduction, statement card, and review are
  at
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-chart-produced-punctured-sector-bounded-density-residual-source.md`,
  `threads/03-block-product-reduction/statement-card-a2-retained-passive-chart-produced-punctured-sector-bounded-density-residual-source.md`,
  and
  `threads/03-block-product-reduction/review-a2-retained-passive-chart-produced-punctured-sector-bounded-density-residual-source.md`.
  Focused build and full `DLNFibre` build passed via `scripts/lb`;
  `scripts/sorries`, `git diff --check`, touched Lean-file forbidden-marker
  scan, and direct axiom probes passed with
  `[propext, Classical.choice, Quot.sound]`.  Xhigh route review by
  `McClintock the 4th` and xhigh post-implementation review by
  `Kierkegaard the 4th` returned PASS.  This is only a bounded-density adapter
  over the chart-produced passive product measure: no external/original
  source-prior density or bound, determinant-chart Haar transport, raw/source
  Haar theorem, passive Jacobian formula, source-image equality, source-rank
  coverage, normal crossings, pole order, or RLCT is claimed.
- **Current status addendum, retained-passive chart-produced punctured-sector
  local-domination residual source, 2026-06-29.** Lean now proves
  `exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_of_restrict_le_smul_passiveProductMeasure_finiteMass`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean`.
  The theorem keeps `sourceMeasure` arbitrary.  After the residual-source
  socket chooses an open determinant-and-pivot-nonzero sector `V`, support of
  `mu = Measure.map sourceChart (sourceMeasure.restrict V)` on the
  retained-passive p.13 local source is unconditional, and residual positivity
  plus `residualNegPowerIntegrableOn` follow under the explicit local
  domination field
  `sourceMeasure.restrict V <= c • (passiveMeasure.prod weightedBox)` with
  finite `c`.  Reproduction, statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-chart-produced-punctured-sector-local-domination-residual-source.md`,
  `threads/03-block-product-reduction/statement-card-a2-retained-passive-chart-produced-punctured-sector-local-domination-residual-source.md`,
  and
  `threads/03-block-product-reduction/review-a2-retained-passive-chart-produced-punctured-sector-local-domination-residual-source.md`.
  Focused build and full `DLNFibre` build passed via `scripts/lb`;
  `scripts/sorries`, `git diff --check`, touched Lean-file forbidden-marker
  scan, and direct axiom probe passed with
  `[propext, Classical.choice, Quot.sound]`.  Xhigh post-implementation
  review by `Einstein the 3rd` returned PASS.  This is only a conditional
  local-domination wrapper: no external/original source-prior domination,
  determinant-chart Haar transport, raw/source Haar theorem, passive Jacobian
  formula, source-image equality, source-rank coverage, normal crossings,
  pole order, or RLCT is claimed.
- **Current status addendum, retained-passive chart-produced punctured-sector
  passive-product residual source, 2026-06-29.** Lean now proves
  `exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_passiveProductMeasure_finiteMass`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean`.
  The theorem specializes the residual-source socket to the concrete coordinate
  domain measure `passiveMeasure.prod weightedBox`, where `weightedBox` is the
  raw selected-entry signed box with Aoyagi's source density.  After the socket
  chooses an open determinant-and-pivot-nonzero sector `V`, the proof uses
  domination
  `Measure.map Prod.snd ((passiveMeasure.prod weightedBox).restrict V) <=
  passiveMeasure Set.univ • weightedBox`, not equality, to transfer the raw
  selected-entry residual positivity and finite negative-power integrability to
  the sector marginal.  Finite passive mass is explicit.  Reproduction,
  statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-chart-produced-punctured-sector-passive-product-residual-source.md`,
  `threads/03-block-product-reduction/statement-card-a2-retained-passive-chart-produced-punctured-sector-passive-product-residual-source.md`,
  and
  `threads/03-block-product-reduction/review-a2-retained-passive-chart-produced-punctured-sector-passive-product-residual-source.md`.
  Focused build and full `DLNFibre` build passed via `scripts/lb`;
  `scripts/sorries`, `git diff --check`, touched Lean-file forbidden-marker
  scan, and direct axiom probe passed with
  `[propext, Classical.choice, Quot.sound]`.  Xhigh route review by
  `Cicero the 3rd` and implementation review by `Epicurus the 3rd` returned
  PASS.  This is only a chart-produced restricted passive-product
  residual-source theorem: no determinant-chart Haar transport, raw/source
  Haar theorem, external/original source-prior comparison, passive Jacobian
  formula, source-image equality, source-rank coverage, normal crossings, pole
  order, or RLCT is claimed.
- **Current status addendum, retained-passive chart-produced punctured-sector
  residual-source socket, 2026-06-29.** Lean now proves
  `exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_marginal`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean`,
  imported by `lean/DLNFibre.lean`.  The theorem works over an arbitrary
  coordinate-domain measure, calls the punctured-sector readout theorem to
  choose an open determinant-and-pivot-nonzero sector `V`, and for
  `mu = Measure.map sourceChart (sourceMeasure.restrict V)` and
  `marginal = Measure.map Prod.snd (sourceMeasure.restrict V)` proves
  `mu.restrict localSource = mu` and transfers explicit marginal residual
  positivity and finite negative-power integrability assumptions to the
  retained-passive p.13 residual-source hypotheses for `mu`.  Reproduction,
  statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-chart-produced-punctured-sector-residual-source-socket.md`,
  `threads/03-block-product-reduction/statement-card-a2-retained-passive-chart-produced-punctured-sector-residual-source-socket.md`,
  and
  `threads/03-block-product-reduction/review-a2-retained-passive-chart-produced-punctured-sector-residual-source-socket.md`.
  Focused build and full `DLNFibre` build passed via `scripts/lb`; `scripts/sorries`,
  `git diff --check`, the added Lean-line forbidden-marker scan, and direct
  axiom probe passed with `[propext, Classical.choice, Quot.sound]`.  Xhigh
  read-only review by `Harvey the 3rd` returned PASS.  This is only a
  chart-produced residual-source socket: no marginal positivity/integrability
  for arbitrary `sourceMeasure`, determinant-chart Haar transport, raw/source
  Haar theorem, external/original source-prior comparison, passive Jacobian
  formula, selected-entry source-image equality, source-rank coverage, normal
  crossings, pole order, or RLCT is claimed.
- **Current status addendum, retained-passive chart-produced punctured-sector
  measure readout, 2026-06-29.** Lean now proves
  `exists_open_measure_map_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_eq_snd`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasure.lean`,
  plus the helper
  `SelectedEntrySignedBox.CenterCoord.measurable_preimageOfPivotNeZero` in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean`.  The theorem
  works over an arbitrary coordinate-domain measure on `eta x (center -> R)`,
  restricted to the open determinant-and-pivot-nonzero sector.  Its
  chart-produced source pushforward is supported on the retained-passive p.13
  local source, and the source-side inverse residual readout pushes that
  measure back to `Measure.map Prod.snd` of the restricted coordinate-domain
  measure.  Reproduction, statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-chart-produced-punctured-sector-measure-readout.md`,
  `threads/03-block-product-reduction/statement-card-a2-retained-passive-chart-produced-punctured-sector-measure-readout.md`,
  and
  `threads/03-block-product-reduction/review-a2-retained-passive-chart-produced-punctured-sector-measure-readout.md`.
  Focused build and full `DLNFibre` build passed via `scripts/lb`; `scripts/sorries`,
  `git diff --check`, the touched Lean-file forbidden-marker scan, and direct
  axiom probes passed with `[propext, Classical.choice, Quot.sound]`.  Xhigh
  read-only review by `Hubble the 3rd` returned PASS.  This is only a chart-produced
  sector-measure theorem: no determinant-chart Haar transport, raw/source
  Haar theorem, external/original source-prior comparison, passive Jacobian
  formula, selected-entry source-image equality, source-rank coverage, normal
  crossings, pole order, or RLCT is claimed.
- **Current status addendum, retained-passive source-prior coordinate-domain
  frontier, 2026-06-29.** A controller reproduction and xhigh read-only review
  now sharpen the source-measure boundary at
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-source-prior-coordinate-domain.md`
  and
  `threads/03-block-product-reduction/review-a2-retained-passive-source-prior-coordinate-domain.md`.
  The artifact is not a Lean theorem.  It records that Aoyagi pp. 10-13
  support the Schur/product algebra, retained-passive coordinate inverse, and
  p.13 product-difference variables, but do not by themselves identify the
  reduced selected-entry signed-box measure with full determinant-chart Haar
  measure or with an external/original DLN source prior.  The next theorem in
  this lane must remove a named field: either a passive-variable-explicit
  sector transport theorem, an external-prior density or mutual absolute
  continuity comparison, or a consumer genuinely rewritten over the
  chart-produced passive sector measure.  No source-prior transport,
  selected-entry image coverage, determinant-chart Haar theorem for the
  reduced section, source-rank coverage, normal crossings, pole order, or RLCT
  is claimed.
- **Current status addendum, retained-passive passive-variable sector transport
  frontier, 2026-06-29.** A reviewed controller specification now records the
  passive-variable-explicit sector needed before the source-measure lane can
  honestly remove determinant-chart `hmap` fields or compare with an external
  source prior:
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-passive-variable-sector-transport.md`,
  `threads/03-block-product-reduction/statement-card-a2-retained-passive-passive-variable-sector-transport.md`,
  and
  `threads/03-block-product-reduction/review-a2-retained-passive-passive-variable-sector-transport.md`.
  Xhigh read-only reviews by `Linnaeus the 3rd` and `Halley the 3rd` returned
  PASS after minor wording repairs.  The raw passive variables are typed over
  `case2PostPivotTwoEdgeDomain ...`; endpoint equivalences move them to the
  fixed-base endpoint complement indices.  The next Lean target should be a
  combined with-passive open punctured-sector inverse/readout package, not a
  measure theorem and not another finite-integral wrapper.  No passive-sector
  Haar transport, external/original source-prior comparison, selected-entry
  source-image equality, source-rank coverage, normal crossings, pole order, or
  RLCT is claimed.
- **Current status addendum, retained-passive open punctured-sector readout,
  2026-06-29.** Lean now proves
  `exists_open_case2EndpointTransport_withPassive_detChart_sourceReadback_eq_preimageOfPivotNeZero_residualReadout_eq`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySource.lean`.
  This is the first subtarget from the passive-variable sector frontier: on
  the open determinant-domain source-readback neighborhood, and under the
  pointwise hypothesis `z.2 pivotNext != 0`, the selected-entry inverse of the
  residual readout from `sourceReadback E` recovers the original selected-entry
  residual vector.  Reproduction, statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-open-punctured-sector-readout.md`,
  `threads/03-block-product-reduction/statement-card-a2-retained-passive-open-punctured-sector-readout.md`,
  and
  `threads/03-block-product-reduction/review-a2-retained-passive-open-punctured-sector-readout.md`.
  Focused build and full `DLNFibre` aggregator build passed via `scripts/lb`;
  xhigh read-only review by `Anscombe the 3rd` returned PASS.
  `git diff --check`, `scripts/sorries`, the touched Lean-file
  forbidden-marker scan, and the direct axiom probe passed; the new theorem
  reports `[propext, Classical.choice, Quot.sound]`.  This is pointwise
  readout only: no measure equality, determinant-chart Haar transport,
  source-prior comparison, selected-entry source-image equality, source-rank
  coverage, normal crossings, pole order, or RLCT is claimed.
- **Current status addendum, Case 2 passive Jacobian-weighted source-stratum
  bounds finite integral, 2026-06-29.** Lean now exposes
  `exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass_sourceStratum_bounds`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean`.
  This is the source-stratum-bound analogue of the passive Jacobian-weighted
  local-source finite-integral handoff: it constructs the source-domain
  determinant neighborhood `Udom`, forms the chart-produced
  Jacobian-weighted measure
  `(sourceMeasure.restrict Udom).withDensity (fun z => ofReal (J z))`,
  pushes it forward by the p.13 source chart to `muJ`, and proves a finite
  regular-coordinate integral over
  `(muJ.restrict (U ∩ sourceStratum)).prod ν`.  The regular-coordinate loss
  lower bound and density bounds are assumed on `nhdsWithin base sourceStratum`;
  residual positivity and residual negative-power integrability still come
  from the retained-passive local-source residual package, plus the local
  coverage open around the fixed base.  Reproduction and statement card are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-jacobian-weighted-source-stratum-bounds-finite-integral.md`
  and
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-jacobian-weighted-source-stratum-bounds-finite-integral.md`.
  Focused build passed for
  `DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`.  Full
  `DLNFibre` aggregator build, `git diff --check`, `scripts/sorries`, and
  direct axiom probe passed.  Xhigh reviews by `Bernoulli the 3rd` and
  `Kant the 3rd` returned PASS after a docstring nonclaim-boundary repair.
  This is only a
  chart-produced passive product-domain finite-integral handoff with
  source-stratum comparison hypotheses: no exact localized residual marginal,
  determinant-chart/raw Haar transport, original source-prior transport,
  source-prior Jacobian formula, source-image equality or source-rank
  coverage, normal crossings, pole order, or RLCT.
- **Current status addendum, Case 2 passive Jacobian-weighted local-source
  finite integral, 2026-06-29.** Lean now exposes
  `exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean`.
  The theorem constructs a source-domain determinant neighborhood `Udom`,
  forms the chart-produced Jacobian-weighted measure
  `(sourceMeasure.restrict Udom).withDensity (fun z => ofReal (J z))`,
  pushes it forward by the p.13 source chart to `muJ`, and proves a finite
  regular-coordinate integral over
  `(muJ.restrict (U ∩ sourceStratum)).prod ν` for some edge-family open
  neighborhood `U` of the fixed base.  The proof consumes the residual-source
  theorem, derives `SFinite muJ` from finite passive mass, and applies the
  generic retained-passive local-source finite-integral theorem with identity
  `Cedge`.  Reproduction, statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-jacobian-weighted-local-source-finite-integral.md`,
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-jacobian-weighted-local-source-finite-integral.md`,
  and
  `threads/03-block-product-reduction/review-a2-case2-passive-jacobian-weighted-local-source-finite-integral.md`.
  Focused build passed for
  `DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`.  Full
  `DLNFibre` aggregator build, `git diff --check`, `scripts/sorries`, and
  direct axiom probe passed.  Xhigh reviews by `Erdos the 3rd` and
  `Lovelace the 3rd` returned PASS.  This is only a chart-produced passive
  product-domain finite-integral handoff: no exact localized residual
  marginal, determinant-chart/raw Haar transport, original source-prior
  transport, source-prior Jacobian formula, source-image equality or local
  coverage, normal crossings, pole order, or RLCT.
- **Current status addendum, Case 2 passive Jacobian-weighted residual source
  hypotheses, 2026-06-29.** Lean now exposes
  `exists_open_residualSourceHypotheses_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean`.
  The theorem packages the previously proved whole-measure
  Jacobian-weighted passive residual integrability theorem over the retained-
  passive p.13 local source.  The proof reindexes the selected-entry `center`
  residual coordinate square sum to the native fixed-base residual-coordinate
  square sum by `aoyagiCoordinateSquareSum_comp_equiv`, then uses
  chart-produced support to rewrite `muJ.restrict localSource = muJ`.
  Reproduction and statement card are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-jacobian-weighted-residual-source-hypotheses.md`
  and
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-jacobian-weighted-residual-source-hypotheses.md`.
  Review is at
  `threads/03-block-product-reduction/review-a2-case2-passive-jacobian-weighted-residual-source-hypotheses.md`.
  Focused build passed for
  `DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`.  Full
  `DLNFibre` aggregator build, `git diff --check`, `scripts/sorries`, and
  direct axiom probe passed.  Xhigh reviews by `Dirac the 3rd` and
  `Hegel the 3rd` returned PASS.  This is only
  residual-source packaging for the same chart-produced passive
  Jacobian-weighted measure: no exact localized residual marginal,
  determinant-chart/raw Haar transport, original source-prior transport,
  source-prior Jacobian formula, source-image equality or local coverage,
  normal crossings, pole order, or RLCT.
- **Current status addendum, Case 2 passive selected-entry weighted local
  source support after open restriction, 2026-06-29.** Lean now exposes
  `exists_open_measure_map_case2EndpointTransport_withPassive_withDensity_restrict_retainedPassiveP13LocalSource_eq_self`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasure.lean`.
  For passive selected-entry coordinates, continuity of the passive fields and
  determinant-unit hypotheses at one base point produce an open determinant
  domain `U`; for any source-domain measure and any density, the pushforward
  of `(sourceMeasure.restrict U).withDensity density` along the fixed-base
  p.13 source chart is supported on the retained-passive local source.  A.e.
  measurability of the source chart and a.e. local-source membership are
  transferred from the restricted base measure to the weighted measure using
  `withDensity_absolutelyContinuous`.  Reproduction, statement card, and
  review are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-selected-entry-weighted-local-source-support-after-open-restriction.md`,
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-selected-entry-weighted-local-source-support-after-open-restriction.md`,
  and
  `threads/03-block-product-reduction/review-a2-case2-passive-selected-entry-weighted-local-source-support-after-open-restriction.md`.
  Focused build passed for
  `DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasure`.
  Full `DLNFibre` aggregator build, `git diff --check`, `scripts/sorries`,
  and direct axiom probe passed.  Xhigh reviews by `Nietzsche the 3rd` and
  `Schrodinger the 3rd` returned PASS.  This is arbitrary-density support
  only after restricting the source-domain measure to the constructed open
  determinant domain: no Jacobian identification, global determinant-chart
  membership, source-image equality, local coverage, source-rank support or
  coverage, determinant-chart/raw Haar transport, source-prior transport,
  exact localized residual marginal, normal crossings, pole order, or RLCT.
- **Current status addendum, Case 2 passive selected-entry local source support
  after open restriction, 2026-06-29.** Lean now exposes
  `exists_open_measure_map_case2EndpointTransport_withPassive_restrict_retainedPassiveP13LocalSource_eq_self`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasure.lean`.
  For passive selected-entry coordinates, continuity of the passive fields and
  determinant-unit hypotheses at one base point produce an open determinant
  domain `U`; for any source-domain measure, the pushforward of
  `sourceMeasure.restrict U` along the fixed-base p.13 source chart is
  supported on the retained-passive local source.  A.e. measurability of the
  source chart on the restricted measure is derived internally from
  determinant-chart subtype continuity.  Reproduction and statement card are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-selected-entry-local-source-support-after-open-restriction.md`
  and
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-selected-entry-local-source-support-after-open-restriction.md`.
  Focused build passed for
  `DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasure`.
  Full `DLNFibre` aggregator build, `git diff --check`, `scripts/sorries`,
  and direct axiom probe passed.  Xhigh reviews by `Singer the 3rd` and
  `Descartes the 3rd` returned PASS after one stale reproduction-note wording
  repair; review is at
  `threads/03-block-product-reduction/review-a2-case2-passive-selected-entry-local-source-support-after-open-restriction.md`.
  This is support only after restricting the source-domain measure to the
  constructed open determinant domain: no global determinant-chart membership,
  source-image equality, local coverage, source-rank support or coverage,
  determinant-chart/raw Haar transport, source-prior transport, Jacobian
  transport, exact localized residual marginal, normal crossings, pole order,
  or RLCT.
- **Current status addendum, Case 2 passive selected-entry local
  source-readback domain, 2026-06-29.** Lean now exposes
  `exists_open_case2EndpointTransport_withPassive_detChart_sourceReadback_eq`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySource.lean`.
  For passive selected-entry coordinates, continuity of the passive fields and
  determinant-unit hypotheses at one base point produce an open neighborhood
  on which the fixed-base p.13 source chart lies in the retained-passive local
  source, and source readback of its extracted edge matrices recovers the full
  endpoint-transported retained-passive datum.  Reproduction and statement
  card are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-selected-entry-local-source-readback-domain.md`
  and
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-selected-entry-local-source-readback-domain.md`.
  Focused build, full aggregator build, `git diff --check`, `scripts/sorries`,
  and direct axiom probe passed.  Xhigh reviews by `McClintock the 3rd` and
  `Galileo the 3rd` returned PASS; review is at
  `threads/03-block-product-reduction/review-a2-case2-passive-selected-entry-local-source-readback-domain.md`.
  This is local source-coordinate inverse/readback only: no selected-entry source-image
  equality, local coverage, source-rank coverage, determinant-chart Haar
  transport, raw/source Haar theorem, source-prior transport, Jacobian
  transport, exact localized residual marginal, normal crossings, pole order,
  or RLCT.
- **Current status addendum, Case 2 passive Jacobian-weighted residual
  integrability, 2026-06-29.** Lean now exposes
  `ae_of_measure_le_smul`, `lintegral_lt_top_of_measure_le_smul`,
  `map_le_smul_map_of_le_smul`, and
  `measure_le_smul_of_le_smul_restrict` in
  `lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean`, plus
  `exists_open_residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean`.
  For a small open neighborhood `U`, residual square-sum positivity a.e. and
  finite negative-power lintegral are proved for
  `Measure.map sourceChart ((sourceMeasure.restrict U).withDensity (fun z => ofReal (J z)))`,
  assuming finite total passive mass and the selected-entry critical
  hypotheses.  Reproduction and statement card are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-jacobian-weighted-residual-integrability.md`
  and
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-jacobian-weighted-residual-integrability.md`.
  Review is at
  `threads/03-block-product-reduction/review-a2-case2-passive-jacobian-weighted-residual-integrability.md`.
  Focused build, `git diff --check`, `scripts/sorries`, direct axiom probes,
  and xhigh review passed after two stale module-doc boundary fixes.
  This is local domination transfer only: no exact localized residual
  marginal, determinant-chart Haar transport, raw/source Haar theorem,
  source-prior transport, selected-entry image coverage, local inverse/coverage,
  normal crossings, pole order, or RLCT.
- **Current status addendum, Case 2 passive residual finite-mass integrability,
  2026-06-29.** Lean now exposes
  `residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_finiteMass`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean`.
  For the passive chart-produced source measure
  `Measure.map sourceChart (passiveMeasure.prod weightedBox)`, residual
  square-sum positivity a.e. and finite negative-power lintegral are proved
  below the selected-entry critical threshold, assuming finite total passive
  mass `passiveMeasure Set.univ < infinity`.  Reproduction and statement card
  are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-residual-finite-mass-integrability.md`
  and
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-residual-finite-mass-integrability.md`.
  Focused build, xhigh review, `git diff --check`, `scripts/sorries`, and
  direct axiom probe passed.  This is a global residual-coordinate consequence
  only: no
  determinant-chart Haar transport, raw/source Haar theorem, source-prior
  transport, selected-entry image coverage, arbitrary localized residual
  marginal, local inverse/coverage, normal crossings, pole order, or RLCT.
- **Current status addendum, Case 2 passive Jacobian withDensity sandwich,
  2026-06-29.** Lean now exposes
  `withDensity_ofReal_sandwich_of_ae_bounds` in
  `lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean` and
  `exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive_passiveProductMeasure`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean`.
  For the concrete passive product-domain measure restricted to a small open
  neighborhood, weighting by the retained-passive solved-`A1` product
  raw-order Jacobian factor gives a measure bounded above and below by
  positive scalar multiples of the restricted measure.  Reproduction and
  statement card are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-jacobian-withdensity-sandwich.md`
  and
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-jacobian-withdensity-sandwich.md`.
  Focused build, xhigh review, `git diff --check`, `scripts/sorries`, and
  direct axiom probes passed.  This is passive chart-domain bounded-density
  bookkeeping only: no
  determinant-chart Haar transport, raw/source Haar theorem, external or
  original source-prior comparison, selected-entry image coverage, source-rank
  coverage, local inverse/coverage, normal crossings, pole order, or RLCT.
- **Current status addendum, Case 2 passive Jacobian product bounded-unit
  a.e. handoff, 2026-06-29.** Lean now exposes
  `exists_open_ae_restrict_of_eventually_nhds` in
  `lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean` and
  `exists_pos_open_ae_restrict_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive_passiveProductMeasure_bounds`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean`.
  For the concrete passive product-domain measure
  `passiveMeasure.prod weightedBox`, the retained-passive solved-`A1` product
  raw-order Jacobian density is a.e. bounded above and below by positive
  constants after restricting to a small open neighborhood of a
  determinant-chart basepoint.  Reproduction and statement card are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-jacobian-product-bounded-unit-ae-handoff.md`
  and
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-jacobian-product-bounded-unit-ae-handoff.md`.
  Focused build, xhigh review, `git diff --check`, `scripts/sorries`, and
  direct axiom probes passed.  This
  is passive chart-domain a.e. bounded-unit bookkeeping only: no
  determinant-chart Haar transport, raw/source Haar transport, external or
  original source-prior comparison, positive-mass/support assertion,
  selected-entry image coverage, source-rank coverage, local inverse/coverage,
  normal crossings, pole order, or RLCT.
- **Current status addendum, Case 2 passive Jacobian product bounded unit,
  2026-06-29.** Lean now exposes
  `exists_pos_eventually_bounds_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean`.
  For the endpoint-transported passive Case 2 selected-entry coordinate map
  `Y`, the retained-passive solved-`A1` product raw-order Jacobian density is
  eventually bounded above and below by positive constants near any basepoint
  whose `Ctop` and passive `A1` determinants are units.  The theorem assumes
  continuity of the passive fields and does not require determinant-unit
  hypotheses away from the basepoint.  Reproduction, statement card, and review
  are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-jacobian-product-bounded-unit.md`,
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-jacobian-product-bounded-unit.md`,
  and
  `threads/03-block-product-reduction/review-a2-case2-passive-jacobian-product-bounded-unit.md`.
  Xhigh review passed.  This is passive retained-coordinate Jacobian-unit
  bookkeeping only: no determinant-chart Haar transport, raw/source Haar
  transport, external/original source-prior comparison, selected-entry image
  coverage, source-rank coverage, local inverse/coverage, normal crossings,
  pole order, or RLCT.
- **Current status addendum, Case 2 passive residual-coordinate product-measure
  pushforward, 2026-06-29.** Lean now exposes
  `measure_map_residualBlockCoordinateMap_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_eq_smul_restrict_chartMap_image`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean`.
  For the concrete passive product-domain source measure
  `passiveMeasure.prod weightedBox`, the residual-coordinate pushforward of
  the chart-produced source measure is
  `passiveMeasure Set.univ` times the selected-entry chart-image measure.  The
  scalar is essential because `passiveMeasure` is arbitrary.  Reproduction,
  statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-residual-coordinate-product-measure-pushforward.md`,
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-residual-coordinate-product-measure-pushforward.md`,
  and
  `threads/03-block-product-reduction/review-a2-case2-passive-residual-coordinate-product-measure-pushforward.md`.
  Focused build and xhigh feasibility/scope reviews passed.  This is a
  residual-coordinate marginal for a chart-produced product-domain measure
  only: no determinant-chart Haar pushforward, raw/source Haar theorem,
  original source-prior transport, passive Jacobian/source-density accounting
  for an ambient prior, source-rank coverage, source-image equality, local
  inverse/coverage, normal crossings, pole order, or RLCT.
- **Current status addendum, Case 2 passive product-measure support,
  2026-06-29.** Lean now exposes
  `case2PassiveDomainProductMeasure_eq_prod_withDensity_sourceDensity`,
  `measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_restrict_retainedPassiveP13LocalSource_eq_self`,
  and
  `measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_restrict_sourceRankStratum_eq_self`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean`.
  The source measure is
  `passiveMeasure.prod (signedBox.withDensity selectedEntrySourceDensity)`.
  Continuity of the passive fields supplies a.e. measurability of the source
  chart, and the arbitrary passive chart-produced support wrappers give
  retained-passive local-source support and, under explicit a.e. rank
  hypotheses, source-rank support.  Reproduction, statement card, and review
  are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-product-measure-support.md`,
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-product-measure-support.md`,
  and
  `threads/03-block-product-reduction/review-a2-case2-passive-product-measure-support.md`.
  Focused build, `git diff --check`, `scripts/sorries`, direct axiom probes,
  and xhigh review passed.  This is concrete
  chart-produced support only: no source-rank coverage, source-image equality,
  determinant-chart pushforward, source-prior transport, normal crossings,
  pole order, or RLCT.
- **Current status addendum, Case 2 passive source-chart continuity,
  2026-06-29.** Lean now exposes
  `continuous_case2PostPivotSelectedEntryRetainedPassiveDataWithPassive` in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean`
  and
  `continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport_withPassive`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean`.
  These theorems prove continuity of the passive selected-entry finite datum
  and continuity of the endpoint-transported fixed-base source edge-family
  chart under continuity of the passive fields.  The source-chart theorem uses
  pointwise determinant-unit hypotheses to enter the determinant-chart subtype
  and has no measure or rank hypotheses.  Reproduction and statement card are
  at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-source-chart-continuity.md`
  and
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-source-chart-continuity.md`.
  Focused build, `git diff --check`, `scripts/sorries`, direct axiom probes,
  and xhigh review passed.  This is
  regularity infrastructure only: no concrete passive product measure,
  source-rank coverage, source-image equality, determinant-chart pushforward,
  source-prior transport, normal crossings, pole order, or RLCT.
- **Current status addendum, Case 2 passive chart-produced support,
  2026-06-29.** Lean now exposes
  `measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_restrict_retainedPassiveP13LocalSource_eq_self`
  and
  `measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_restrict_sourceRankStratum_eq_self`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean`.
  These theorems lift the passive pointwise local-source/source-rank support
  lemmas to arbitrary chart-produced measures on `eta x (center -> R)`, with
  `AEMeasurable sourceChart sourceMeasure` explicit and the successor rank
  equation assumed a.e. for source-rank support.  Reproduction and statement
  card are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-chart-produced-support.md`
  and
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-chart-produced-support.md`.
  Focused build passed, and direct axiom probes for both theorem names report
  `[propext, Classical.choice, Quot.sound]`.
  Xhigh review passed with no findings in
  `threads/03-block-product-reduction/review-a2-case2-passive-chart-produced-support.md`.
  This is chart-produced support bookkeeping only: no concrete passive product
  measure, source-rank coverage, source-image equality, determinant-chart
  pushforward, source-prior transport, normal crossings, pole order, or RLCT.
- **Current status addendum, Case 2 passive-parameter fixed-base source
  readback, 2026-06-29.** Lean now exposes
  `retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean`.
  The theorem defines a fixed-base p.13 source family on
  `eta x (center -> R)` from passive field families and selected-entry
  residual coordinates.  Under explicit determinant-unit hypotheses on
  `Ctop` and `A1passive`, every produced source family lands in the
  retained-passive local source, and source readback recovers a residual factor
  product equal to the selected-entry center-coordinate matrix.  Reproduction
  and statement card are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-parameter-fixed-base-source-readback.md`
  and
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-parameter-fixed-base-source-readback.md`.
  Controller review and xhigh review passed with no findings in
  `threads/03-block-product-reduction/review-a2-case2-passive-parameter-fixed-base-source-readback.md`;
  direct axiom probe reports `[propext, Classical.choice, Quot.sound]`.
  This is source-map/readback bookkeeping only: no source-image equality,
  local coverage of arbitrary source points, measure pushforward,
  source-prior transport, normal crossings, pole order, or RLCT.
- **Current status addendum, Case 2 passive-parameter pointwise support
  readout, 2026-06-29.** Lean now exposes
  `case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_mem_sourceRankStratum`,
  `paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive`,
  and
  `case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_mem_sourceRankStratum_and_localSource_and_residualBlockCoordinateMap_eq_chartMap`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean`.
  The combined theorem says each constructed passive-sector point lies in the
  specified source-rank stratum and retained-passive p.13 local source, and its
  residual coordinate map is the selected-entry chart map, under explicit
  determinant-unit and pointwise rank hypotheses.  Reproduction and statement
  card are at
  `threads/03-block-product-reduction/reproduction-a2-case2-passive-parameter-pointwise-support-readout.md`
  and
  `threads/03-block-product-reduction/statement-card-a2-case2-passive-parameter-pointwise-support-readout.md`.
  Xhigh review passed with no findings in
  `threads/03-block-product-reduction/review-a2-case2-passive-parameter-pointwise-support-readout.md`;
  direct axiom probe reports `[propext, Classical.choice, Quot.sound]`.
  This is pointwise support/readout only: no source-rank coverage, no
  source-image equality, no measure pushforward, no source-prior transport,
  no normal crossings, pole order, or RLCT.
- **Current status addendum, Case 2 selected-entry passive-parameter datum,
  2026-06-29.** Lean now exposes
  `case2PostPivotSelectedEntryRetainedPassiveDataWithPassive`,
  `case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_detChart`,
  `case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_detChart`,
  and
  `case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean`.
  The theorem family enlarges the reduced selected-entry retained-passive
  datum by supplied passive fields while keeping the residual `C` family
  unchanged.  Under explicit `Ctop` and `A1passive` determinant-unit
  hypotheses, the datum and endpoint transport land in the determinant chart,
  and the endpoint-transported residual factor product is the same successor
  selected-entry center-coordinate chart matrix as before.  Reproduction and
  statement card are at
  `threads/03-block-product-reduction/reproduction-a2-case2-selected-entry-passive-parameter-datum.md`
  and
  `threads/03-block-product-reduction/statement-card-a2-case2-selected-entry-passive-parameter-datum.md`.
  Review is at
  `threads/03-block-product-reduction/review-a2-case2-selected-entry-passive-parameter-datum.md`
  and passed by xhigh Euclid the 3rd.
  This is finite coordinate algebra only: it does not prove a source map,
  local inverse, image/coverage theorem, measure pushforward, source-prior
  transport, normal crossings, pole order, or RLCT.
- **Current status addendum, source-measure frontier after scout round,
  2026-06-29.** Post-interruption reorientation and three xhigh read-only
  scouts confirm that the next A2 work is a retained-passive source-measure
  construction package, not another finite-integral wrapper.  The local
  retained-passive `hcoverage` field used by the local-measure sockets is
  already discharged by an open subset of the determinant-chart preimage, and
  the retained-passive chart-layer raw-order inverse-Jacobian measure identity
  is already proved.  The remaining real blockers are the explicit Case 2
  determinant-chart pushforward
  `m.restrict Sdet = Measure.map chart weightedBox` and any original/external
  source-prior transport theorem.  Reorientation, reproduction, and statement
  card are at
  `threads/03-block-product-reduction/reorientation-a2-source-frontier-2026-06-29.md`,
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-source-prior-passive-variable-frontier.md`,
  and
  `threads/03-block-product-reduction/statement-card-a2-retained-passive-source-prior-passive-variable-frontier.md`.
  This addendum claims no new Lean theorem.  It records the kill condition
  that the reduced selected-entry signed-box section must not be used to claim
  full determinant-chart/raw Haar or original source-prior transport; passive
  variables need a named coordinate domain, source map, local inverse,
  image/coverage theorem, and Jacobian/passive-unit accounting.
- **Current status addendum, Case 2 source-rank-supported endpoint-basis
  original-loss finite-integral bridge, 2026-06-29.** Lean now exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_continuousAt_pos_density_restrict_open_of_sourceRankSupport`.
  This wraps the endpoint-basis original-loss source-stratum theorem with the
  existing Case 2 chart-produced source-rank support theorem.  Under explicit
  rank equations `hprod`, `hr0`, and `hr1`, the chart-produced measure
  satisfies `mu.restrict sourceStratum = mu`, so the final finite-integral
  conclusion is over `(mu.restrict U).prod nu` instead of
  `(mu.restrict (U inter sourceStratum)).prod nu`.  Reproduction and statement
  card are at
  `threads/03-block-product-reduction/reproduction-a2-case2-original-loss-source-rank-supported-finite-integral-bridge.md`
  and
  `threads/03-block-product-reduction/statement-card-a2-case2-original-loss-source-rank-supported-finite-integral-bridge.md`;
  review is at
  `threads/03-block-product-reduction/review-a2-case2-original-loss-source-rank-supported-finite-integral-bridge.md`.
  This is only support bookkeeping: the rank equations are
  hypotheses, not source-rank coverage; it does not prove selected-entry
  source/image equality, external source-prior transport, Jacobian comparison
  for such a prior, normal crossings, pole order, or RLCT.
- **Current status addendum, Case 2 endpoint-basis original-loss
  finite-integral bridge, 2026-06-29.** Lean now exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_continuousAt_pos_density`.
  For the endpoint-transported continuing Case 2 chart-produced selected-entry
  source measure, positive continuity of the regular-coordinate density gives
  a preliminary radius and upper density bound; the self-base multi-edge
  product-coordinate theorem gives the adapted p.13 product-difference lower
  bound at the final radius; and the finite endpoint-basis comparison turns
  that adapted lower bound into a lower bound for original endpoint
  square-Frobenius `lossDLN` in supplied endpoint bases.  The theorem returns
  finite integrability over
  `(mu.restrict (U inter sourceStratum)).prod nu`.  Reproduction, statement
  card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-case2-original-loss-finite-integral-bridge.md`,
  `threads/03-block-product-reduction/statement-card-a2-case2-original-loss-finite-integral-bridge.md`,
  and
  `threads/03-block-product-reduction/review-a2-case2-original-loss-finite-integral-bridge.md`.
  This removes the adapted-loss-only limitation for this chart-produced
  finite-integral direction, but it does not prove a reverse implication,
  source-rank support rewrite, selected-entry source/image equality, external
  source-prior transport, Jacobian comparison for such a prior, normal
  crossings, pole order, or RLCT.
- **Current status addendum, Case 2 adapted product-difference finite-integral
  bridge, 2026-06-29.** Lean now exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_adaptedProductDifferenceSquareSum_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_continuousAt_pos_density`.
  For the endpoint-transported continuing Case 2 chart-produced selected-entry
  source measure, positive continuity of the regular-coordinate density gives
  a preliminary radius and density bound; the self-base multi-edge
  product-coordinate theorem then gives the adapted p.13 product-difference
  lower bound at the final radius; the existing Case 2 source-stratum socket
  returns finite integrability over
  `(mu.restrict (U inter sourceStratum)).prod nu`.  Reproduction, statement
  card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-case2-adapted-product-difference-finite-integral-bridge.md`,
  `threads/03-block-product-reduction/statement-card-a2-case2-adapted-product-difference-finite-integral-bridge.md`,
  and
  `threads/03-block-product-reduction/review-a2-case2-adapted-product-difference-finite-integral-bridge.md`.
  This removes only the supplied regular-plus-residual lower comparison for
  the adapted p.13 square-sum.  It does not identify an original loss, prove a
  reverse implication, rewrite by source-rank support, prove selected-entry
  source/image equality, transport an external source prior or Jacobian,
  construct normal crossings, compute pole order, or extract RLCT.
- **Current status addendum, selected-entry center residual upper bound on
  small signed boxes, 2026-06-29.** Lean now exposes
  `SelectedEntrySignedBox.CenterCoord.residual_le_sq_of_abs_le`,
  `SelectedEntrySignedBox.CenterCoord.residual_le_sq_of_mem_signedBoxSet`,
  `SelectedEntrySignedBox.CenterCoord.residual_le_sq_ae_signedBox_of_smallBox`,
  and
  `SelectedEntrySignedBox.CenterCoord.residual_le_sq_ae_withDensity_sourceDensity_of_smallBox`.
  If all center coordinates are bounded by `δ` and
  `δ^2 * (1 + #(center.erase pivot) * δ^2) <= R^2`, then the
  center-indexed selected-entry residual is at most `R^2`; the same bound
  holds on a signed box with radii `<= δ`, and a.e. for the unweighted and
  selected-entry weighted signed-box source measures.  Reproduction,
  statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-selected-entry-center-residual-upper-bound-small-signed-box.md`,
  `threads/03-block-product-reduction/statement-card-a2-selected-entry-center-residual-upper-bound-small-signed-box.md`,
  and
  `threads/03-block-product-reduction/review-a2-selected-entry-center-residual-upper-bound-small-signed-box.md`.
  This does not yet push the bound through a retained-passive chart-produced
  measure, choose signed-box radii, prove selected-entry critical
  integrability, identify an original source prior/Jacobian/density, construct
  normal crossings, compute pole order, or extract RLCT.
- **Current status addendum, retained-passive source-edge-family
  chart-produced source-stratum two-sided continuous-density iff,
  2026-06-29.** Lean now exposes
  `exists_pos_radius_le_eventually_nhdsWithin_density_two_sided_bounds_of_continuousAt_pos`
  and
  `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure_continuousAt_pos_density`.
  Positive continuity of the transported density at `(base,0)` produces
  `R <= Rmax` and constants `0 < dρ`, `0 <= Dρ` with eventual source-stratum
  density bounds at radius `R`.  The two source-stratum loss comparison bounds
  are supplied at `Rmax` and restricted to `R`.  Residual boundedness is not
  inferred from `Rmax`; after `R` is produced, residual boundedness over the
  chart-produced measure restricted to `localSource` remains an explicit
  premise at `R^2` before the local iff is returned.  Reproduction, statement
  card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-source-edge-family-chart-produced-source-stratum-two-sided-continuous-density-iff.md`,
  `threads/03-block-product-reduction/statement-card-a2-retained-passive-source-edge-family-chart-produced-source-stratum-continuous-density-two-sided-iff.md`,
  and
  `threads/03-block-product-reduction/review-a2-retained-passive-source-edge-family-chart-produced-source-stratum-continuous-density-two-sided-iff.md`.
  This does not prove residual boundedness, loss comparison bounds,
  selected-entry critical integrability, signed-box source/image equality,
  source-rank coverage, external source-prior or Jacobian/density transport,
  normal crossings, pole order, or RLCT.
- **Current status addendum, retained-passive source-edge-family
  chart-produced source-stratum two-sided iff, 2026-06-29.** Lean now exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure`.
  For the concrete retained-passive source-edge-family chart produced from
  determinant-chart retained data, retained-data a.e. measurability and chart
  continuity give source-chart a.e. measurability; the retained source-edge-
  family readback theorem gives local-source landing and residual-factor
  matrix readout; and the square-sum bridge gives the selected-entry residual
  readout.  The theorem keeps residual boundedness over the chart-produced
  measure restricted to `localSource`, `[SFinite nu]`, `nu.IsAddHaarMeasure`,
  and the four source-stratum comparison bounds explicit, and returns the local
  iff between actual loss-density finiteness over
  `(mu.restrict (U inter sourceStratum)).prod nu` and
  `residualNegPowerIntegrableOn (fun E => E) (U inter sourceStratum) mu t`.
  Reproduction, statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-source-edge-family-chart-produced-source-stratum-two-sided-iff.md`,
  `threads/03-block-product-reduction/statement-card-a2-retained-passive-source-edge-family-chart-produced-source-stratum-two-sided-iff.md`,
  and
  `threads/03-block-product-reduction/review-a2-retained-passive-source-edge-family-chart-produced-source-stratum-two-sided-iff.md`.
  This does not prove residual boundedness, comparison bounds, selected-entry
  critical integrability, signed-box source/image equality, source-rank
  coverage, external source-prior or Jacobian/density transport, normal
  crossings, pole order, or RLCT.
- **Current status addendum, retained-passive source-stratum chart-produced
  selected-entry two-sided loss-density iff, 2026-06-29.** Lean now exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure`.
  For the selected-entry weighted signed-box chart-produced measure, pointwise
  chart landing in the retained-passive p.13 local source derives the
  local-source restriction equality required by the retained-passive
  source-stratum-bound selected-entry two-sided iff.  The theorem keeps
  residual readout, residual boundedness over the chart-produced measure
  restricted to `localSource`, and the four source-stratum comparison bounds
  explicit, and returns the local iff between actual loss-density finiteness
  over `(mu.restrict (U inter sourceStratum)).prod nu` and
  `residualNegPowerIntegrableOn Cedge (U inter sourceStratum) mu t`.
  Reproduction, statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-source-stratum-chart-produced-selected-entry-two-sided-loss-density-iff.md`,
  `threads/03-block-product-reduction/statement-card-a2-retained-passive-source-stratum-chart-produced-selected-entry-two-sided-loss-density-iff.md`,
  and
  `threads/03-block-product-reduction/review-a2-retained-passive-source-stratum-chart-produced-selected-entry-two-sided-loss-density-iff.md`.
  This does not prove chart landing, residual readout, comparison bounds,
  residual boundedness, selected-entry critical integrability, signed-box
  source/image equality, source-rank coverage, external source-prior or
  Jacobian/density transport, normal crossings, pole order, or RLCT.
- **Current status addendum, retained-passive source-stratum selected-entry
  two-sided loss-density iff, 2026-06-29.** Lean now exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds`.
  For the retained-passive p.13 local source, the selected-entry monomial
  lower bound plus supplied residual readout and signed-box pushforward prove
  residual positivity on the local source.  The retained-passive self-base
  local coverage theorem then allows the source-stratum/local-source two-sided
  iff to use source-rank-stratum comparison bounds.  The theorem keeps
  residual boundedness and all four source-stratum comparison bounds explicit,
  and returns the local iff between actual loss-density finiteness over
  `(mu.restrict (U inter sourceStratum)).prod nu` and
  `residualNegPowerIntegrableOn Cedge (U inter sourceStratum) mu t`.
  Reproduction, statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-source-stratum-selected-entry-two-sided-loss-density-iff.md`,
  `threads/03-block-product-reduction/statement-card-a2-retained-passive-source-stratum-selected-entry-two-sided-loss-density-iff.md`,
  and
  `threads/03-block-product-reduction/review-a2-retained-passive-source-stratum-selected-entry-two-sided-loss-density-iff.md`.
  This does not prove signed-box pushforward, residual readout, comparison
  bounds, residual boundedness, selected-entry critical integrability,
  signed-box source/image equality, source-rank coverage, external source-prior
  or Jacobian/density transport, normal crossings, pole order, or RLCT.
- **Current status addendum, retained-passive chart-produced selected-entry
  two-sided loss-density iff, 2026-06-29.** Lean now exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure`.
  For the selected-entry weighted signed-box chart-produced measure, pointwise
  chart landing in the retained-passive p.13 local source derives the
  local-source restriction equality required by the retained-passive
  local-source selected-entry two-sided iff.  The theorem keeps residual
  readout, residual boundedness, and the four two-sided comparison bounds
  explicit, and returns the local iff between actual loss-density finiteness
  over `(mu.restrict (U inter localSource)).prod nu` and
  `residualNegPowerIntegrableOn Cedge (U inter localSource) mu t`.
  Reproduction, statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-chart-produced-selected-entry-two-sided-loss-density-iff.md`,
  `threads/03-block-product-reduction/statement-card-a2-retained-passive-chart-produced-selected-entry-two-sided-loss-density-iff.md`,
  and
  `threads/03-block-product-reduction/review-a2-retained-passive-chart-produced-selected-entry-two-sided-loss-density-iff.md`.
  This does not prove chart landing, residual readout, comparison bounds,
  residual boundedness, selected-entry critical integrability,
  retained-passive source coverage, source-rank coverage, source/image
  equality, external source-prior/Jacobian/density transport, normal
  crossings, pole order, or RLCT.
- **Current status addendum, retained-passive local-source selected-entry
  two-sided loss-density iff, 2026-06-29.** Lean now exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity`.
  For the retained-passive p.13 local source, continuity of `Cedge` supplies
  the source measurability and fixed-basis edge-matrix measurability needed by
  the selected-entry local-source two-sided iff.  The selected-entry signed-box
  pushforward, residual readout, residual boundedness, and four two-sided
  loss/density comparison bounds remain explicit.  The theorem returns a local
  iff between actual loss-density finiteness over
  `(mu.restrict (U inter localSource)).prod nu` and
  `residualNegPowerIntegrableOn Cedge (U inter localSource) mu t`.
  Reproduction, statement card, and review are at
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-local-source-selected-entry-two-sided-loss-density-iff.md`,
  `threads/03-block-product-reduction/statement-card-a2-retained-passive-local-source-selected-entry-two-sided-loss-density-iff.md`,
  and
  `threads/03-block-product-reduction/review-a2-retained-passive-local-source-selected-entry-two-sided-loss-density-iff.md`.
  This does not prove the signed-box pushforward or residual readout,
  comparison bounds, residual boundedness, selected-entry critical
  integrability, retained-passive source coverage, source-rank coverage,
  source/image equality, source-prior/Jacobian/density transport, normal
  crossings, pole order, or RLCT.
- **Current status addendum, generic selected-entry chart-produced determinant
  residual, 2026-06-28.** Lean now exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_selectedEntrySignedBox_chartProducedMeasure`.
  For any selected-entry chart-produced measure supported on the retained-
  passive determinant chart, this theorem proves determinant-chart residual
  positivity and finite negative-power residual integral from direct residual
  positive-set measurability and the selected-entry residual readout.  The Case
  2 chart-produced determinant residual theorem now uses this generic front
  end.  This is not an arbitrary-measure theorem, Haar/source-prior transport,
  full determinant-chart coverage, source-rank coverage, normal crossings,
  pole order, or RLCT.
- **Current status addendum, Case 2 chart-produced determinant residual
  support wrapper, 2026-06-28.** Lean now exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_selectedEntrySignedBox_chartProducedMeasure`.
  For the endpoint-transported explicit Case 2 selected-entry retained-passive
  chart, the selected-entry weighted signed-box pushforward measure is
  supported on `topologyTupleDetChartSet`; hence the existing supplied-map Case
  2 determinant residual theorem applies with the target measure fixed to that
  chart-produced measure.  The proof uses endpoint-transport determinant-chart
  membership, `topologyTuple`, open determinant-chart measurability,
  `withDensity_absolutelyContinuous`, `ae_map_iff`, and
  `Measure.restrict_eq_self_of_ae_mem`.  This does not remove the supplied-map
  hypothesis from the arbitrary-measure theorem, identify Haar measure or an
  external source prior, prove full determinant-chart coverage, prove
  source-rank coverage, prove normal crossings, compute pole order, or extract
  RLCT.
- **Current status addendum, Case 2 inverse-Jacobian continuous-density wrapper,
  2026-06-28.** Lean now exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_case2EndpointTransport_selectedEntrySignedBox_map_continuousAt_pos_density`.
  For the endpoint-transported Case 2 raw-order inverse-Jacobian source
  measure, positive continuity of the supplied integrand density at `(base,0)`
  supplies local density nonnegativity and boundedness after shrinking the
  regular-coordinate radius.  The theorem returns `R`, `C`, and `U` with
  `0 < R`, `R <= Rmax`, `0 <= C`, `IsOpen U`, and `base ∈ U`, plus the
  finite-integral conclusion over the raw-order inverse-Jacobian source measure.
  The determinant-chart pushforward identity, selected-entry residual inputs,
  and local loss lower bound remain explicit.  This does not identify Haar
  measure or an external source prior, prove chart coverage, prove source-rank
  coverage, construct normal crossings, compute pole order, or extract RLCT.
- **Current status addendum, retained-passive direct source-chart
  inverse-Jacobian measure, 2026-06-28.** Lean now exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.measure_map_paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_restrict_detChart_eq_map_rawOrderSourceChart_withDensity_inverseJacobian`.
  For the fixed-base retained-passive p.13 chart layer, the direct
  determinant-chart source-edge-family pushforward of Haar measure equals the
  public raw-order p.13 source-chart pushforward of the raw-order
  determinant-chart measure weighted by
  `topologyTupleEdgeRawOrderInverseJacobianDensity`.  The proof applies the
  retained-passive raw-order inverse-Jacobian change-of-variables theorem with
  downstream map equal to the raw-order source chart, then replaces
  `rawChart (topologyTupleEdgeRawOrder z)` by the direct source chart a.e. on
  the determinant chart.  This is retained-passive chart-layer
  source-measure/Jacobian transport only.  It does not identify an original
  external DLN source prior, prove source-rank coverage, prove selected-entry
  residual positivity/integrability, prove normal crossings, compute pole
  order, or extract RLCT.
- **Current status addendum, retained-passive source-edge-family density
  continuous-at finite integral, 2026-06-28.** Lean now exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceEdgeFamilyOfData_chartProducedMeasure_continuousAt_pos_density`.
  For the generic retained-passive source-edge-family chart-produced measure,
  positive continuity of `density` at `(base,0)` supplies local density
  nonnegativity and boundedness after shrinking the regular-coordinate radius.
  The theorem removes supplied `Rreg`, `Creg`, `0 <= Creg`, eventual density
  nonnegativity, and eventual density boundedness as inputs, returning a
  smaller `R`, a bound `C`, and an open neighborhood `U`.  It still assumes
  ambient `EdgeFamily` measurable/open-measurable/Borel structure,
  determinant-subtype measurable/open-measurable structure, `hdet`,
  `residualCoordEquiv`, `hdataFactor`, `hretainedData`, source data, positive
  `Rmax`, `creg`, and `t`, positive residual radii, the selected-entry
  critical inequality, Haar measure, and the local loss lower bound on
  `ball 0 Rmax`.  This does not construct endpoint equivalences, prove
  endpoint provenance, identify an original prior or external source measure,
  compare Jacobians for such a prior, prove source-rank coverage, prove normal
  crossings, compute pole order, or extract RLCT.
- **Current status addendum, retained-passive source-edge-family
  chart-produced measure, 2026-06-28.** Lean now exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceEdgeFamilyOfData_chartProducedMeasure`.
  For a retained-passive determinant-chart data path, the fixed-base p.13
  source edge-family map supplies the selected-entry chart-produced
  finite-integral handoff.  The theorem removes separate user-facing
  `hsourceChart`, `hchart_mem`, and `hfactor` assumptions by using
  `hretainedData`, `hdet`, and `hdataFactor` for the concrete
  `paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData` chart.  It
  still assumes determinant-subtype measurable/open-measurable structure,
  source data, local loss/density bounds, residual radii, the critical
  selected-entry inequality, and Haar measure.  This does not construct
  endpoint equivalences, prove endpoint provenance, identify an original prior
  or external source measure, compare Jacobians for such a prior, prove
  source-rank coverage, prove normal crossings, compute pole order, or extract
  RLCT.
- **Current status addendum, Case 2 chart-produced density continuous-at
  finite integral, 2026-06-28.** Lean now exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_continuousAt_pos_density`.
  For the endpoint-transported explicit Case 2 selected-entry chart-produced
  measure, positive continuity of the transported density at `(base,0)`
  supplies local density nonnegativity and boundedness after shrinking the
  regular-coordinate radius.  The theorem removes supplied `Rreg`, `Creg`,
  `0 <= Creg`, eventual density nonnegativity, and eventual density boundedness
  as inputs, returning a smaller `R`, a bound `C`, and an open neighborhood
  `U`.  This does not construct endpoint equivalences, prove endpoint
  provenance, identify an original prior or external source measure, compare
  Jacobians for such a prior, prove source-rank coverage, prove normal
  crossings, compute pole order, or extract RLCT.
- **Current status addendum, Case 2 topology-tuple source-family alignment,
  2026-06-28.** Lean now exposes
  `paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_topologyTuple_eq_sourceEdgeFamilyOfData`,
  and
  `PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_topologyTuple_eq_case2EndpointTransport_sourceEdgeFamilyOfData`.
  For any determinant-chart retained-passive datum, the raw-order p.13 source
  chart evaluated at `topologyTupleEdgeRawOrder (topologyTuple data)` is the
  direct fixed-base p.13 source edge family of `data`; for the endpoint-
  transported explicit Case 2 selected-entry datum, the determinant-chart
  hypothesis is discharged by the existing endpoint-transport determinant
  theorem.  This removes the concrete `ofTopologyTuple`/direct-datum mismatch
  on the raw-order p.13 source path.  It is not endpoint provenance,
  source-image equality, pushforward-measure transport, source-rank coverage,
  source-prior transport, Jacobian comparison, normal crossings, pole order, or
  RLCT.
- **Current status addendum, Case 2 fixed-pivot source-readback readout,
  2026-06-28.** Lean now exposes
  `case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_residualFactorProduct_fixedPivot_entry_eq_yNext`,
  `case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_residualFactorProduct_fixedPivot_entry_ne_zero_of_yNext_pivot_ne_zero`,
  `PaperEndpointFixedBaseRegularCoordinateSourceData.sourceReadback_residualFactorProduct_fixedPivot_entry_eq_yNext_of_case2EndpointTransport_sourceEdgeFamilyOfData`,
  and
  `PaperEndpointFixedBaseRegularCoordinateSourceData.sourceReadback_residualFactorProduct_fixedPivot_entry_ne_zero_of_case2EndpointTransport_sourceEdgeFamilyOfData_yNext_pivot_ne_zero`
  in the Case 2 selected-entry/local-jacobian bridge files.  For the
  endpoint-transported explicit Case 2 datum, and for the fixed-base source
  readback of the p.13 source edge family built from it, the residual-factor
  product entry corresponding to the displayed successor pivot `(J + 2,J + 2)`
  is exactly `yNext pivotNext`; under `hyNext` that fixed entry is nonzero.
  This removes the all-pivot existential ambiguity for this constructed
  branch, but does not construct `tau`, prove `hTau`, give canonical endpoint
  labelling, identify arbitrary `ofTopologyTuple` data, transport source
  priors, compare Jacobians, prove normal crossings, compute pole order, or
  extract RLCT.
- **Current status addendum, Case 2 endpoint-transport factor alignment,
  2026-06-28.** Lean now exposes
  `case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_C_one_submatrix_eq_displayedPostPivotResidualBlock`,
  `case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_C_zero_submatrix_eq_displayedPostPivotFreeFollowingFactor`,
  and
  `exists_pivot_residualFactorProduct_case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_eq_selectedEntryCenter_matrix_of_ne_zero`
  in `RetainedPassiveCase2SelectedEntryChartBridge.lean`.  For the
  endpoint-transported explicit Case 2 selected-entry retained-passive datum,
  the displayed post-pivot residual block and displayed free following factor
  are recovered from `C 1` and `C 0` by submatrixing with the forward endpoint
  equivalences.  The new all-pivot consumer removes supplied `hD`/`hF` for this
  explicit transported datum, while retaining the displayed-product nonzero
  hypothesis.  This does not prove product nonzeroness, fixed-pivot
  nonzeroness, arbitrary `ofTopologyTuple` factor alignment, fixed-base
  source-readback provenance, source-prior transport, Jacobian comparison,
  normal crossings, pole order, or RLCT.  Focused build and xhigh read-only
  statement/orientation check passed.
- **Current status addendum, Case 2 endpoint-transport pivot nonzero consumer,
  2026-06-28.** Lean now exposes
  `exists_pivot_residualFactorProduct_case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_eq_selectedEntryCenter_matrix_of_yNext_pivot_ne_zero`
  in `RetainedPassiveCase2SelectedEntryChartBridge.lean`.  This theorem
  applies the explicit-datum endpoint-transport factor-aligned all-pivot
  consumer under the concrete successor pivot-coordinate nonzero hypothesis
  `hyNext`, deriving displayed-product nonzeroness from the successor-source
  product equality and successor selected-entry matrix nonzero lemma.  The
  conclusion still returns some pivot and coordinates; it does not identify
  them with `(J + 2, J + 2)` or the supplied `yNext`.  This does not prove
  arbitrary `ofTopologyTuple` factor alignment, fixed-base source-readback
  provenance, source-prior transport, Jacobian comparison, normal crossings,
  pole order, or RLCT.
- **Current status addendum, Case 2 source-readback factor provenance,
  2026-06-28.** Lean now exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.sourceReadback_eq_case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_of_case2EndpointTransport_sourceEdgeFamilyOfData`,
  `PaperEndpointFixedBaseRegularCoordinateSourceData.sourceReadback_C_one_submatrix_eq_displayedPostPivotResidualBlock_of_case2EndpointTransport_sourceEdgeFamilyOfData`,
  and
  `PaperEndpointFixedBaseRegularCoordinateSourceData.sourceReadback_C_zero_submatrix_eq_displayedPostPivotFreeFollowingFactor_of_case2EndpointTransport_sourceEdgeFamilyOfData`
  in `RetainedPassiveCase2LocalJacobianMeasure.lean`.  The fixed-base source
  readback of the endpoint-transported explicit Case 2 source edge family is
  the transported datum itself; its readback `C 1` and `C 0` factors therefore
  recover the displayed post-pivot residual block and free following factor
  after forward endpoint reindexing.  This removes a real source-readback
  factor field for the constructed endpoint-transported datum, but does not
  construct `tau`, prove `hTau`, give label-preserving endpoint provenance,
  identify arbitrary `ofTopologyTuple` data, transport source priors, compare
  Jacobians, prove normal crossings, compute pole order, or extract RLCT.
- **Current status addendum, Case 2 self-endpoint transport, 2026-06-28.** Lean
  now exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_selfEndpoint_sourceEdgeFamilyOfData`
  in `RetainedPassiveCase2LocalJacobianMeasure.lean`.  This theorem is exactly
  the self-endpoint specialization of the supplied-equivalence
  endpoint-transport source-family theorem: it sets
  `tau := Case2ResidualColIndex n S (J + 1)` and uses
  `eNext := Equiv.refl _`.  The endpoint-family equivalences `e` remain
  supplied.  Focused build, sorry scan, whitespace check, touched Lean-file
  forbidden-marker search, direct axiom probe, and independent xhigh review
  passed with the standard `[propext, Classical.choice, Quot.sound]` footprint.
  This does not prove `hTau`, construct endpoint-family equivalences, prove
  endpoint provenance or label preservation, compare source priors or Jacobians,
  prove normal crossings, compute pole order, or extract RLCT.
- **Current status addendum, Case 2 residual endpoint scalar cardinalities,
  2026-06-28.** Lean now exposes
  `case2ResidualEndpoint_card_eqs_of_width_rank` and
  `case2PostPivotTwoEdgeDomain_card_eq_endpointComplementIndex_of_sourceData_width_rank`
  in `Case2ResidualFactorProduct.lean`.  The first theorem proves the
  successor residual column and row scalar cardinalities from the explicit
  hypotheses `H 2 = n (S + 1)`, `H 1 = prefixMinNat n S`, and `r = J + 1`, using
  finite interval cardinality.  The second theorem applies the existing
  source-data endpoint-cardinality bridge, leaving `hTau : card tau = H 3 - r`
  explicit.  This does not prove the width/rank identifications, prove `hTau`,
  construct `tau`, produce canonical endpoint labels, preserve selected
  entries, compare source priors or Jacobians, prove normal crossings, pole
  order, or RLCT.  Focused build, sorry scan, whitespace check, touched
  Lean-file forbidden-marker search, direct axiom probes, and xhigh review
  passed.
- **Current status addendum, Case 2 endpoint cardinalities from source data,
  2026-06-28.** Lean now exposes
  `case2PostPivotTwoEdgeDomain_card_eq_endpointComplementIndex_of_sourceData`
  in `Case2ResidualFactorProduct.lean`.  It derives the pointwise endpoint-
  cardinality family for `case2PostPivotTwoEdgeDomain n S J tau` from fixed-
  base source data and explicit scalar equalities for `tau`, the residual
  column type, and the residual row type.  This removes only `hEndpoints` once
  those scalar equalities are supplied.  It does not prove the scalar
  equalities, construct `tau`, produce canonical endpoint labels, preserve
  selected entries, compare source priors or Jacobians, prove normal crossings,
  pole order, or RLCT.
- **Current status addendum, endpoint equivalences from cardinalities,
  2026-06-28.** Lean now exposes
  `case2EndpointTransportEquivs_of_card_eq` in
  `Case2ResidualFactorProduct.lean`, a noncomputable finite constructor for
  the endpoint equivalence data required by the Case 2 endpoint-transport
  wrappers.  It requires explicit cardinality equalities for `eNext` and for
  each endpoint of the displayed two-edge family.  Lean also exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.endpointComplementIndex_card_eq_H_rev_sub_rank`
  in `RegularSuspensionCoordinates.lean`, computing fixed-base endpoint
  complement cardinalities as `H (q.rev.val + 1) - r` from source data.  This
  is finite cardinality/reindexing infrastructure only; it does not construct
  canonical or label-preserving endpoint equivalences, prove the geometric
  origin of `tau`, preserve selected entries or pivot order, construct charts,
  compare source priors or Jacobians, prove source-rank coverage, produce
  normal crossings, compute pole order, or extract RLCT.
- **Current status addendum, Case 2 endpoint-transport pre-measure from
  cardinalities, 2026-06-28.** Lean now exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData_card_eq`
  in `RetainedPassiveCase2LocalJacobianMeasure.lean`.  It replaces the
  supplied endpoint equivalences in the first Case 2 endpoint-transport
  fixed-base pre-measure input theorem by explicit endpoint cardinality
  equalities, constructs the noncanonical equivalences via
  `case2EndpointTransportEquivs_of_card_eq`, and applies the existing supplied-
  equivalence theorem.  It does not prove the cardinality equalities, canonical
  endpoint labels, selected-entry preservation, source-prior transport,
  Jacobian comparison, positivity/integrability, normal crossings, pole order,
  or RLCT.
- **Current status addendum, Case 2 endpoint-transport chart-produced finite
  integral, 2026-06-28.** Lean now exposes
  `ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_endpointTransport`,
  `ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_endpointTransport_detChart_subtype`,
  `PaperEndpointFixedBaseRegularCoordinateSourceData.continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport`,
  and
  `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure`.
  The endpoint-transported explicit Case 2 fixed-base source chart is
  continuous, hence supplies the measurability input for the generic
  chart-produced selected-entry finite-integral handoff.  The source measure is
  the selected-entry signed-box pushforward by this chart; local loss and
  density bounds, source-data, radii, exponent inequality, endpoint
  equivalences, and measurable/Borel structure on the source edge-family space
  remain explicit.  This does not identify an original source prior, compare
  Jacobians for an external prior, prove source-rank coverage, normal crossings,
  pole order, or RLCT.
- **Current status addendum, Case 2 endpoint-transport source-family residual
  square-sum, 2026-06-28.** Lean now exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_case2EndpointTransport_sourceEdgeFamilyOfData`
  in `RetainedPassiveCase2LocalJacobianMeasure.lean`.  It proves that the
  fixed-base residual-block coordinate square-sum of the source chart built
  from the endpoint-transported explicit Case 2 retained-passive datum equals
  the successor selected-entry center residual.  It still assumes the endpoint
  equivalences and does not prove source-chart measurability, source-prior
  pushforward, Jacobian density comparison, positivity/integrability, normal
  crossings, pole order, or RLCT.
- **Current status addendum, Case 2 endpoint-transport source-family
  pre-measure inputs, 2026-06-28.** Lean now exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData`
  in `RetainedPassiveCase2LocalJacobianMeasure.lean`.  Given supplied endpoint
  equivalences from the displayed Case 2 two-edge endpoint family to the
  fixed-base retained-passive endpoint family, the theorem builds the
  source-family chart from the endpoint-transported explicit Case 2 datum and
  returns local-source membership plus the source-readback selected-entry
  residual-factor matrix identity.  It does not construct the endpoint
  equivalences, transport `edgeMatrix` or `sourceReadback` as standalone
  operations, prove source-prior pushforward, Jacobian density comparison,
  positivity/integrability, normal crossings, pole order, or RLCT.
- **Current status addendum, source-edge-family pre-measure specialization,
  2026-06-28.** Lean now exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_sourceEdgeFamilyOfData`,
  which specializes the fixed-base pre-measure input bridge to the canonical
  source edge-family map attached to retained-passive coordinate data.  It
  removes the separate `hedge` input only in this fixed-base source-family
  setting, by using
  `paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq`.
  It still assumes determinant-chart proofs and the stored-data residual-factor
  readout, and it does not transport `edgeMatrix` or `sourceReadback`, prove
  endpoint-transported explicit Case 2 fixed-base realization, source-prior
  pushforward, Jacobian density comparison, normal crossings, pole order, or
  RLCT.
- **Current status addendum, fixed-base retained-passive pre-measure inputs,
  2026-06-28.** Lean now exposes
  `PaperEndpointFixedBaseRegularCoordinateSourceData.retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_retainedPassiveCoordinateData_edgeMatrix`,
  which packages local-source membership and the source-readback residual-factor
  matrix identity from supplied `hdet`, `hedge`, and `hdataFactor` hypotheses.
  This is a consumer-shaped bridge for fixed-base work; it does not prove the
  edge-matrix realization hypothesis `hedge`, endpoint transport of
  `edgeMatrix` or `sourceReadback`, source-prior pushforward, Jacobian density
  comparison, normal crossings, pole order, or RLCT.
- **Current status addendum, retained-passive endpoint transport,
  2026-06-28.** Lean now exposes
  `ChartLocalSuffixState.residualFactorProduct_endpointTransport`,
  `RetainedPassiveNonredundantCoordinateData.endpointTransport`,
  `RetainedPassiveNonredundantCoordinateData.endpointTransport_detChart`,
  `RetainedPassiveNonredundantCoordinateData.residualFactorProduct_C_endpointTransport`,
  `case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_detChart`,
  and
  `case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix`.
  These prove endpoint reindexing of explicit residual-factor products and
  the stored `C` product of retained-passive data, including the explicit Case
  2 selected-entry datum.  This supplies a finite `hdataFactor` transport
  ingredient for fixed-base work, but it does not transport `edgeMatrix`,
  `sourceRecursiveDetChart`, `sourceReadback`, or suffix-recursion states, and
  it does not prove fixed-base local-source membership, source-prior
  pushforward, chart-image membership, Jacobian density comparison, coverage,
  normal crossings, pole order, or RLCT.
- **Current status addendum, source-readback center-matrix handoff,
  2026-06-28.** Lean now exposes
  `case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix`,
  which rewrites the explicit Case 2 source family's actual source-readback
  residual-factor product into the selected-entry center-coordinate matrix
  shape expected by local-measure `hfactor` consumers.  This is not itself a
  local-measure theorem and does not prove source-prior pushforward, chart-image
  membership, Jacobian density comparison, arbitrary retained-passive coverage,
  source-rank coverage, normal crossings, pole order, or RLCT.
- **Current status addendum, source-readback square-sum prehandoff,
  2026-06-28.** Lean now exposes
  `aoyagiCoordinateSquareSum_case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryCenter_residual`,
  which reads the explicit source-readback center-matrix product through
  `AoyagiResidualBlockCoordinateIndex.value`, reindexes the square-sum, and
  identifies it with the selected-entry center residual.  This is still only a
  finite pre-handoff readout; it does not identify the source family with a
  fixed-base p.13 source chart and does not prove a finite-integral theorem.
- **Current status addendum, retained-passive datum center-matrix handoff,
  2026-06-28.** Lean now exposes
  `case2PostPivotSelectedEntryRetainedPassiveData_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix`,
  the stored-`C` datum-level version of the selected-entry center-coordinate
  matrix equality.  This removes only the source-readback wrapper from the
  previous handoff.  The fixed-base local-source frontier is endpoint transport:
  the explicit Case 2 datum is indexed by `case2PostPivotTwoEdgeDomain`, while
  fixed-base retained-passive sockets use `throughSubspaceEndpointComplementIndex`.
  This is not a local-source theorem and does not prove source-prior pushforward,
  chart-image membership, Jacobian density comparison, coverage, normal
  crossings, pole order, or RLCT.
- **Current status addendum, explicit selected-entry source-family regularity,
  2026-06-28.** The constructed Case 2 selected-entry-to-source family now has
  finite-coordinate regularity.  Lean proves continuity of the successor
  selected-entry matrix, continuity of the constructed retained-passive datum
  and its determinant-chart subtype map, and continuity/measurability of
  `case2PostPivotSelectedEntrySourceEdgeFamily`.  This uses only finite product
  topology, selected-entry chart-map continuity, submatrix continuity, and the
  existing retained-passive determinant-chart `edgeMatrix` continuity theorem.
  Reproduction:
  `threads/03-block-product-reduction/reproduction-a2-case2-explicit-selected-entry-source-family-regularity.md`.
  It still does not prove source-prior pushforward, Jacobian density
  comparison, arbitrary retained-passive coverage, source-rank coverage,
  normal crossings, pole order, or RLCT.
- **Current status addendum, explicit selected-entry source chart, 2026-06-28.**
  The constructed Case 2 source-production lane now has an explicit parametric
  source-family map.  Lean defines the old residual as a zero-extension of the
  successor selected-entry matrix reindexed by `eNext.symm`, defines the free
  `Cprime` from the reindexed identity `(1).submatrix id eNext`, packages these
  as `case2PostPivotRetainedPassiveData`, and takes `edgeMatrix`.  The resulting
  source family lies in `sourceRecursiveDetChart`, and its actual
  `sourceReadback` residual-factor product equals the successor selected-entry
  matrix for all `yNext`.  Nonzeroness is a separate corollary from the
  displayed successor pivot coordinate being nonzero.  This removes the
  `Classical.choose`/existential-map obstruction for this constructed Case 2
  lane, but it still does not prove continuity/measurability, Jacobian or
  source-prior pushforward, arbitrary retained-passive coverage, source-rank
  coverage, normal crossings, pole order, or RLCT.
- **Current status addendum, 2026-06-28.** The old target-normaliser
  determinant frontier has been surpassed.  Lean now has the retained-passive
  full target normaliser/determinant bridge, formal/product-density
  change-of-variables, canonical local-source COV, canonical product-density
  residual and finite-integral handoffs, source-side residual positive-set
  measurability for the canonical identity source, the canonical raw-order
  source-map image theorem onto the fixed-base retained-passive source
  edge-family set, the matching raw-order source-chart homeomorphism/local
  inverse package, and the canonical chart-side residual readout as both
  `residualProduct (topologyTupleEdgeMatrix z)` and
  `residualFactorProduct (ofTopologyTuple z).C`.  The selected-entry finite
  coordinate model also now proves residual a.e. positivity and finite
  negative-power integrability under its own formal pivot-Jacobian source
  density, with integrability condition
  `2 * t < ((center.erase pivot.1).card : ℝ) + 1`, and this result has now
  been pushed forward to Lebesgue measure restricted to the selected-entry
  target chart image.  The current A2 frontier is not another selected-entry
  retained-passive wrapper, but a genuine source-production/pushforward bridge
  from retained-passive determinant-chart coordinates to selected-entry
  signed-box coordinates, or an equivalent retained-passive chart-side
  monomial/normal-crossing construction.  Original source-prior/density
  transport remains separate if that route is used.  This addendum supersedes
  older "positive-tail F3 open", "not full target normalisation", and
  "construction of target equivalence remains separate" phrases retained below
  as historical detail.
- **Current status addendum, raw-order pushforward, 2026-06-28.** The public
  raw-order source chart now has source-measure support and product-density
  pushforward theorems to the fixed-base retained-passive source edge-family
  set.  This removes a hidden-let presentation gap in the canonical
  local-source measure route, but it is still reduced fixed-base
  retained-passive measure plumbing.  It does not prove original source-prior
  transport, full source-rank coverage, retained-passive-to-selected-entry
  signed-box density identification, residual positivity/integrability,
  normal crossings, pole order, or RLCT.
- **Current status addendum, source-readout frontier, 2026-06-28.** A
  post-interruption controller/source audit recorded in
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-to-selected-entry-fixed-pivot-boundary.md`
  confirms that Aoyagi pp. 10-13 and pp. 19-22 support the retained-passive
  signs, the p.13 literal product-difference block, the Case 2 fixed-pivot
  chart algebra, and the two-edge factor order.  They do not prove fixed-pivot
  nonzero coverage or factor alignment for an actual `sourceReadback` point.
  Therefore the next source-moving target is to prove the displayed
  post-pivot/following-factor identities for actual retained-passive readback
  data and prove pivot provenance or an all-pivot cover; a wrapper retaining
  `hD`, `hF`, and `hpivot` is not formalisation progress.
- **Current status addendum, raw-order source-chart composition, 2026-06-28.**
  Lean now exposes the direct determinant-chart source presentation
  `paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_eq_sourceEdgeFamilyOfData`.
  It proves that the public raw-order source chart after
  `topologyTupleEdgeRawOrder` is the direct fixed-base source family attached
  to `ofTopologyTuple z`, for `z ∈ topologyTupleDetChartSet`.  This is useful
  source-map bookkeeping, but it does not discharge the active selected-entry
  fields: factor alignment for actual `sourceReadback` data, pivot
  provenance/all-pivot coverage, original source-rank coverage, measure/prior
  transport, normal crossings, pole order, and RLCT remain open.
- **Current status addendum, selected-entry all-pivot coverage, 2026-06-28.**
  Lean now proves finite all-pivot selected-entry inverse lemmas
  `SelectedEntrySignedBox.CenterCoord.exists_pivot_chartMap_eq_value_of_ne_zero`
  and
  `SelectedEntrySignedBox.CenterCoord.exists_pivot_matrix_eq_chartMap_of_ne_zero`.
  These remove the fixed-pivot choice once a nonzero center vector or nonzero
  residual matrix is known.  They do not prove retained-passive source/readback
  nonzero production, factor alignment for the displayed post-pivot and
  following factors, original source-rank coverage, measure/prior transport,
  normal crossings, pole order, or RLCT.
- **Current status addendum, retained-passive Case 2 all-pivot adapter,
  2026-06-28.** Lean now lifts the finite all-pivot selected-entry inverse into
  the retained-passive Case 2 two-edge bridges:
  `exists_pivot_residualFactorProduct_retainedPassiveCoordinateData_eq_selectedEntryCenter_matrix_of_case2PostPivot_of_ne_zero`,
  `exists_pivot_residualFactorProduct_ofTopologyTuple_eq_selectedEntryCenter_matrix_of_case2PostPivot_of_ne_zero`,
  and
  `exists_pivot_aoyagiCoordinateSquareSum_retainedPassiveP13Canonical_chart_eq_selectedEntryCenter_residual_of_case2PostPivot_of_ne_zero`.
  These replace a supplied fixed pivot/nonzero pivot entry by the single
  hypothesis that the displayed post-pivot product matrix is nonzero.  They do
  not prove that nonzeroness, actual retained-passive factor alignment,
  source/prior transport, normal crossings, pole order, or RLCT.
- **Current status addendum, constructed Case 2 displayed-product
  nonzeroness, 2026-06-28.** Lean now proves a constructed finite-data source
  production theorem:
  `exists_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero`
  and its concrete two-edge residual-factor-family form
  `exists_residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero`.
  From a successor selected-entry coordinate vector with nonzero displayed
  successor pivot coordinate, the theorem constructs residual data and free
  `Cprime` so the displayed post-pivot product is exactly the successor
  selected-entry matrix and hence nonzero.  Reproduction:
  `threads/03-block-product-reduction/reproduction-a2-case2-displayed-product-nonzero-source-production.md`.
  This removes nonzeroness only for constructed displayed data; it does not
  prove arbitrary retained-passive `sourceReadback` factor alignment or
  nonzeroness, source/prior transport, normal crossings, pole order, or RLCT.
- **Current status addendum, constructed Case 2 source-readback production,
  2026-06-28.** Lean now proves
  `exists_sourceRecursiveEdgeFamily_case2PostPivot_sourceReadback_residualFactorProduct_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero`.
  From successor selected-entry coordinates with nonzero displayed successor
  pivot coordinate, the theorem constructs a two-edge source family `E` in the
  source-recursive determinant chart such that the actual `sourceReadback E`
  residual-factor product is the successor selected-entry matrix and is
  nonzero.  This is constructed source production only; it does not prove
  arbitrary retained-passive `sourceReadback E` factor alignment,
  source/prior transport, normal crossings, pole order, or RLCT.
- **Historical status.** partial algebraic Lean artifacts landed and reviewed: the
  post-`Ctop` terminal `F3` zero-tail (`M = 0`) stage is now packaged as a
  determinant-one raw-tuple shear fixing all fields except `F3`, with composed
  zero-tail `F3` component agreement against the formal raw-order Jacobian;
  the positive-tail `F3` bridge remains open and needs a post-`Ctop`
  `dEarly_postC` linear-map package.  The
  edge-pair, post-edge-pair passive `A1`, and post-`A1passive` `Ctop` stages
  are now composed in Lean through the `Ctop` component, with absolute
  determinant one and actual-derivative agreement for `Ctop` against the formal
  raw-order Jacobian; xhigh `Popper the 2nd` review passed.  This is not
  full target normalisation: `F3` agreement remains open, so it is not a full
  tuple equality or actual raw-order determinant equality.  The earlier
  edge-pair and post-edge-pair passive `A1` shears are composed in Lean, with
  absolute determinant one and componentwise actual-derivative agreement for
  `A1passive`, `(F2,C)`, and `A3passive` against the formal raw-order
  Jacobian; xhigh `Pasteur the 2nd` review passed.  The post-edge-pair
  passive `A1` branch now has a
  raw-tuple linear equivalence
  fixing `(F2,A3passive,C,Ctop,F3)`, changing only `A1passive`, and proving
  determinant one/absolute determinant one by the product-shear calculation on
  `A1passive × rest`.  Its correction reads the successor `F2` family from
  `(retainedPassiveFormalRawF2CLinearEquivAt hz).symm (w.F2,w.C)`, the
  already-normalised post-edge-pair pair, rather than from the pre-edge-pair
  target recovery recurrence.  This is not yet the composed target normalizer
  or actual raw-order determinant equality.  The target edge-pair branch now
  has a full raw-tuple linear equivalence fixing
  `A1passive`, `A3passive`, `Ctop`, and `F3`, replacing only `(F2,C)` by the
  target edge-pair shear, and using only the formal inverse's first component
  as recovered `X` in the inverse map.  The same full raw-tuple equivalence
  now has determinant one and absolute determinant one, proved by conjugating
  the inverse map to edge-block coordinates and applying a successor-triangular
  determinant calculation.  This determinant result is not a determinant-one
  theorem for the formal separated `(F2,C)` equivalence and not determinant
  equality for the actual raw-order Frechet derivative; xhigh review by
  `Lorentz the 2nd` passed.  The target-side all-edge
  `(F2,C)` branch also has a linear-map package:
  the backward target-recovered `F2` recurrence, its successor family, and
  `retainedPassiveTargetEdgePairShearAt z w` are all packaged as `LinearMap`s
  in the target raw tuple, with terminal zero, nonterminal `Fin.succ_castSucc`
  cast, and the `Xsucc * coord.C q` term preserved; this is only a component
  linear map, not an equivalence, normalizer, or determinant theorem.  Generic
  determinant infrastructure now has abs-det-one wrappers for product
  congruences, lower refl/refl skew shears, and upper shears; these wrappers
  support a future target-side normalizer but do not construct it.  The
  positive-tail terminal `F3` bridge now has a target-only `dEarly` wrapper,
  replacing the source-staged recursive early lower-left derivative by
  `retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt (M := M) ... 0`
  on actual raw-order derivative targets, while preserving the terminal
  `dLast#` factor and the order `- dEarly * solvedA1(last)`; the
  retained-passive lower-left derivative frontier now has a full recursive
  target-only derivative for the zeroed-final lower-left tail.  It target-stages
  the current solved-`A1`, stored-`C`/`Cnext`, solved-`A1` suffix `dPsucc`
  beginning at `p.succ.val`, and successor lower-left terms, proves equality
  with the existing source-staged recursion on actual raw-order derivative
  targets, and proves the resulting Frechet derivative formula.  The same layer
  also has a solved-`A1` suffix derivative API covering the terminal solved
  factor and a positive-suffix algebra lemma relating solved suffixes to passive
  seed suffixes when `1 <= m`; the
  retained-passive lower-left derivative frontier also has a target-only
  stored-`C` suffix derivative and positive-tail `Cnext` specialization, plus
  a wrapper that feeds this staged `dCnext` into the one-step lower-left target
  core while still keeping `dAcur`, `dPsucc`, and `dNext` explicit; the
  retained-passive frontier also has a target-only recovered-`Ctop` helper,
  current solved-`A1` helper, and one-step lower-left target core replacing
  current source `C` and passive lower-left source reads by target-side
  readouts; these target-only step cores are proved equal to the existing
  source step core on actual raw-order derivative targets.  The
  retained-passive lower-left derivative recurrence also has a named
  one-step helper and generic/zero/successor branch wrappers through that
  helper, with the successor current tangent explicitly `v.1 s.castSucc`;
  the retained-passive zeroed-final lower-left tail now also has a
  Nat-recursive target-staged expression/unfold API, and that recursive
  expression is now proved equal to the actual Frechet derivative under the
  determinant-chart hypothesis; the positive-tail `F3` bridge now consumes
  that recursive expression at index `0` and has a matching source-`F3`
  recovery theorem;
  the target-normalizer frontier now has a target-recovered source `(F2,C)`
  pair and source-`C` projection, recovering `(v.F2,v.C)` and `v.C(q)` on
  actual raw-order derivative targets, plus a general product-linear-equivalence
  determinant helper;
  the passive top-left `A1` suffix now has a target-only Nat recursion, the
  actual Frechet derivative of every seed-product suffix is proved to agree
  with that recursion on raw-order derivative targets, and the first value is
  plugged into the first top-left `Ctop` branch with source-`Ctop` recovery;
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
  p. 13 coordinate package is now connected to the deterministic suffix-state
  step: the actual recursive `suffixState` supplies the lower-unitriangular
  left witness existentially, and the one-step wrappers produce the next
  triangular product and signed product-difference identities for
  `P p.castSucc j`. The
  matrix-entry-ideal consequence of that product-difference matrix is now also
  packaged at the fixed-base/source-rank boundary: determinant-unit triangular
  multiplication transports the entry ideal of `T - T0` to the cleaned
  four-block ideal generated by entries of `Ctop - 1`, `F2`, `F3`, and the
  deterministic residual product. The regular block-entry count from `C1 -
  Er`, `F2`, and `F3` is also proved to give the displayed regular term after
  dividing by two, and is connected to the finite `jacobianPriorLossShift`
  socket without asserting analytic additivity. The endpoint rank-width bounds
  needed by that finite shift are now derived from source-rank-stratum
  membership and the explicit dimension convention when `L=N`; the reduced
  certificate and its minimum/order facts remain supplied. The one-step
  determinant-chart coordinate change is now proved to be a homeomorphism
  between the raw and chart determinant domains; its record-level formal
  inverse laws are also available under the weaker hypothesis
  `IsUnit A1.det`, with determinant-chart inverse theorems retained as
  wrappers. The p. 13 source
  regular-suspension boundary is now pinned: the lower-right literal block is
  `prod_s C^(s)-F3F2`, the residual block is `prod_s C^(s)`, and the displayed
  RLCT shift remains an unproved analytic regular-suspension assertion. Lean
  now also packages the source-data constructor with the source-stratum
  factor-`2` comparison between the literal and cleaned p. 13 finite
  square-sums. The supplied regular-suspension extraction projection now also
  exposes that extraction on `Cfull` gives the reduced finite minimum plus the
  regular count shift and the reduced finite order. The source-stratum
  literal p.13 square-sum is now also compared directly with
  regular-block square-sum plus residual-block square-sum, including the
  half lower-bound form and a supplied ambient-loss handoff.  The signed-box
  comparison layer now also has a generic model-loss adapter, dividing the
  monomial lower-bound constant by a positive model/actual comparison
  constant. The regular-square product-measure layer now also has a
  bounded-density wrapper consuming supplied `loss >= c*(residualSquareSum +
  regularNormSq)` and `0 <= density <= C` hypotheses. It now also has a
  p.13 fixed-base regular-coordinate adapter that rewrites the Euclidean
  regular-coordinate fiber dimension as `aoyagiTheorem2RegularVariableCount`
  and states the lower-loss hypothesis using the p.13 regular coordinate
  square-sum. A generic local measure handoff now also turns
  `nhdsWithin` facts into a.e. facts after restricting a measure to a smaller
  measurable source neighborhood, with a first-projection product version. The
  explicit p.13 product-coordinate family is also now proved to preserve
  source-rank-stratum membership locally in small regular coordinates, under
  the base product-reduction certificate and determinant-unit condition. The
  raw-order inverse-density pushforward is now consumed conditionally for the
  actual p.13 left-step raw tuple under an explicit source/product-chart raw
  pushforward hypothesis, with raw chart null-measurability and raw-order
  a.e.-measurability derived internally; the needed `Ctop` determinant-unit
  a.e. fact is derived internally from raw-chart support. The raw p.13 section
  facts `C1 = I` and `A3 = 0` are formalized as guardrails against treating
  the section as a full raw-Haar chart. A page-pinned p.13 source-boundary
  audit now confirms that pp. 5-14 do not state the raw source pushforward,
  and the positive-rank section obstruction prevents deriving full raw-Haar
  pushforward from the p.13 section alone. The full source Theorem 3/RLCT
  claim remains blocked on the analytic product-coordinate regular-square
  suspension theorem and the actual p.13 chart/density construction.  Latest
  retained-passive derivative/Jacobian slice: the positive-tail `F3` bridge now
  uses the recursive target-staged lower-left derivative as its `dEarly` term,
  replacing the previous finite-unroll frontier while keeping the older
  finite-unroll theorems as compatibility lemmas.  The first top-left `Ctop`
  branch now uses the full recursive target-staged passive top-left
  `A1` suffix derivative as its `dTail` term, replacing the previous finite
  one/two-step `Ctop` suffix expansions while keeping them as compatibility
  lemmas.  Lean proves the recursive `Ctop` consumer and `Ctop` recovery
  companion in `RetainedPassiveCoordinatesJacobian.lean`, preserving the order
  `Tail⁻¹ * dTail * Tail⁻¹ * coord.Ctop`.  Latest determinant/Jacobian
  assembly slice: Lean now proves
  a conditional bridge from a supplied determinant-one target-side
  `LinearEquiv` identifying the actual raw-order Frechet derivative with the
  point-specialized formal raw-order Jacobian to equality of the actual
  forward absolute Jacobian determinant and the formal product determinant.
  This packages the determinant consequence of such a target normalizer; it
  does not construct the normalizer, prove source-prior transport, or prove
  normal crossings, pole order, or RLCT.
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
  `threads/03-block-product-reduction/reproduction-a2-regular-variable-count.md`;
  regular-variable source-rank shift at
  `threads/03-block-product-reduction/reproduction-a2-regular-variable-source-rank-shift.md`;
  regular-variable rank-width shift at
  `threads/03-block-product-reduction/reproduction-a2-regular-variable-rank-width-shift.md`;
  canonical product-difference regular-chart source at
  `threads/03-block-product-reduction/reproduction-a2-canonical-product-difference-regular-chart-source.md`;
  regular-suspension coordinate index at
  `threads/03-block-product-reduction/reproduction-a2-regular-suspension-coordinate-index.md`;
  product-difference coordinate source data at
  `threads/03-block-product-reduction/reproduction-a2-product-difference-coordinate-source-data.md`;
  one-step determinant-chart coordinate equivalence at
  `threads/03-block-product-reduction/reproduction-a2-one-step-determinant-chart-coordinate-equivalence.md`;
  p. 13 source regular-suspension boundary at
  `threads/03-block-product-reduction/reproduction-a2-p13-source-regular-suspension-boundary.md`;
  supplied regular-suspension extraction projection at
  `threads/03-block-product-reduction/reproduction-a2-supplied-regular-suspension-extraction-projection.md`;
  source-stratum literal regular/residual square-sum comparison at
  `threads/03-block-product-reduction/reproduction-a2-source-stratum-literal-regular-residual-square-sum.md`;
  p.13 half loss lower bound at
  `threads/03-block-product-reduction/reproduction-a2-p13-half-loss-lower-bound.md`;
  signed-box model-loss adapter at
  `threads/03-block-product-reduction/reproduction-a2-signed-box-model-loss-adapter.md`;
  regular-square bounded-density wrapper at
  `threads/03-block-product-reduction/reproduction-a2-regular-square-bounded-density-wrapper.md`;
  regular square-suspension integrability target at
  `threads/03-block-product-reduction/reproduction-a2-regular-square-suspension-integrability-target.md`;
  one-sided regular-suspension integrability brick at
  `threads/03-block-product-reduction/reproduction-a2-one-sided-regular-suspension-integrability.md`;
  radial finite-side integrability brick at
  `threads/03-block-product-reduction/reproduction-a2-radial-finite-side-integrability.md`;
  null-origin radial integrability transfer at
  `threads/03-block-product-reduction/reproduction-a2-null-origin-radial-integrability.md`;
  product below-critical integrability at
  `threads/03-block-product-reduction/reproduction-a2-product-below-critical-integrability.md`;
  selected-entry chart-image characterization at
  `threads/03-block-product-reduction/reproduction-a2-selected-entry-chart-image-characterization.md`;
  selected-entry residual-product square-sum at
  `threads/03-block-product-reduction/reproduction-a2-selected-entry-residual-product-square-sum.md`;
  selected-entry finite sector cover at
  `threads/03-block-product-reduction/reproduction-a2-selected-entry-finite-sector-cover.md`;
  product-coordinate source-rank membership at
  `threads/03-block-product-reduction/reproduction-a2-product-coordinate-source-rank-membership.md`;
  source-stratum local-subset local-source finite-integral consumer at
  `threads/03-block-product-reduction/reproduction-a2-source-stratum-local-subset-local-source-finite-integral-consumer.md`;
  selected-entry residual-factor readout boundary at
  `threads/03-block-product-reduction/reproduction-a2-selected-entry-residual-factor-readout-boundary.md`;
  p.13 left-step conditional raw pushforward consumer at
  `threads/03-block-product-reduction/reproduction-a2-p13-left-step-conditional-raw-pushforward-consumer.md`;
  p.13 raw pushforward source-boundary audit at
  `threads/03-block-product-reduction/source-audit-a2-p13-left-step-raw-pushforward-boundary.md`;
  retained-passive first passive `A1` target staging at
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-a1-tail-target-staged-first-passive.md`;
  retained-passive two-positive-tail second passive `A1` target staging at
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-ctop-two-positive-tail-second-a1-target-staging.md`;
  retained-passive recursive passive top-left `A1` suffix and `Ctop` plug-in
  at
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-recursive-target-staged-a1-tail.md`;
  retained-passive recursive lower-left and positive-tail `F3` plug-in design
  at
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-recursive-target-staged-lower-left-tail.md`;
  retained-passive conditional determinant/Jacobian bridge at
  `threads/03-block-product-reduction/reproduction-a2-retained-passive-conditional-determinant-jacobian-bridge.md`.
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
  conditional determinant/Jacobian bridge reviewed by xhigh `Noether the 2nd`
  in
  `threads/03-block-product-reduction/review-a2-retained-passive-conditional-determinant-jacobian-bridge.md`;
  retained-passive positive-tail `F3` recursive `dEarly` plug-in reviewed by
  xhigh `Franklin the 2nd` in
  `threads/03-block-product-reduction/review-a2-retained-passive-f3-recursive-dearly-plugin.md`;
  retained-passive recursive passive top-left `A1` suffix and `Ctop` plug-in
  reviewed by xhigh `Dirac the 2nd` in
  `threads/03-block-product-reduction/review-a2-retained-passive-recursive-a1-tail-ctop-plugin.md`;
  local source-rank endpoint package reviewed in
  `threads/03-block-product-reduction/review-a2-local-source-rank-endpoint-package.md`;
  block product-difference algebra independently checked by xhigh
  pen-and-paper scout `Lorentz` and accepted by xhigh fidelity/scope reviewer
  `Fermat` in
  `threads/03-block-product-reduction/review-a2-block-product-difference-algebra.md`;
  product-difference entry-ideal boundary reviewed by xhigh `Dewey` in
  `threads/03-block-product-reduction/review-a2-product-difference-entry-ideal-boundary.md`;
  regular-variable count and finite-shift bridge reviewed by xhigh `Franklin`
  in `threads/03-block-product-reduction/review-a2-regular-variable-count.md`;
  regular-variable source-rank shift checked by xhigh `Helmholtz the 2nd` in
  `threads/03-block-product-reduction/review-a2-regular-variable-source-rank-shift.md`;
  regular-variable rank-width shift checked by xhigh `Ramanujan the 3rd` in
  `threads/03-block-product-reduction/review-a2-regular-variable-rank-width-shift.md`;
  product-difference coordinate source-data checked by xhigh
  `Descartes the 3rd` in
  `threads/03-block-product-reduction/review-a2-product-difference-coordinate-source-data.md`
  after a source-anchor wording repair; one-step determinant-chart coordinate
  equivalence reviewed by xhigh `Herschel the 4th` in
  `threads/03-block-product-reduction/review-a2-one-step-determinant-chart-coordinate-equivalence.md`;
  p. 13 source regular-suspension boundary reviewed by xhigh `Gibbs the 4th`
  in
  `threads/03-block-product-reduction/review-a2-p13-source-regular-suspension-boundary.md`;
  supplied regular-suspension extraction projection and source-stratum literal
  regular/residual square-sum comparison reviewed by xhigh `Tesla the 4th` in
  `threads/03-block-product-reduction/review-a2-regular-suspension-projections-and-loss-shape.md`;
  one-sided regular-suspension integrability brick reviewed by xhigh
  `Copernicus the 4th` in
  `threads/03-block-product-reduction/review-a2-one-sided-regular-suspension-integrability.md`;
  radial finite-side integrability brick reviewed by xhigh `Volta the 4th` in
  `threads/03-block-product-reduction/review-a2-radial-finite-side-integrability.md`;
  null-origin radial integrability transfer reviewed by xhigh `Jason the 4th` in
  `threads/03-block-product-reduction/review-a2-null-origin-radial-integrability.md`;
  product below-critical integrability reviewed by xhigh `Hypatia the 4th` in
  `threads/03-block-product-reduction/review-a2-product-below-critical-integrability.md`;
  p.13 half lower bound and signed-box model-loss adapter reviewed by xhigh
  `Hume the 4th` in
  `threads/03-block-product-reduction/review-a2-p13-half-and-signed-box-model-adapter.md`;
  regular-square bounded-density wrapper reviewed by xhigh `Mendel the 4th`
  in
  `threads/03-block-product-reduction/review-a2-regular-square-bounded-density-wrapper.md`;
  selected-entry chart-image characterization reviewed by xhigh `Halley` in
  `threads/03-block-product-reduction/review-a2-selected-entry-chart-image-characterization.md`;
  selected-entry residual-product square-sum reviewed by xhigh `Hooke` in
  `threads/03-block-product-reduction/review-a2-selected-entry-residual-product-square-sum.md`;
  selected-entry finite sector cover reviewed by xhigh `Bacon` in
  `threads/03-block-product-reduction/review-a2-selected-entry-finite-sector-cover.md`;
  product-coordinate source-rank membership reviewed by xhigh check-ins
  `Bernoulli`, `Banach`, and `Confucius` in
  `threads/03-block-product-reduction/review-a2-product-coordinate-source-rank-membership.md`;
  source-stratum local-subset local-source consumer reviewed by xhigh scouts
  `Bohr the 2nd`, `Dirac the 2nd`, and `Heisenberg the 2nd` in
  `threads/03-block-product-reduction/review-a2-source-stratum-local-subset-local-source-finite-integral-consumer.md`;
  selected-entry residual-factor readout boundary reviewed by xhigh source/API
  scouts `Kant` and `Kuhn` in
  `threads/03-block-product-reduction/review-a2-selected-entry-residual-factor-readout-boundary.md`;
  p.13 left-step conditional raw pushforward consumer reviewed by xhigh
  `Ampere the 2nd` in
  `threads/03-block-product-reduction/review-a2-p13-left-step-conditional-raw-pushforward-consumer.md`;
  p.13 raw pushforward boundary rechecked by xhigh source, Lean-boundary, and
  pen-and-paper scouts on 2026-06-26, recorded in
  `threads/03-block-product-reduction/source-audit-a2-p13-left-step-raw-pushforward-boundary.md`;
  retained-passive first passive `A1` target staging reviewed by xhigh
  `Banach the 2nd` in
  `threads/03-block-product-reduction/review-a2-retained-passive-a1-tail-target-staged-first-passive.md`;
  retained-passive two-positive-tail second passive `A1` target staging
  reviewed by xhigh `Schrodinger the 2nd` in
  `threads/03-block-product-reduction/review-a2-retained-passive-ctop-two-positive-tail-second-a1-target-staging.md`.
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
  `lean/DLNFibre/DLN/Aoyagi/RegularVariableShift.lean`, including
  source-rank-stratum endpoint bounds and source-rank finite-shift constructors;
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
  chart-certificate projections, and supplied finite-formula hypotheses. Also
  proved the source-side wrapper
  `exists_paperEndpointFixedBaseRegularCoordinateSourceData_literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two_nhdsWithin_source_of_rank_eq`,
  which chooses fixed-base regular-coordinate source data from real rank/source
  hypotheses and returns the existing `nhdsWithin` source-rank factor-`2`
  comparison between the literal and cleaned p. 13 finite square-sums. Also
  proved supplied full-certificate extraction projections
  `AoyagiSuppliedRegularSuspensionCertificate.lambda_eq_reduced_add_half_regularCount`,
  `...poleOrder_eq_reduced_exponentOrder`,
  `...lambda_eq_reduced_add_regularTerm`, and
  `...lambda_and_poleOrder_eq_reduced_add_regularTerm`. Also proved
  `PaperEndpointFixedBaseRegularCoordinateSourceData.literal_regular_add_residual_squareSum_eventually_factor_two_nhdsWithin_source`,
  which rewrites the source-stratum literal/cleaned factor-`2` comparison as a
  comparison with the regular-block square-sum plus residual-block square-sum.
  Also proved
  `PaperEndpointFixedBaseRegularCoordinateSourceData.literal_regular_add_residual_squareSum_eventually_half_le_nhdsWithin_source`,
  `PaperEndpointFixedBaseRegularCoordinateSourceData.const_mul_literal_squareSum_eventually_le_loss_to_half_regular_add_residual_squareSum_nhdsWithin_source`,
  and
  `exists_paperEndpointFixedBaseRegularCoordinateSourceData_literal_regular_add_residual_squareSum_eventually_half_le_nhdsWithin_source_of_rank_eq`,
  which package the lower-bound half of the same finite comparison and a
  supplied ambient-loss handoff. In `MonomialChartIntegrability.lean`, also
  proved
  `lintegral_ofReal_loss_rpow_neg_mul_density_signedBox_lt_top_of_modelLoss_le_const_mul_loss`,
  the signed-box model-loss adapter from `modelLoss <= K*loss` with `K>0`.
  Also proved
  `lintegral_ofReal_loss_rpow_neg_mul_density_coordinateSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_residual_power_lt_top`
  and
  `lintegral_ofReal_loss_rpow_neg_mul_density_residualBlockSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_residual_power_lt_top`,
  the bounded-density regular-square finite-side wrappers. Also proved
  `PaperEndpointFixedBaseRegularCoordinateSourceData.regularCoordinateEuclidean_finrank_eq_regularVariableCount`
  and
  `PaperEndpointFixedBaseRegularCoordinateSourceData.lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residual_power_lt_top`,
  the p.13 fixed-base regular-coordinate finite-side adapter, reviewed by
  xhigh `Pasteur the 4th` at
  `threads/03-block-product-reduction/review-a2-p13-regular-coordinate-bounded-density-adapter.md`.
  Also proved `exists_open_ae_restrict_inter_of_eventually_nhdsWithin` and
  `exists_open_ae_restrict_inter_prod_fst_of_eventually_nhdsWithin` in
  `LocalMeasureHandoff.lean`, the generic local filter-to-restricted-measure
  handoff, reviewed by xhigh `Carver the 4th` at
  `threads/03-block-product-reduction/review-a2-local-measure-handoff.md`.
  Also proved the fixed-base p.13 regular-suspension local-measure wrappers
  in `RegularSuspensionLocalMeasure.lean`, turning the half lower bound and a
  supplied base-loss lower bound into restricted-source and first-projection
  product a.e. facts, and turning supplied uniform-in-fiber source-filter
  loss/density bounds into product-measure a.e. hypotheses, with
  source-stratum measurability still supplied;
  reviewed by xhigh `McClintock the 5th` at
  `threads/03-block-product-reduction/review-a2-regular-suspension-local-measure.md`
  and xhigh `Boyle the 5th` at
  `threads/03-block-product-reduction/review-a2-regular-suspension-uniform-product-handoff.md`.
  Also proved
  `aemeasurable_productReductionStepTopologyTupleToChartRawOrder_restrict_detChart`,
  `ae_mem_productReductionStepRawDetChartSet_of_map_eq_restrict`,
  `paperEndpointFixedBaseP13RawPreimageTuple_C1_eq_one`,
  `paperEndpointFixedBaseP13RawPreimageTuple_A3_eq_zero`,
  `p13ProductCoordinateLeftStepRawTopologyTuple_C1_eq_one`,
  `p13ProductCoordinateLeftStepRawTopologyTuple_A3_eq_zero`,
  `ae_isUnit_ctopMatrix_det_of_p13RawPreimage_map_eq_restrict_rawDetChart`,
  `ae_isUnit_ctopMatrix_det_of_p13LeftStepRaw_map_eq_restrict_rawDetChart`,
  `map_productReductionStepRawOrder_comp_eq_withDensity_inverseJacobian`,
  `p13ProductCoordinateLeftStepRawTopologyTuple`,
  `map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_rawPreimage_map`,
  and
  `map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map`,
  the conditional p.13 left-step raw pushforward consumer.  It keeps the raw
  source pushforward as an explicit hypothesis and places the inverse-Jacobian
  density on the restricted raw target measure; `Ctop` unit a.e. is now
  derived from the supplied raw-chart pushforward.
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
- **Tier.** Established in Aoyagi; avoided in the current Lean theorem scope.
- **Status.** avoided for current local/conditional final sockets.  Xhigh
  scouts `Boole` and `Dirac the 3rd` found that Aoyagi Theorem 4 is analytic
  background cited to another Aoyagi paper, while the current final sockets
  are already local/conditional on supplied source data and supplied
  normal-crossing certificates.  The theorem reopens only for a future result
  that claims a global arbitrary-base-point RLCT statement or proves that a
  source-produced certificate attains the global DLN RLCT.
- **Kill-condition.** Any theorem tries to pass from arbitrary source/base
  points to the deepest-point certificate, or uses lower semicontinuity/global
  analytic comparison, without expanding the citation boundary.
- **Evidence/source.** Aoyagi Theorem 4, PDF p. 14.
- **Pen-and-paper reproduction.** source scout report at
  `threads/02-analytic-interface/scout-report.md`; avoidance audit by xhigh
  `Dirac the 3rd` recorded in this claim and the A6 boundary map.
- **Reproduction check.** xhigh `Dirac the 3rd` checked current Lean final
  sockets and found no silent Theorem 4 dependency.
- **Lean target.** none for current supplied local/conditional theorem scope.
- **Proved.** not proved; avoided by theorem statement shape.
- **Assumed.** no Theorem 4 assumption in current Lean final sockets.
- **Cited.** not allowed as a separate Lean citation under current goal.
- **Deferred.** restricted deepest-point proof or operator decision only if a
  future global theorem requires it.
- **Controller caution.** Do not add Aoyagi Theorem 4 as a hidden citation.
  Keep final Lean statements local/conditional unless the operator explicitly
  expands the cited boundary or a restricted deepest-point lemma is proved.

## Claim A4 - blow-up transition certificate

- **Statement.** Aoyagi's recursive Case 1 / Case 2 coordinate substitutions
  transform the reduced ideal into a monomial/diagonal normal-crossing form with
  the exponent vectors stated in the paper.
- **Tier.** New Lean packaging of source-guided finite bookkeeping; the full
  transition proof is not yet established.
- **Current status addendum, recurrence-aware Case 2 branch progress,
  2026-06-30.** Lean now lifts the displayed Case 2 selected-entry
  branch-progress bridge to the recurrence-aware branch state via
  `AoyagiRecurrenceBranchState.case2DisplayedActiveGuard`,
  `selectedEntryCase2DisplayedRecurrencePrefixBoundBranchProgressData`, and
  `selectedEntryCase2DisplayedRecurrenceContinuingBranchProgressData` in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryBranchProgressBridge.lean`.  The
  adapter takes supplied child recurrence data
  `childRecurrence s h : IntroducedLabelRecurrenceState L n s.S (s.J+1) alpha`
  for each continuing branch, chooses
  `sameStageChildWithRecurrence s (childRecurrence s h)` as the continuing
  child, and proves the selected-entry `continuing_child_step` with
  `AoyagiRecurrenceBranchState.sameStageChildWithRecurrence_progress_of_prefixBound`.
  Reproduction and statement card are at
  `threads/04-blow-up-certificate/reproduction-a4-recurrence-case2-branch-progress.md`
  and
  `threads/04-blow-up-certificate/statement-card-a4-recurrence-case2-branch-progress.md`,
  and
  `threads/04-blow-up-certificate/review-a4-recurrence-case2-branch-progress.md`.
  Focused local build, direct warning check, full local build, no-sorry audit,
  whitespace check, and direct axiom probe passed; the new declarations report
  only `[propext, Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer
  `Avicenna` and xhigh Lean/API reviewer `Bernoulli` returned PASS.  This
  constructs no recurrence data, source-production payloads, branch guards,
  terminal payloads, chart construction, analytic atlas fields, normal
  crossings, pole order, or RLCT.
- **Current status addendum, recurrence branch termination data,
  2026-06-30.** Lean now exposes the recurrence-aware progress relation through
  the selected-entry termination socket via
  `selectedEntryRecurrenceBranchTerminationData` in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryBranchProgressBridge.lean`.  The
  adapter consumes a supplied initial recurrence state
  `IntroducedLabelRecurrenceState L n 1 0 alpha`, sets `step` to
  `AoyagiRecurrenceBranchState.progressStep L n alpha`, uses
  `AoyagiRecurrenceBranchState.progressStep_wellFounded`, and sets the initial
  branch state to `(1,0)` with the supplied recurrence data.  Reproduction,
  statement card, and review are at
  `threads/04-blow-up-certificate/reproduction-a4-recurrence-branch-termination-data.md`,
  `threads/04-blow-up-certificate/statement-card-a4-recurrence-branch-termination-data.md`,
  and
  `threads/04-blow-up-certificate/review-a4-recurrence-branch-termination-data.md`.
  Focused local build, direct warning check, full local build, no-sorry audit,
  whitespace check, and direct axiom probe passed; the declaration reports only
  `[propext, Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer
  `Russell` and xhigh Lean/API reviewer `Ohm` returned PASS.  This is only a
  termination-data adapter: it constructs no recurrence data, source-production
  payloads, branch-guard coverage, continuing children, terminal payloads,
  full analytic-atlas branch termination theorem, normal crossings, pole order,
  or RLCT.
- **Current status addendum, combined recurrence branch progress,
  2026-06-30.** Lean now adds the recurrence-aware branch state
  `AoyagiRecurrenceBranchState` in
  `lean/DLNFibre/DLN/Aoyagi/BlowupBranchProgress.lean`.  Its progress measure
  is a weighted natural encoding of
  `(remaining, stageBudget, abovePivotCount)`:
  `(remaining * (L+2) + stageBudget) * (#actualWidthLabelFinset + 1) +
  abovePivotCount`.  Same-stage Case 1(2)/Case 2 moves decrease `remaining`
  by support growth.  Stage handoffs `(S,J) -> (S+1,0)` weakly decrease
  `remaining` by introduced-domain monotonicity and strictly decrease
  `stageBudget`.  Case 1(1) selected-old same-domain lowering keeps the first
  two coordinates fixed and decreases `abovePivotCount`.  Reproduction,
  statement card, and review are at
  `threads/04-blow-up-certificate/reproduction-a4-combined-recurrence-branch-progress.md`,
  `threads/04-blow-up-certificate/statement-card-a4-combined-recurrence-branch-progress.md`,
  and
  `threads/04-blow-up-certificate/review-a4-combined-recurrence-branch-progress.md`.
  Focused local build, direct warning check, full local build, no-sorry audit,
  whitespace check, and direct axiom probe passed; the new declarations report
  only `[propext, Classical.choice, Quot.sound]`.  Xhigh source explorer
  `Einstein` independently recommended this three-coordinate finite measure
  including the stage handoff.  Xhigh source/scope reviewer `Heisenberg` and
  xhigh Lean/API reviewer `Ptolemy` returned PASS.  This is still finite
  branch-progress bookkeeping only: it proves no source-production payloads,
  branch-guard coverage, terminal payloads, full analytic-atlas branch
  termination theorem, normal crossings, pole order, or RLCT.
- **Current status addendum, Case 1(1) same-domain plateau progress,
  2026-06-30.** Lean now adds a separate same-domain finite level-count
  progress kernel for Case 1(1) in
  `lean/DLNFibre/DLN/Aoyagi/BlowupBranchProgress.lean`.  The exact plateau
  data `IntroducedLabelRecurrenceState.levelPlateau` and
  `levelPlateauProgress` count introduced labels at a fixed recurrence level.
  The same-domain measure `abovePivotLevelFinset` and
  `abovePivotLevelProgress` count introduced labels whose recurrence level is
  still above `J`.  The Case 1(1) theorems consume
  `IntroducedLabelRecurrenceState.Case1SelectedOldLevelMoveData` and prove
  that the selected old lowering erases `(s0,k0)` from both the `J+J1` plateau
  and the above-pivot set, hence strictly decreases both finite counts.
  Reproduction, statement card, and review are at
  `threads/04-blow-up-certificate/reproduction-a4-case1-same-domain-plateau-progress.md`,
  `threads/04-blow-up-certificate/statement-card-a4-case1-same-domain-plateau-progress.md`,
  and
  `threads/04-blow-up-certificate/review-a4-case1-same-domain-plateau-progress.md`.
  Focused local build, direct warning check, and direct axiom probe passed; the
  new declarations report only `[propext, Classical.choice, Quot.sound]`.
  Xhigh source/scope reviewer `Boole` and xhigh Lean/API reviewer `Arendt`
  returned PASS.  This proves no Case 1(2) progress, introduced-label support
  growth, chart construction, source production, full branch termination,
  normal crossings, pole order, or RLCT.
- **Current status addendum, Case 1(2) row-strip progress bridge,
  2026-06-30.** Lean now adds the same-stage introduced-label progress alias
  `AoyagiIntroducedLabelBranchState.progressStep_sameStage_increment` and the
  Case 1(2) payload bridge
  `AoyagiIntroducedLabelBranchState.progressStep_case1DisplayedRowStrip_jIncrementPayload`
  in `lean/DLNFibre/DLN/Aoyagi/BlowupBranchProgress.lean`.  The bridge consumes
  only `Case1DisplayedRowStripJIncrementPayload` and proves the finite
  introduced-label support-growth step `(S,J) -> (S,J+1)` from the payload's
  actual-width proof for the fresh label.  Reproduction, statement card, and
  review are at
  `threads/04-blow-up-certificate/reproduction-a4-case1-rowstrip-progress-bridge.md`,
  `threads/04-blow-up-certificate/statement-card-a4-case1-rowstrip-progress-bridge.md`,
  and
  `threads/04-blow-up-certificate/review-a4-case1-rowstrip-progress-bridge.md`.
  Focused local build, direct warning check, full local `lake build DLNFibre`,
  no-sorry audit, whitespace check, and direct axiom probe passed; the new
  declarations report only `[propext, Classical.choice, Quot.sound]`.  Xhigh
  source/scope reviewer `Wegener` and xhigh Lean/API reviewer `Euler` returned
  PASS.  This covers Case 1(2), not Case 1(1): the latter is same-domain
  selected-old lowering and needs a separate old-variable plateau-count
  progress measure.  This proves no chart construction, post-state
  construction, source production, full branch termination, normal crossings,
  pole order, or RLCT.
- **Current status addendum, selected-entry branch progress bridge,
  2026-06-30.** Lean now adds a separate branch-progress layer
  `SelectedEntryAtlasBranchProgressData` in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryAnalyticAtlasProducer.lean`, and the
  displayed Case 2 introduced-label instance in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryBranchProgressBridge.lean`.  The
  source-production record is unchanged.  The progress data consumes supplied
  `SelectedEntryAtlasProducedBranchData` and supplied
  `SelectedEntryBranchTerminationData`, records an active branch guard, proves
  the supplied continuing/stopped guards cover it, and supplies a decreasing
  child only for continuing branches.  The displayed Case 2 instance uses the
  active guard `s.J+1 <= prefixMinNat n (s.S+1)` and continuing child
  `(S,J+1)`.  Reproduction and statement card are at
  `threads/04-blow-up-certificate/reproduction-a4-selected-entry-branch-progress-bridge.md`
  and
  `threads/04-blow-up-certificate/statement-card-a4-selected-entry-branch-progress-bridge.md`.
  Focused local build, direct warning checks, full local `lake build DLNFibre`,
  no-sorry audit, whitespace check, and direct axiom probe passed.  Xhigh
  source scout `Erdos` confirmed that Case 1(1) is same-domain old-plateau
  progress, not introduced-label support growth; only Case 1(2) should later
  feed a `J -> J+1` support-growth bridge.  This proves no source-production
  payloads, child-state realization by payload source data, stopped-branch
  child, full termination coverage, normal crossings, pole order, or RLCT.
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
  supplied bookkeeping, not chart-produced post-data. The corrected scalar
  accounting for the displayed Case 2 `Q/P` identity is now also proved:
  `D_J = u N` with `b'_i = u b_i` transports the selected scalar into the
  diagonal weights and does not leave a further final factor of `u`. The displayed
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
  The selected-entry finite affine-overlap family certificate
  `SelectedEntryFiniteAffineTransitionRegularFamily` is also proved in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`, with pair
  extraction and Case 2/displayed-pivot specialisations.  It records the
  actual transition-point formula, target coordinate formula, finite chart-map
  equality on the normalised target-coordinate overlap, inverse transition,
  self-transition, and cocycle.  This is finite selected-entry overlap algebra
  only: it can instantiate a finite transition predicate explicitly defined to
  mean these identities, but it is not analytic transition regularity, atlas
  coverage, source production, normal crossings, pole order, termination, or
  RLCT.
  Missing arbitrary pivot
  charts,
  non-top-left source-displayed formulas, the full source blockdiag identity
  beyond the unchanged-top lift, full polynomial-coordinate chart construction,
  and proof that the chart produces the supplied recurrence post-state remain
  open. The printed `b'_i` versus
  standalone-`u` ambiguity is now handled only by the single-count
  normalization: the selected variable is absorbed into successor weights, not
  counted a second time outside them. The introduced-label progress kernel now
  proves that strict growth of the finite introduced-label support is
  well-founded and that the displayed Case 2 same-stage advance
  `(S,J) -> (S,J+1)` is one such progress step under the actual-width bound,
  hence under the prefix-minimum continuation bound. This is termination
  infrastructure only: it does not connect branch source-production payloads
  or branch guards to the progress relation. Termination and boundary cases
  remain open.
- **Kill-condition.** The transition system misses a source chart or permits a
  terminal state not covered by Aoyagi's proof; or the Case 2 mismatch is a
  genuine source gap with no certificate-level repair compatible with the
  terminal formula.
- **Evidence/source.** Aoyagi blow-up section, PDF pp. 14-23.
- **Pen-and-paper reproduction.** draft at
  `threads/04-blow-up-certificate/reproduction-draft.md`; current repair
  report at `threads/04-blow-up-certificate/reproduction-repair-a4.md`;
  progress kernel at
  `threads/04-blow-up-certificate/reproduction-a4-introduced-label-progress-kernel.md`;
  recurrence branch termination-data adapter at
  `threads/04-blow-up-certificate/reproduction-a4-recurrence-branch-termination-data.md`;
  Case 1(2) row-strip progress bridge at
  `threads/04-blow-up-certificate/reproduction-a4-case1-rowstrip-progress-bridge.md`;
  Case 1(1) same-domain plateau progress at
  `threads/04-blow-up-certificate/reproduction-a4-case1-same-domain-plateau-progress.md`;
  combined recurrence branch progress at
  `threads/04-blow-up-certificate/reproduction-a4-combined-recurrence-branch-progress.md`.
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
	  Review of the introduced-label progress kernel is saved at
	  `threads/04-blow-up-certificate/review-a4-introduced-label-progress-kernel.md`.
	  Review of the Case 1(2) row-strip progress bridge is saved at
	  `threads/04-blow-up-certificate/review-a4-case1-rowstrip-progress-bridge.md`.
	  Review of the Case 1(1) same-domain plateau progress kernel is saved at
	  `threads/04-blow-up-certificate/review-a4-case1-same-domain-plateau-progress.md`.
	  Review of the combined recurrence branch progress kernel is saved at
	  `threads/04-blow-up-certificate/review-a4-combined-recurrence-branch-progress.md`.
	  Review of the recurrence branch termination-data adapter is saved at
	  `threads/04-blow-up-certificate/review-a4-recurrence-branch-termination-data.md`.
- **Lean target.** No full transition theorem yet. Safe narrow targets must
  stay inside finite bookkeeping or monomial divisibility lemmas that do not
  assert Aoyagi's Case 2 transition. The first such target is landed in
  `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`; the introduced-label
  progress kernel is landed in
  `lean/DLNFibre/DLN/Aoyagi/BlowupBranchProgress.lean`.
- **Proved.** introduced-label progress kernel:
  `AoyagiIntroducedLabelBranchState`, `support`, `remaining`,
  `support_subset_actual`, `remaining_lt_of_support_ssubset`, `progressStep`,
  `progressStep_wellFounded`, `support_ssubset_case2_increment`,
  `progressStep_case2_increment`, and
  `progressStep_case2_increment_of_prefixBound`; same-stage and Case 1(2)
  row-strip payload bridges:
  `AoyagiIntroducedLabelBranchState.progressStep_sameStage_increment` and
  `AoyagiIntroducedLabelBranchState.progressStep_case1DisplayedRowStrip_jIncrementPayload`.
  This proves well-founded
  descent for strict growth of the finite introduced-label support and the
  displayed Case 2 and Case 1(2) row-strip same-stage increments under their
  stated actual-width/payload bounds; same-domain Case 1(1) plateau progress:
  `IntroducedLabelRecurrenceState.levelPlateau`,
  `levelPlateauProgress`, `levelPlateauProgress_wellFounded`,
  `abovePivotLevelFinset`, `abovePivotLevelProgress`,
  `abovePivotLevelProgress_wellFounded`,
  `levelPlateauProgress_of_case1SelectedOldLevelMoveData`,
  `levelPlateauProgress_case1SelectedOldLevelMove_of_sameDomain`,
  `abovePivotLevelProgress_of_case1SelectedOldLevelMoveData`, and
  `abovePivotLevelProgress_case1SelectedOldLevelMove_of_sameDomain`; these
  prove strict finite count decrease for Case 1(1) selected-old lowering, but
  are not yet a combined branch termination theorem. Combined recurrence branch
  progress:
  `AoyagiRecurrenceBranchState`, `support`, `toIntroducedState`, `remaining`,
  `stageBudget`, `abovePivotCount`, `progressStageBase`, `progressWeightBase`,
  `progressMeasure`, `progressStep`, `progressStep_wellFounded`,
  `progressStep_of_toIntroducedState_progress`,
  `sameStageChildWithRecurrence_progress_of_actualWidth`,
  `sameStageChildWithRecurrence_progress_of_prefixBound`,
  `case2SuccChild_progress_of_prefixBound`,
  `sameStageChildWithRecurrence_progress_of_case1DisplayedRowStripPayload`,
  `sameStageChildWithRecurrence_progress_of_case2DisplayedPayload`,
  `stageSuccZeroWithRecurrence_progress`,
  `sameDomainWithRecurrence_progress_of_abovePivotProgress`,
  `sameDomainWithRecurrence_progress_of_case1SelectedOldLevelMoveData`, and
  `case1SelectedOldLevelMove_progress_of_sameDomain`; these prove a single
  finite well-founded progress relation combining support growth, stage
  handoff, and same-domain selected-old lowering, but still do not construct
  source production, branch guards, terminal payloads, or full analytic-atlas
  termination. Selected-entry recurrence branch termination adapter:
  `selectedEntryRecurrenceBranchTerminationData`; this packages the combined
  recurrence progress relation as `SelectedEntryBranchTerminationData` from
  supplied initial recurrence data, but does not construct source production,
  branch guards, continuing children, terminal payloads, or full analytic-atlas
  termination. Also
  proved terminal-exponent split API:
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
  Latest minimum-to-lambda normalization: Lean now proves
  `aoyagiLemma5MinNumerator_div_four_sq_eq_theorem2ResidueTerm` in
  `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`, showing that for
  `ell=n+1`,
  `aoyagiLemma5MinNumerator n a / (4*ell^2) = a*(ell-a)/(4*ell)` over
  rationals.  Reproduction:
  `threads/05-arithmetic-tail/reproduction-lemma5-min-numerator-residue-normalization-a5.md`;
  statement card:
  `threads/05-arithmetic-tail/statement-card-a5-lemma5-min-numerator-residue-normalization.md`;
  review:
  `threads/05-arithmetic-tail/review-lemma5-min-numerator-residue-normalization-a5.md`.
  This is only finite rational cancellation; it does not prove terminal
  exponent identification, active-ratio minimality, terminal-label exactness,
  chart counts, pole order, normal crossings, or RLCT.

## Claim A6 - final Aoyagi formula, conditional on A0

- **Statement.** Combining the proved Aoyagi-specific reductions with the cited
  normal-crossing extraction interface gives Aoyagi's RLCT and RLCT-order
  formula for deep linear networks.
- **Tier.** Final synthesis claim.
- **Status.** open.  Formula-notation, Definition 3 bridge, Definition 3
  source-data ceiling, Definition 3 source-data local wrappers, Definition 3
  source-data final-boundary handoff, conditional finite-exponent bridge,
  rank-width regular-shift final-boundary handoff,
  Case 2 regular-shift finite-formula bridge,
  terminal-order equality-bridge, Eq5 terminal-order bridge, Definition 3 Eq5
  `hsource`/`hlast` bridges, Definition 3 source-data Eq5 terminal-order
  bridge, Definition 3 terminal counted-datum classifier final-boundary
  bridge, Definition 3 arbitrary source-data obstruction, and Definition 3
  `ell=1` nonselected obstruction, equal-width source-data, equal-width ceiling
  data, equal-width explicit ceiling-data, positive-remainder ceiling data,
  all-source selected source-data, all-source selected/source-rank
  ceiling-data slices, and a nonconstant `(1,2,2)` diagnostic example, a
  three-width `L=2` triangle-inequality all-source constructor, and the `L=2`
  pairwise-distinct and repeated-positive/triangle finite classifications,
  repeated-positive/triangle finite formula packages, and a branch-overlap
  finite formula/order disagreement diagnostic, and the Theorem 2
  selected-width pair-sum range/Icc indexing conversion have landed.  A
  follow-up source audit confirms that Aoyagi PDF pp. 8-9 contain no
  branch-selection tie-breaker, so arbitrary Definition 3 source-data
  quantification is unsafe.  A separate closed-form cutoff boundary now records
  that `ClosedForm.lean` is a Core/LR-dependent comparison bridge unless and
  until its repaired-cutoff arithmetic is split into an explicitly quarantined
  import-light module.
  The final RLCT theorem remains open.
- **Kill-condition.** Any source hypothesis, rank bound, dimension convention,
  or pole-order convention is lost in translation.
- **Evidence/source.** Aoyagi Theorem 2, PDF pp. 8-9. Aoyagi Theorem 1
  (PDF pp. 6-7) is a cited earlier three-layer formula, not the multi-layer
  main theorem.
- **Pen-and-paper reproduction.** Definition 3/Theorem 2 formula translation
  reproduced at
  `threads/06-dln-translation/reproduction-definition3-theorem2-translation-a6.md`;
  Theorem 2 selected-width pair-sum range/Icc conversion reproduced at
  `threads/06-dln-translation/reproduction-theorem2-selected-width-pair-sum-range-icc-a6.md`;
  Definition 3 exact ceiling data reproduced at
  `threads/06-dln-translation/reproduction-definition3-exact-ceil-data-a6.md`;
  corrected closed-form cutoff boundary recorded at
  `threads/06-dln-translation/boundary-paper-closed-form-corrected-cutoff-a6.md`;
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
  Definition 3 Eq5 `hsource` bridge reproduced at
  `threads/06-dln-translation/reproduction-definition3-eq5-hsource-bridge-a6.md`;
  Definition 3 Eq5 `hlast` bridge reproduced at
  `threads/06-dln-translation/reproduction-definition3-eq5-hlast-bridge-a6.md`;
  Definition 3 arbitrary source-data obstruction reproduced at
  `threads/06-dln-translation/reproduction-definition3-source-data-obstruction-a6.md`;
  Definition 3 `ell=1` nonselected obstruction reproduced at
  `threads/06-dln-translation/reproduction-definition3-ell-one-nonselected-obstruction-a6.md`;
  Definition 3 source-data Eq5 terminal-order bridge reproduced at
  `threads/06-dln-translation/reproduction-definition3-source-data-eq5-terminal-order-bridge-a6.md`;
  rank-width regular-shift final-boundary bridge reproduced at
  `threads/06-dln-translation/reproduction-theorem2-rank-width-regular-shift-bridge-a6.md`;
  Definition 3 terminal counted-datum classifier final-boundary bridge
  reproduced at
  `threads/06-dln-translation/reproduction-definition3-terminal-countdatum-classifier-final-bridge-a6.md`;
  Definition 3 equal-width source data reproduced at
  `threads/06-dln-translation/reproduction-definition3-equal-width-source-data-a6.md`;
  Definition 3 equal-width ceiling data reproduced at
  `threads/06-dln-translation/reproduction-definition3-equal-width-ceil-data-a6.md`;
  Definition 3 equal-width explicit ceiling data reproduced at
  `threads/06-dln-translation/reproduction-definition3-equal-width-explicit-ceil-data-a6.md`;
  Definition 3 positive-remainder ceiling data reproduced at
  `threads/06-dln-translation/reproduction-definition3-positive-remainder-ceil-data-a6.md`;
  Definition 3 all-source selected source data reproduced at
  `threads/06-dln-translation/reproduction-definition3-all-source-selected-source-data-a6.md`;
  Definition 3 all-source selected ceiling data reproduced at
  `threads/06-dln-translation/reproduction-definition3-all-source-ceil-data-a6.md`;
  Definition 3 all-source source-rank ceiling data reproduced at
  `threads/06-dln-translation/reproduction-definition3-all-source-source-rank-ceil-data-a6.md`;
  Definition 3 nonconstant `(1,2,2)` example reproduced at
  `threads/06-dln-translation/reproduction-definition3-nonconstant-one-two-two-example-a6.md`;
  Definition 3 three-width triangle constructor reproduced at
  `threads/06-dln-translation/reproduction-definition3-three-width-triangle-a6.md`;
  Definition 3 `L=2` pairwise-distinct classification reproduced at
  `threads/06-dln-translation/reproduction-definition3-l-eq-two-pairwise-distinct-classification-a6.md`;
  Definition 3 `L=2` repeated-width classification reproduced at
  `threads/06-dln-translation/reproduction-definition3-l-eq-two-repeated-width-classification-a6.md`;
  Definition 3 `L=2` branch formula disagreement reproduced at
  `threads/06-dln-translation/reproduction-definition3-l-eq-two-branch-formula-disagreement-a6.md`;
  Definition 3 `L=2` branch order disagreement reproduced at
  `threads/06-dln-translation/reproduction-definition3-l-eq-two-order-disagreement-a6.md`;
  Definition 3 branch-selection source audit at
  `threads/06-dln-translation/source-audit-definition3-branch-selection-a6.md`;
  Definition 3 `L=2` branch-formula rank-width removal reproduced at
  `threads/06-dln-translation/reproduction-definition3-l-eq-two-branch-formula-rankwidth-removal-a6.md`;
  Definition 3 `L=2` branch-disjunction formula reproduced at
  `threads/06-dln-translation/reproduction-definition3-l-eq-two-branch-disjunction-formula-a6.md`;
  Case 2 finite-formula wrapper reproduced at
  `threads/06-dln-translation/reproduction-case2-theorem2-finite-formula-bridge-a6.md`;
  Case 2 regular-shift finite-formula wrapper reproduced at
  `threads/06-dln-translation/reproduction-case2-theorem2-regular-shift-finite-formula-bridge-a6.md`;
  Case 2 ratio-count finite-formula wrapper reproduced at
  `threads/06-dln-translation/reproduction-case2-theorem2-ratio-count-finite-formula-bridge-a6.md`;
  Case 2 chart-final boundary wrapper reproduced at
  `threads/06-dln-translation/reproduction-case2-theorem2-chart-final-bridge-a6.md`;
  remaining source-obligations boundary map at
  `threads/06-dln-translation/boundary-map-theorem2-remaining-source-obligations-a6.md`.
- **Reproduction check.** xhigh source/API checks incorporated in
  `threads/06-dln-translation/review-final-formula-notation-a6.md`;
  Theorem 2 selected-width pair-sum range/Icc conversion reviewed at
  `threads/06-dln-translation/review-theorem2-selected-width-pair-sum-range-icc-a6.md`;
  Definition 3 exact ceiling data reviewed at
  `threads/06-dln-translation/review-definition3-exact-ceil-data-a6.md`;
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
  Definition 3 Eq5 `hsource` bridge reviewed at
  `threads/06-dln-translation/review-definition3-eq5-hsource-bridge-a6.md`;
  Definition 3 Eq5 `hlast` bridge reviewed at
  `threads/06-dln-translation/review-definition3-eq5-hlast-bridge-a6.md`;
  Definition 3 arbitrary source-data obstruction reviewed at
  `threads/06-dln-translation/review-definition3-source-data-obstruction-a6.md`;
  Definition 3 `ell=1` nonselected obstruction reviewed at
  `threads/06-dln-translation/review-definition3-ell-one-nonselected-obstruction-a6.md`;
  Definition 3 source-data Eq5 terminal-order bridge reviewed at
  `threads/06-dln-translation/review-definition3-source-data-eq5-terminal-order-bridge-a6.md`;
  rank-width regular-shift final-boundary bridge reviewed at
  `threads/06-dln-translation/review-theorem2-rank-width-regular-shift-bridge-a6.md`;
  Definition 3 terminal counted-datum classifier final-boundary bridge
  reviewed at
  `threads/06-dln-translation/review-definition3-terminal-countdatum-classifier-final-bridge-a6.md`;
  Definition 3 equal-width source data reviewed at
  `threads/06-dln-translation/review-definition3-equal-width-source-data-a6.md`;
  Definition 3 equal-width ceiling data reviewed at
  `threads/06-dln-translation/review-definition3-equal-width-ceil-data-a6.md`;
  Definition 3 equal-width explicit ceiling data reviewed at
  `threads/06-dln-translation/review-definition3-equal-width-explicit-ceil-data-a6.md`;
  Definition 3 positive-remainder ceiling data reviewed at
  `threads/06-dln-translation/review-definition3-positive-remainder-ceil-data-a6.md`;
  Definition 3 all-source selected source data reviewed at
  `threads/06-dln-translation/review-definition3-all-source-selected-source-data-a6.md`;
  Definition 3 all-source selected ceiling data reviewed at
  `threads/06-dln-translation/review-definition3-all-source-ceil-data-a6.md`;
  Definition 3 all-source source-rank ceiling data reviewed at
  `threads/06-dln-translation/review-definition3-all-source-source-rank-ceil-data-a6.md`;
  Definition 3 nonconstant `(1,2,2)` example reviewed at
  `threads/06-dln-translation/review-definition3-nonconstant-one-two-two-example-a6.md`;
  Definition 3 three-width triangle constructor reviewed at
  `threads/06-dln-translation/review-definition3-three-width-triangle-a6.md`;
  Definition 3 `L=2` pairwise-distinct classification reviewed at
  `threads/06-dln-translation/review-definition3-l-eq-two-pairwise-distinct-classification-a6.md`;
  Definition 3 `L=2` repeated-width classification reviewed at
  `threads/06-dln-translation/review-definition3-l-eq-two-repeated-width-classification-a6.md`;
  Definition 3 `L=2` branch formula disagreement reviewed at
  `threads/06-dln-translation/review-definition3-l-eq-two-branch-formula-disagreement-a6.md`;
  Definition 3 `L=2` branch order disagreement reviewed at
  `threads/06-dln-translation/review-definition3-l-eq-two-order-disagreement-a6.md`;
  Definition 3 branch-selection source audit by xhigh `Einstein the 3rd` at
  `threads/06-dln-translation/source-audit-definition3-branch-selection-a6.md`;
  Definition 3 `L=2` branch-formula rank-width removal reviewed at
  `threads/06-dln-translation/review-definition3-l-eq-two-branch-formula-rankwidth-removal-a6.md`;
  Definition 3 `L=2` branch-disjunction formula reviewed at
  `threads/06-dln-translation/review-definition3-l-eq-two-branch-disjunction-formula-a6.md`;
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
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.ofSelectedSumCeil`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.ofSelectedSumCeil_ceilWidth`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.ofSelectedSumCeil_aParam`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.nonempty_of_ell_pos`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.ofSelectedSumPositiveRemainder`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.theorem2OrderFormula`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.reducedWidth_mem_selectedValueSet_of_ell_eq_one`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.of_ell_eq_one_selectedValueSet_covers`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_ell_one_of_L_eq_two_positive_repeated`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_sourceData_iff_repeatedPositive_or_triangle_of_L_eq_two`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_ceilData`,
  `DLNFibre.DLN.Aoyagi.aoyagiSelectedWidthPairSum`,
  `DLNFibre.DLN.Aoyagi.aoyagiSelectedWidthPairSum_eq_range_Icc_selectedWidthNat`,
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
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.selected_strict_of_eq_selectedReducedWidths`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.lastPoint_le`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.not_exists_widths_one_two_hundred`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.reducedWidth_mem_selectedValueSet_of_ell_eq_one_rankWidth`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.selectedWidth_le_pred_of_ceilData`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.htildeLowerNat_add_one_labelBounds_of_ceilData`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.lemma5Eq4_localData_of_ceilData`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.lemma5Eq5_labelBounds_of_ceilData`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.lemma5Eq3_localData_of_ceilData_and_slack`,
  and
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_selectedReducedWidthCeilData_of_rankWidth`
  plus equal-width constructors
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_consecutive_of_constant_reducedWidth_pos`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_consecutive_of_all_selected_strict`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict_rankWidth`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict_sourceRankStratum`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_consecutive_three_widths_selectedReducedWidthCeilData_of_triangle_rankWidth`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.ell_eq_two_of_L_eq_two_rankWidth_pairwiseDistinct`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.cut_eq_consecutive_of_L_eq_two`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_sourceData_iff_allSourceStrict_of_L_eq_two_rankWidth_pairwiseDistinct`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_consecutive_nonconstant_widths_one_two_two_selectedReducedWidthCeilData`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.sourceRangeRankWidth_of_constant_reducedWidth`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_consecutive_selectedReducedWidthCeilData_of_constant_reducedWidth_pos`,
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.equalWidthOfDecomposition`, and
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_consecutive_explicitCeilData_of_constant_reducedWidth_decomposition`
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
  Definition 3 Eq5 `hsource` bridge:
  `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze_of_definition3SourceData`
  in `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalOrderDefinition3Bridge.lean`,
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
  rank-width regular-shift final-boundary bridge:
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_rankWidth_regularVariableCountShift`
  and
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_regularVariableCountShift`
  in `lean/DLNFibre/DLN/Aoyagi/Theorem2RankWidthRegularShiftBridge.lean`; current
  Definition 3 terminal counted-datum classifier final-boundary bridge:
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_rankWidth_activePair_ratioCount_terminalMinimumCountDatumClassifier`
  and
  `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_activePair_ratioCount_terminalMinimumCountDatumClassifier`
  in `lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`; current
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
  Definition 3 selected-sum average rewrite, Nat-indexed range/Icc reindexing
  of Theorem 2's selected-width pair sum, equality of the average and ceiling
  displayed lambda formulas under supplied ceiling data, and equality of the
  ceiling and expanded displayed lambda formulas when `0 < ell`.  Also proved
  an exact Definition 3 ceiling-data constructor pinning
  `ceilWidth=(sum+ell-1)/ell` and the positive residue
  `aParam=((sum-1)%ell+1).toNat`; the older `nonempty_of_ell_pos` constructor
  now delegates to this exact datum.  Also
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
  existence remains supplied.  Also proved the explicit positive-remainder
  ceiling-data constructor: a supplied decomposition
  `sum_j m_j = ell * ceilPred + a` with `0<a<=ell` gives
  `ceilWidth=ceilPred+1` and `aParam=a`; this is finite arithmetic only and
  does not add a source-facing wrapper.  Also proved source-data local wrappers
  that
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
  Eq5 `hsource` bridge: the strict selected-width inequality consumed by the
  Eq5 terminal-order block-width cardinal squeeze is derived from
  `AoyagiDefinition3SourceData` after rewriting
  `m = aoyagiSelectedReducedWidths H r C`; the blockwise actual-width
  hypothesis, Eq5 endpoint-family payload, injectivity, branch data, and
  terminal-family data remain explicit.  This is not selected-cutpoint
  construction, Definition 3 source-data existence, actual-width dominance,
  Eq5 construction, Lemma 5 exactness, chart production, pole order, or RLCT.
  The same wrapper now also derives the terminal source-range endpoint
  `C.point (N+1) <= L+1` from `AoyagiDefinition3SourceData.cut_le`, via
  `AoyagiDefinition3SourceData.lastPoint_le`; generic Eq5 APIs still keep that
  endpoint hypothesis explicit.  This does not construct selected cutpoints,
  Definition 3 source data, Eq5 families, charts, pole order, or RLCT.  Also
  proved a Definition 3
  source-data Eq5 terminal-order bridge: source data and a source-range
  rank-width hypothesis existentially produce `m,data`, and a supplied Eq5
  payload/active-ratio/chart-count callback for that produced pair builds the
  supplied final-boundary and chart-final-boundary sockets.  The callback
  requires `P.cut = C`, so the Eq5 payload and Definition 3 source data use
  the same selected cutpoints.  This is not selected-cutpoint construction,
  rank-width from matrix data, Eq5 family construction, Lemma 5 exactness,
  active-ratio bounds, chart counts, chart production, pole order, or RLCT.
  Also proved a rank-width regular-shift final-boundary bridge: source data
  and full source-range rank-width `hr` produce `m,data`, while the finite
  regular-variable shift uses only the endpoint projections from the same
  `hr`.  The shifted extraction hypothesis and reduced minimum/order
  obligations remain supplied.  The existing source-rank regular-shift bridge
  now derives `hr` from the A2 source-rank stratum and delegates to this
  rank-width bridge.  This does not construct regular-suspension charts,
  analytic ideal transport, normal crossings, pole order, or RLCT.
  Also proved a Definition 3 terminal counted-datum classifier final-boundary
  bridge: source data and a source-range rank-width hypothesis
  existentially produce `m,data`, and a supplied terminal counted-datum
  classifier, supplied branch-label injectivity, active-ratio certificate,
  displayed-ratio chart-count certificate, and A0 extraction hypothesis build
  the supplied final-boundary and chart-final-boundary sockets for that
  produced pair.  This is not selected-cutpoint construction, rank-width from
  matrix data, classifier construction, branch-label injectivity, active-ratio
  bounds, chart counts, chart production, pole order without A0, or RLCT.
  Also proved a Definition 3 arbitrary source-data obstruction: for `L=2`,
  `r=0`, and reduced widths `1,2,100`, no `ell,C` satisfy
  `AoyagiDefinition3SourceData 2 ell H 0 C`.  This blocks a blanket
  source-data existence theorem under the printed inequalities; it is not a
  corrected Definition 3 or a classification of source-data existence.  Also
  proved the general `ell=1` necessary condition: under source-range
  rank-width nonnegativity, `AoyagiDefinition3SourceData L 1 H r C` forces
  every source-range reduced-width value to belong to the selected value set.
  This isolates the `ell=1` branch of the obstruction and is not selected-
  cutpoint construction or an `ell>1` classification.  Also proved the
  equal-width Definition 3 lane from Aoyagi's example: positive constant
  source-range reduced width gives consecutive selected cutpoints and
  `AoyagiDefinition3SourceData`; the same constant-width hypothesis gives the
  source-range rank-width bound and hence the standard selected reduced-width
  ceiling-data package.  Finally, under a positive-remainder decomposition
  `w = L*q + a` with `0<a<=L`, Lean constructs the explicit equal-width
  ceiling datum with `ceilWidth = w+q+1` and `aParam = a`.  These equal-width
  results do not prove arbitrary source-data existence, uniqueness of the
  ceiling datum, Eq5 construction, chart production, pole order, or RLCT.  Also
  proved the all-source selected source-data constructor: under the strict
  all-source selected inequality, consecutive cutpoints with `ell=L` give
  `AoyagiDefinition3SourceData L L H r C`.  The nonselected clauses are
  vacuous because every source-range reduced-width value lies in the selected
  value image.  This removes the constant-width hypothesis from that narrow
  consecutive lane, but still does not prove arbitrary selected-cutpoint
  existence, Definition 3 classification, ceiling data, Eq5 construction,
  chart production, pole order, or RLCT.  Also proved the all-source selected
  ceiling-data package: adding explicit source-range rank-width to the
  all-source strict inequality produces selected reduced widths and a
  Definition 3 ceiling datum through the existing generic package.  This does
  not prove rank-width from matrix data, compute `ceilWidth` or `aParam`, build
  Eq5 payloads, produce charts, identify pole order, or extract RLCT.  Also
  proved the source-rank-stratum version of that all-source package, using the
  existing A2 bridge from source-rank stratum membership and the dimension
  convention to discharge rank-width.  This is the only source-rank wrapper for
  the all-source lane so far; avoid final-socket clones unless a downstream
  theorem needs one.  Also proved a concrete nonconstant diagnostic example:
  reduced widths `(1,2,2)` at `L=2,r=0` produce consecutive all-source source
  data and a ceiling package with selected widths `1,2,2`.  This witnesses
  that the all-source lane is broader than equal-width but is not an arbitrary
  existence or classification theorem.  Also proved the full finite `L=2`
  Definition 3 source-data classification: source data exists exactly when
  either all three reduced-width values are positive and at least two repeat,
  or the three all-source triangle inequalities hold.  This bare source-data
  classification needs no rank-width hypothesis; it does not classify `L>2`,
  construct ceiling data, build Eq5 payloads, produce charts, identify pole
  order, or extract RLCT.  Also proved a branch-overlap finite formula
  diagnostic: for `L=2,r=0` and reduced widths `(2,3,3)`, the printed
  Definition 3 conditions as formalised admit both an `ell=1` repeated-positive
  package and an `ell=2` all-source triangle package, but their finite Theorem
  2 lambda formula values are `3` and `5/2`.  This is a guardrail against
  branch-independence claims, not an analytic RLCT ambiguity theorem.  The
  companion `(1,2,2)` diagnostic proves that overlapping branches can also
  have equal finite lambda value but different finite order formulas, `1` and
  `2`.  The follow-up source audit found no printed Definition 3 tie-breaker
  on pp. 8-9, so the controller boundary is to keep selected source data
  supplied or produce it inside a source-backed branch.  This is finite formula
  bookkeeping only, not a pole-order theorem.
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

Latest A6 Case 2 regular-shift finite-formula wrappers:
`Case2Theorem2FiniteExponentBridge.lean` now also contains
`Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_regularVariableCountShift_of_forall_le_of_centerCard_add_regularTerm_eq_fromCeilData`
and
`Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_regularVariableCountShift_of_forall_le_of_centerCard_add_regularTerm_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le`.
These consume the reduced Case 2/A0 center-ratio minimum bridge, endpoint rank
bounds, supplied active-ratio lower bounds, and a supplied shifted lambda
equality
`card(case2ResidualBlockPivotEntries n S J)/2 + regularTerm =
aoyagiTheorem2Lambda_fromCeilData ...`.  They fill the finite formula
boundary for
`D.jacobianPriorLossShift (aoyagiTheorem2RegularVariableCount Lthm H r)`.
The chart-count variant derives only the reduced order equality before the
shift.  This is finite exponent-array arithmetic, not regular-suspension chart
construction, analytic transport, normal-crossing production, pole order, or
RLCT.  Reproduction:
`threads/06-dln-translation/reproduction-case2-theorem2-regular-shift-finite-formula-bridge-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-case2-theorem2-regular-shift-finite-formula-bridge.md`.

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

Latest A5 terminal binary first-nonbase selector:
`Lemma5SuppliedFamily.lean` now proves a total finite maps-to adapter for a
supplied terminal binary-prefix-delta chain:
`aoyagiLemma5InteriorNonbaseCoordSet`,
`aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase`, and
`aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase_mem_of_terminalH_binaryIncrementPrefixDelta`.
The selector returns the base datum when all interior chain values agree with
`baseValue`, otherwise the least nonbase interior coordinate-value datum.  The
membership proof is exactly base insertion in the first case and the existing
single-coordinate terminal binary maps-to theorem in the second.  This is not
the Lemma 5 source classifier: no injection, no no-extra coverage, no
back-to-label map, no Eq3/Eq4/Eq5 branch construction, no terminal exactness,
no pole order, no normal crossings, and no RLCT extraction are proved.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-binary-first-nonbase-selector-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-binary-first-nonbase-selector.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-binary-first-nonbase-selector-a5.md`.

Latest A2 product-reduction triangular coordinate chart:
`ProductReduction.lean` now defines
`ProductReductionStepRawCoordinates`,
`ProductReductionStepChartCoordinates`, their determinant-chart predicates,
the p. 13 forward map and inverse map, determinant-domain preservation, and
the two inverse identities.  The variables are dimension-balanced by retaining
passive `D`, `A1`, and `A3`; the formulas invert `A1` and `Ctop`/`C1*A1` but
never invert `D`.  This reproduces the elementary triangular variable change
behind the p. 13 regular variables.  It is not analytic coordinate-chart
construction, exact-rank/source-rank openness, block-difference wrapper
transport, regular-suspension construction, analytic germ transport, coverage,
Jacobian compatibility, normal crossings, pole order, or RLCT extraction.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-product-reduction-triangular-coordinate-chart.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-product-reduction-triangular-coordinate-chart.md`.
Review:
`threads/03-block-product-reduction/review-a2-product-reduction-triangular-coordinate-chart.md`.

Latest A2 product-reduction step product-difference wrapper:
`ProductReduction.lean` now proves
`productReductionStepCoordinate_triangularBlockProduct` and
`productReductionStepCoordinate_productDifference`.  These theorems consume a
prior triangular product hypothesis
`[I 0; F3old I] T = [C1 0; 0 D] [A1 A2; A3 A4]`, use `x.toChart`, and prove
the next diagonal product plus the signed p. 13 product-difference block
with lower-right correction `D*C - F3*F2`.  No inverse of `D` is used.  This
is finite block algebra only, not a suffix-state adapter, analytic chart,
ideal-transport theorem, normal-crossing statement, pole-order result, or RLCT
extraction.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-product-reduction-step-product-difference-wrapper.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-product-reduction-step-product-difference-wrapper.md`.
Review:
`threads/03-block-product-reduction/review-a2-product-reduction-step-product-difference-wrapper.md`.

Latest A2 suffix-state step coordinate adapter:
`ProductReduction.lean` now proves the local `ChartLocalSuffixState`
adapter from a block-diagonal suffix-state invariant to the p. 13 coordinate
wrappers:
`stepRawCoordinates`, determinant and field bridge lemmas,
`stepRawCoordinates_priorProduct`,
`stepRawCoordinates_triangularBlockProduct`, and
`stepRawCoordinates_productDifference`.  The raw `A` blocks come from
`transformedEdge E p S`; the matrix `T` in the product wrapper is
`P p.castSucc j`.  The adapter takes a lower-unitriangular witness for `S.L`
as input, uses the transformed-edge determinant chart, and never inverts
`S.D`.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-suffix-state-step-coordinate-adapter.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-suffix-state-step-coordinate-adapter.md`.
Review:
`threads/03-block-product-reduction/review-a2-suffix-state-step-coordinate-adapter.md`.

Latest A2 suffix-state step coordinate specialization:
`ProductReduction.lean` now proves
`ChartLocalSuffixState.suffixState_stepRawCoordinates_triangularBlockProduct`
and
`ChartLocalSuffixState.suffixState_stepRawCoordinates_productDifference`.
These wrappers specialize the arbitrary `S` adapter to
`S = suffixState E j p.succ hpj`, use
`suffixState_L_eq_lowerUnitriangular` to choose `F3prev`, and keep only the
local inputs `S.BlockDiagonal P hpj` and the determinant chart for
`transformedEdge E p S`.  The product matrix is
`P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj)`, not the transformed
edge.  This is finite block algebra only: no global chart derivation, analytic
coverage, ideal transport, normal crossings, pole order, or RLCT extraction.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-suffix-state-step-coordinate-specialization.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-suffix-state-step-coordinate-specialization.md`.
Review:
`threads/03-block-product-reduction/review-a2-suffix-state-step-coordinate-specialization.md`.

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

Latest A4 Case 2 transition supplied-successor reindexed product:
`SelectedEntryNormalCrossing.lean` now adds
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_reindexedNextSourceProduct_suppliedCsucc_sourceSubstitution_of_displayed_normalized_ne_zero`.
It consumes transition-generated displayed target data and a supplied
`SourceProductionObligation` for those data, then combines the displayed
substitution-block transition equality with the supplied-`Csucc` reindexed
product consumer.  This is a finite adapter only.  It does not construct the
obligation, construct or source-produce `Csucc`, produce suffixes or successor
charts, prove analytic transition regularity, chart coverage, normal
crossings, pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-transition-supplied-successor-reindexed-product-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-transition-supplied-successor-reindexed-product.md`.
Review:
`threads/04-blow-up-certificate/review-case2-transition-supplied-successor-reindexed-product-a4.md`.

Latest A4 Case 2 source-current stack substitution block:
`BlowupArithmetic.lean` now proves
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.continuing_sourceCurrentStack_suppliedCsucc_of_substitutionBlock_eq`.
Given a supplied block equality
`case2DisplayedSourceSubstitutionBlock ... = B`, it reuses the existing
supplied-`Csucc` source-current stack theorem and rewrites only the lower-left
substitution block.  The row-operation witness, supplied successor, suffix,
and corrected post-data are unchanged.  This is finite congruence only: no
source-production obligation, `Csucc`, suffix, successor chart, transition
regularity, chart coverage, normal crossing, pole-order, or RLCT construction
is proved.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-current-stack-substitution-block-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-current-stack-substitution-block.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-current-stack-substitution-block-a4.md`.

Latest A4 Case 2 free-`Cprime` two-edge factor-product naming:
`BlowupArithmetic.lean` now names the already-proved displayed lower-row
product as
`case2DisplayedPostPivotFreeTwoEdgeFactorProduct`, with alias theorem
`case2DisplayedPaperDppp_mul_freeCprime_postPivot_eq_freeTwoEdgeFactorProduct`.
This exposes the finite product as post-pivot residual block followed by the
transported free following-factor tail, without forcing a dependent
`residualFactorProduct` statement.  It is vocabulary only: no ambient p.13
factor-family construction, source production of `Cprime`, source coverage,
residual-index equivalence, normal crossings, pole order, or RLCT.  Updated
reproduction/statement/review:
`threads/04-blow-up-certificate/reproduction-case2-free-cprime-continuing-branch-a4.md`,
`threads/04-blow-up-certificate/statement-card-a4-case2-free-cprime-continuing-branch.md`,
and
`threads/04-blow-up-certificate/review-case2-free-cprime-continuing-branch-a4.md`.

Latest A4 Case 2 transition source-current stack supplied successor:
`SelectedEntryNormalCrossing.lean` now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_continuingSourceCurrentStack_suppliedCsucc_sourceSubstitution_of_displayed_normalized_ne_zero`.
It consumes transition-generated displayed target data and a supplied
`SourceProductionObligation` for those data, then combines chart-map equality,
the displayed target substitution-block rewrite, and the supplied-`Csucc`
source-current stack consumer.  The source selected block appears only as the
lower-left substitution block; target post-pivot data, displayed paper data,
weights, and center/principalization outputs remain target-displayed.  This
does not construct the obligation, `Csucc`, `Cterm`, suffixes, successor
charts, chart coverage, transition regularity, normal crossings, pole order,
termination, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-transition-source-current-stack-supplied-successor-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-transition-source-current-stack-supplied-successor.md`.
Review:
`threads/04-blow-up-certificate/review-case2-transition-source-current-stack-supplied-successor-a4.md`.

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

Latest A4 Case 2 constructed source following factor with old top rows:
`BlowupArithmetic.lean` now adds a finite source-coordinate constructor with
free carried old-top rows and free displayed residual-column data.  It proves
that old-top restriction recovers `Cold`, displayed residual restriction
recovers `Csrc`, generic `paperCprime` is `Q^-1*Csrc`, and the specialized
choice `Csrc=Q*Cprime` recovers `Cprime`.  The source-current row wrappers
then identify the current stacked block as `[Cold; Q*Cprime]` and the
formula-level successor stacked block as `[Cold; Cprime]`.  This does not
construct `SourceProductionObligation`, source-produce a successor chart or
suffix, produce recurrence/exponent post-data, prove chart coverage,
transition regularity, normal crossings, pole order, termination, or RLCT.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-constructed-source-following-factor-with-old-top-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-constructed-source-following-factor-with-old-top.md`.
Review:
`threads/04-blow-up-certificate/review-case2-constructed-source-following-factor-with-old-top-a4.md`.

Latest A4 Case 2 constructed old-top `Cprime` source-current stack:
`BlowupArithmetic.lean` now specializes the continuing source-current stack
theorem to the constructed old-top/free-`Cprime` source following factor.  The
left current row block is
`[Cold; case2DisplayedPaperConstructedFollowingFactor ... Cprime]`; the right
formula-level successor block is `[Cold; Cprime]`.  The theorem keeps `q`
existential and takes suffix matrices as supplied inputs.  This is finite stack
specialization only: no `SourceProductionObligation`, `Csucc`, suffix
production, successor chart family, chart coverage, transition regularity,
normal crossings, pole order, termination, or RLCT is constructed.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-constructed-oldtop-cprime-source-current-stack-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-constructed-oldtop-cprime-source-current-stack.md`.
Review:
`threads/04-blow-up-certificate/review-case2-constructed-oldtop-cprime-source-current-stack-a4.md`.

Latest A4 Case 2 constructed old-top `Cprime` terminal rows:
`BlowupArithmetic.lean` now proves that, for the constructed
old-top/free-`Cprime` source following factor, the stopped terminal transported
rows reindexed by `case2SourceTerminalRowEquiv J` are
`[Cold; case2DisplayedFreeCprimeTop ... Cprime]`.  The terminal candidate has
the same reindexed presentation, the explicit source-row matrix supplies
`SuppliedTerminalCprimeBridge.of_constructedWithOldTopFromCprime`, and the
stopped terminal product candidate rewrites through this explicit terminal
matrix.  This is not the source-current `[Cold; Cprime]` block theorem: the
terminal theorem keeps only the old rows plus the top row of `Cprime`.  No
source production, terminal chart construction, suffix production, transition
regularity, chart coverage, normal crossings, pole order, termination, or RLCT
is proved.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-constructed-oldtop-cprime-terminal-rows-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-constructed-oldtop-cprime-terminal-rows.md`.
Review:
`threads/04-blow-up-certificate/review-case2-constructed-oldtop-cprime-terminal-rows-a4.md`.

Latest A4 Case 2 constructed old-top `Cprime` terminal prefix:
`BlowupArithmetic.lean` now reindexes the constructed terminal source-row
matrix `[Cold; top(Cprime)]` to the stopped terminal-prefix row type under
`hstop : not (J+2 <= prefixMinNat n (S+1))`, and rewrites the stopped
terminal-prefix product candidate through that explicit prefix matrix.  This
requires the stopped-prefix row equivalence and does not use actual-width
collapse.  It proves no source production, terminal chart construction, suffix
production, transition regularity, chart coverage, normal crossings, pole
order, termination, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-constructed-oldtop-cprime-terminal-prefix-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-constructed-oldtop-cprime-terminal-prefix.md`.
Review:
`threads/04-blow-up-certificate/review-case2-constructed-oldtop-cprime-terminal-prefix-a4.md`.

Latest A4 Case 2 constructed old-top `Cprime` terminal-prefix source suffix:
`BlowupArithmetic.lean` now specializes the stopped terminal-prefix
source-suffix entry-ideal consumer to the constructed old-top/free-`Cprime`
source following factor.  The source side is `[Cold; Q*Cprime]`; the terminal
side is the stopped-prefix reindexing of the source-row reindexing of
`[Cold; top(Cprime)]`, followed by the supplied raw `sourceSuffixProduct`.
This proves no actual-width collapse, source production of `Csucc` or
`C'^(S+1)`, suffix construction, successor charts, transition regularity,
coverage, normal crossings, pole order, termination, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-constructed-oldtop-cprime-terminal-prefix-source-suffix-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-constructed-oldtop-cprime-terminal-prefix-source-suffix.md`.
Review:
`threads/04-blow-up-certificate/review-case2-constructed-oldtop-cprime-terminal-prefix-source-suffix-a4.md`.

Latest A4 Case 2 constructed old-top `Cprime` source-production obligation:
`BlowupArithmetic.lean` now packages the constructed old-top/free-`Cprime`
following factor into `SourceProductionObligation` with explicit terminal
matrix equal to the source-row reindexing of `[Cold; top(Cprime)]`.
The landed names are
`case2DisplayedSourceTerminalTransportedRows_constructedWithOldTopFromCprime_eq_terminalStack`
and
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.of_constructedWithOldTopFromCprime_terminalStack`.
This proves only finite interface packaging from the canonical formula-level
constructor; no source production of `Csucc` or `C'^(S+1)`, suffix construction,
successor chart construction, transition regularity, chart coverage, normal
crossings, pole order, termination, or RLCT is proved.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-constructed-oldtop-cprime-source-production-obligation-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-constructed-oldtop-cprime-source-production-obligation.md`.
Review:
`threads/04-blow-up-certificate/review-case2-constructed-oldtop-cprime-source-production-obligation-a4.md`.

Latest A4 Case 2 transition constructed old-top `Cprime` source-current stack:
`SelectedEntryNormalCrossing.lean` now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_continuingSourceCurrentStack_constructedWithOldTopFromCprime_sourceSubstitution_of_displayed_normalized_ne_zero`.
It constructs the required `SourceProductionObligation` from arbitrary `Cold`,
free displayed `Cprime`, and supplied suffix matrices `Ctail`, then consumes
the existing supplied-`Csucc` displayed-overlap source-current stack theorem.
The source-current side uses the constructed following factor
`[Cold; Q*Cprime]`; the successor side is the formula-level successor for that
factor; the lower-left substitution block is rewritten to the original
source-selected block.  This proves no source production of `Csucc` or
`C'^(S+1)`, no suffix construction, no successor charts, no transition
regularity, no chart coverage, no normal crossings, no pole order, no
termination, and no RLCT consequence.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-transition-constructed-oldtop-cprime-source-current-stack-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-transition-constructed-oldtop-cprime-source-current-stack.md`.
Review:
`threads/04-blow-up-certificate/review-case2-transition-constructed-oldtop-cprime-source-current-stack-a4.md`.

Current A4 boundary claim after the constructed old-top `Cprime` stack:
do not count any theorem as source production if its proof only chooses
formula-level `Csucc`/`Cterm`, invokes
`SourceProductionObligation.of_formulaSuccessor_transportTerminalRows` or
`SourceProductionObligation.of_constructedWithOldTopFromCprime_terminalStack`,
uses `ob.Csucc_eq_formula`, or packages arbitrary `Cold`, `Cprime`, and
`Ctail` inputs.  Such theorems are compatibility adapters.  The durable audit
is
`threads/04-blow-up-certificate/audit-case2-post-constructed-cprime-source-production-boundary-a4.md`.

Next A4 source-moving claim to investigate: the selected-entry finite
chart-certificate layer already feeds the A0 certificate spine with chart maps,
one active coordinate, monomial loss, formal Jacobian/prior determinant, unit
factors, exponent ratios, and chart counts.  It still does not prove analytic
atlas coverage, transition regularity, source production of successor/suffix
data, analytic Jacobian/volume-form compatibility, global normal crossings,
termination, pole order, or RLCT.  The next reproduction target is
`threads/04-blow-up-certificate/reproduction-selected-entry-analytic-atlas-boundary-a4.md`.
The matching statement card is
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-analytic-atlas-boundary.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-analytic-atlas-boundary-a4.md`.
Lean now defines `SelectedEntryAnalyticAtlasBoundary` and
`SelectedEntryAnalyticAtlasBoundary.exponentData` in
`SelectedEntryNormalCrossing.lean`.  This is a supplied boundary only: no
coverage, regularity, source production, termination, normal crossings, pole
order, or RLCT theorem is proved.

Latest A4 selected-entry analytic atlas final-socket adapter:
`SelectedEntryAnalyticAtlasFinalBridge.lean` now proves
`SelectedEntryAnalyticAtlasBoundary.theorem2SuppliedChartFinalBoundary_of_selectedWidths_eq_reduced_of_extractionHypothesis_of_finiteExponentFormula`.
It consumes a supplied `SelectedEntryAnalyticAtlasBoundary`, selected-width
provenance, an explicit `B.chartCertificate.ExtractionHypothesis`, and an
explicit `AoyagiTheorem2FiniteExponentFormulaHypothesis B.exponentData ...`,
then returns the existing chart-final Theorem 2 boundary for
`B.chartCertificate`.  This proves no analytic atlas existence, extraction
hypothesis, finite formula, active-ratio lower bound, chart count, source
production, pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-analytic-atlas-final-socket-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-analytic-atlas-final-socket.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-analytic-atlas-final-socket-a4.md`.

Latest A4 concrete selected-entry analytic atlas Case 2 source-production
payload:
`SelectedEntryAnalyticAtlasCase2FinalBridge.lean` now proves
`SelectedEntryCase2DisplayedA0SourceProduction.of_case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate`.
For the concrete all-pivot finite chart certificate
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate n hS hcont`,
the theorem constructs the nonvacuous
`SelectedEntryCase2DisplayedA0SourceProduction` payload from the displayed
continuing Case 2 center-square/formal-Jacobian certificate and the existing
all-pivot local exponent-coordinate adapter.  This removes an opaque
source-production payload only for that concrete finite certificate.  It does
not prove source production for arbitrary `Cnc`, analytic atlas coverage,
chart or transition regularity, analytic Jacobian/volume-form compatibility,
branch termination, global active-ratio/chart-count facts, normal crossings,
pole order, or RLCT.  The arbitrary chart index `c` is only a finite
exponent-coordinate adapter.  Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-analytic-atlas-case2-concrete-source-production-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-analytic-atlas-case2-concrete-source-production.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-analytic-atlas-case2-concrete-source-production-a4.md`.

Latest A4 selected-entry coordinate postdata:
`SelectedEntryNormalCrossing.lean` now proves the generic coordinate
equalities
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.coord_sourceChartPoint_eq`
and
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.coord_sourceChartTransitionPoint_eq`,
plus the Case 2 source-selected wrappers
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.coord_sourceChartPoint_eq_sourceSelected`
and
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.coord_sourceChartTransitionPoint_eq_sourceSelected`.
The coordinate is `u` at a source chart point and `u` times the normalized
target entry at a transition-generated target chart point.  This is finite
postdata only; no nonzero denominator, overlap, transition regularity,
analytic atlas, source production, Jacobian theorem, normal crossings, pole
order, termination, or RLCT result is proved.  Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-coordinate-postdata-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-coordinate-postdata.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-coordinate-postdata-a4.md`.

Latest A4 selected-entry source-point coverage with coordinate:
`SelectedEntryNormalCrossing.lean` now proves
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exists_sourceChartPoint_chartMap_eq_value_and_coord_zero_eq`.
This combines the existing finite source-point coverage theorem with the
coordinate projection for the same witness.  For any finite center value,
there are `c`, `u`, and `residual` such that the all-pivot certificate chart
map at `sourceChartPoint c u residual` is the value and coordinate
`(0 : Fin 1)` is `u`.  After xhigh review, no Case 1 wrapper was added because
it would be a thin specialization without an immediate consumer.  This is not
analytic coverage, transition regularity, source production, Jacobian control,
normal crossings, pole order, termination, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-source-point-coverage-coordinate-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-source-point-coverage-coordinate.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-source-point-coverage-coordinate-a4.md`.

Latest A6/A2 source-range rank-width bridge:
`Definition3RankWidthBridge.lean` now proves
`paperTotalMap_rank_le_layer_finrank`,
`paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth`, and
`AoyagiDefinition3SourceData.exists_selectedReducedWidthCeilData_of_sourceRankStratum`.
It derives `forall s, 1<=s -> s<=N+1 -> r<=H s` from the total product rank
field of `paperEndpointFixedBaseSourceRankStratum`, plus the explicit layer
dimension convention `H(k+1)=finrank K (W k)`, then feeds this into the
existing Definition 3 source-data ceiling constructor.  Selected cutpoints,
Definition 3 source data, exact-rank openness, finite exponent formulas,
normal crossings, pole order, and RLCT remain outside this theorem.
Reproduction:
`threads/06-dln-translation/reproduction-definition3-source-range-rank-width-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-source-range-rank-width.md`.
Review:
`threads/06-dln-translation/review-definition3-source-range-rank-width-a6.md`.

Latest A6 source-rank final handoff:
`Theorem2SourceRankFinalBridge.lean` and `Theorem2SourceRankEq5Bridge.lean`
now provide source-rank-stratum variants of the four existing Definition 3
final-boundary/Eq5 handoffs.  They specialize the final layer count to `N`,
derive the source-range rank-width hypothesis from
`paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth W B hx hH`, and
then call the existing `_of_rankWidth` wrappers.  They do not construct
selected cutpoints or Definition 3 source data, prove exact-rank openness,
construct Eq5 families, prove Lemma 5 exactness, active-ratio/chart-count
facts, chart production, normal crossings, pole order, or RLCT.  Reproduction:
`threads/06-dln-translation/reproduction-definition3-source-rank-final-handoff-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-source-rank-final-handoff.md`.
Review:
`threads/06-dln-translation/review-definition3-source-rank-final-handoff-a6.md`.

Latest A6 source-rank regular-shift final bridge:
`Theorem2SourceRankRegularShiftBridge.lean` now proves
`AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_sourceRankStratum_regularVariableCountShift`
and
`AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_sourceRankStratum_regularVariableCountShift`.
These compose Definition 3 source data, A2 source-rank-stratum provenance, and
the finite regular-variable shift into the existing supplied final sockets for
the shifted exponent datum/certificate.  The extraction hypothesis is for the
shifted object, and reduced minimum-plus-regular-term and reduced order
obligations remain supplied.  They do not construct the shifted certificate,
prove regular-suspension charts, transport analytic ideals, prove Aoyagi
Lemma 1, prove exact-rank openness, prove active-ratio/chart-count facts,
produce normal-crossing charts, identify pole order, or extract RLCT.
Reproduction:
`threads/06-dln-translation/reproduction-theorem2-source-rank-regular-shift-bridge-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-theorem2-source-rank-regular-shift-bridge.md`.
Review:
`threads/06-dln-translation/review-theorem2-source-rank-regular-shift-bridge-a6.md`.

Latest A6 Definition 3 selected/nonselected redundancy:
`Definition3Bridge.lean` now proves
`aoyagiDefinition3_selected_lt_of_selectedStrict_nonselectedLe` and
`AoyagiDefinition3SourceData.of_selectedStrict_nonselectedLe_rankWidth`.
The constructor derives the `selected_lt_nonselected` field from the strict
selected inequality, the nonselected upper inequality, and source-range
rank-width nonnegativity at selected cutpoints.  It still supplies selected
cutpoints, cutpoint bounds, rank-width, strict selected inequalities, and
nonselected upper inequalities; it does not prove selected-cutpoint existence
or `exists C, AoyagiDefinition3SourceData ... C`.  Reproduction:
`threads/06-dln-translation/reproduction-definition3-selected-lt-from-nonselected-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-selected-lt-from-nonselected.md`.
Review:
`threads/06-dln-translation/review-definition3-selected-lt-from-nonselected-a6.md`.

Latest A6 Definition 3 equal-width source data:
`Definition3Bridge.lean` now proves
`AoyagiDefinition3SourceData.exists_consecutive_of_constant_reducedWidth_pos`.
For the positive equal-width source-range profile, it constructs consecutive
cutpoints `C.cut j = j.val+1` with `ell=L` and proves
`AoyagiDefinition3SourceData L L H r C`.  This is source-data existence only
for Aoyagi's equal-width example.  It does not prove arbitrary selected
cutpoint existence, repair Definition 3's printed inequalities, construct Eq5
families, prove Lemma 5 exactness, produce charts, identify pole order, or
extract RLCT.  Reproduction:
`threads/06-dln-translation/reproduction-definition3-equal-width-source-data-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-equal-width-source-data.md`.
Review:
`threads/06-dln-translation/review-definition3-equal-width-source-data-a6.md`.

Latest A6 Definition 3 equal-width ceiling data:
`Definition3Bridge.lean` now proves
`AoyagiDefinition3SourceData.sourceRangeRankWidth_of_constant_reducedWidth`
and
`AoyagiDefinition3SourceData.exists_consecutive_selectedReducedWidthCeilData_of_constant_reducedWidth_pos`.
The first theorem derives source-range rank-width from the constant
Nat-valued reduced-width equality; the second packages that with the
equal-width source-data constructor and the existing selected reduced-width
ceiling-data theorem.  This removes repeated supplied rank-width/source-data
inputs in the equal-width lane only.  It proves no arbitrary selected-cutpoint
existence, no closed form for `ceilWidth` or `aParam`, no Eq5 payload, no
finite exponent formula, no chart production, no pole order, and no RLCT.
Reproduction:
`threads/06-dln-translation/reproduction-definition3-equal-width-ceil-data-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-equal-width-ceil-data.md`.
Review:
`threads/06-dln-translation/review-definition3-equal-width-ceil-data-a6.md`.

Latest A6 Definition 3 equal-width explicit ceiling data:
`Definition3Bridge.lean` now proves the explicit equal-width ceiling datum.
For a positive-remainder decomposition `w = L*q + a`, `0<a<=L`,
`AoyagiDefinition3CeilData.equalWidthOfDecomposition` constructs the constant
selected-width datum with `ceilWidth = w+q+1` and `aParam = a`.  The
source-facing theorem
`AoyagiDefinition3SourceData.exists_consecutive_explicitCeilData_of_constant_reducedWidth_decomposition`
combines this with the consecutive equal-width source data and returns the
standard selected reduced-width package with explicit fields.  This is finite
equal-width arithmetic only: it does not prove arbitrary source-data
existence, uniqueness of the ceiling datum, automatic construction of the
decomposition, Eq5 payloads, charts, pole order, or RLCT.  Reproduction:
`threads/06-dln-translation/reproduction-definition3-equal-width-explicit-ceil-data-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-equal-width-explicit-ceil-data.md`.
Review:
`threads/06-dln-translation/review-definition3-equal-width-explicit-ceil-data-a6.md`.

Latest A6 Definition 3 equal-width finite Theorem 2 formula:
`FinalFormula.lean` now proves `aoyagiSelectedWidthPairCount_cast` and
`aoyagiSelectedWidthPairSum_const`, and `Definition3Bridge.lean` proves
`AoyagiDefinition3SourceData.exists_consecutive_equalWidth_theorem2Formula_of_constant_reducedWidth_decomposition`.
For the source-backed equal-width branch with `ell=L`, `m_j=w`, and
`w=L*q+a`, `0<a<=L`, Lean constructs consecutive source data and returns
explicit ceiling data, order `a*(L-a)+1`, pair sum
`((L+1)*L*w^2)/2`, and the unfolded finite lambda formula with pair
contribution `((L+1)*L*w^2)/4`.

Artifacts:
`threads/06-dln-translation/reproduction-definition3-equal-width-theorem2-formula-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-equal-width-theorem2-formula.md`.
Review:
`threads/06-dln-translation/review-definition3-equal-width-theorem2-formula-a6.md`.

Nonclaims: restricted finite formula arithmetic only.  No arbitrary Definition
3 branch selection, no Eq5 payload, no chart production, no normal crossings,
no pole order, and no RLCT.

Latest A6 Definition 3 positive-remainder ceiling data:
`Definition3Bridge.lean` now proves
`AoyagiDefinition3CeilData.ofSelectedSumPositiveRemainder`.  For a supplied
positive-remainder decomposition
`sum_j m_j = ell * ceilPred + a` with `0<a<=ell`, it constructs the
Definition 3 ceiling datum with `ceilWidth = ceilPred+1` and `aParam = a`.
This is pure finite arithmetic; no source-facing wrapper was added until a
downstream theorem needs explicit field projections.  Reproduction:
`threads/06-dln-translation/reproduction-definition3-positive-remainder-ceil-data-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-positive-remainder-ceil-data.md`.
Review:
`threads/06-dln-translation/review-definition3-positive-remainder-ceil-data-a6.md`.

Latest A6 Definition 3 `L=2` repeated-width classification:
`Definition3Bridge.lean` now proves
`AoyagiDefinition3SourceData.exists_sourceData_iff_repeatedPositive_or_triangle_of_L_eq_two`,
plus the supporting rank-width-free `ell=1` necessary condition and
positive repeated constructor.  Bare source-data existence for `L=2` is
equivalent to either positive repeated reduced-width values or the all-source
triangle inequalities.  This is finite Definition 3 source-data structure
only; no rank-width hypothesis is required, and no ceiling package, Eq5
payload, chart production, pole order, or RLCT is proved.  Reproduction:
`threads/06-dln-translation/reproduction-definition3-l-eq-two-repeated-width-classification-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-l-eq-two-repeated-width-classification.md`.
Review:
`threads/06-dln-translation/review-definition3-l-eq-two-repeated-width-classification-a6.md`.

Latest A2 supplied regular-suspension interface:
Proved finite boundary/projection only.  The claim is that if a supplied full
normal-crossing chart certificate `Cfull` and a reduced certificate `Cred`
satisfy

```text
Cfull.exponentData =
  Cred.exponentData.jacobianPriorLossShift regularCount,
```

then the full finite exponent minimum/order are obtained from the reduced
ones by the existing finite shift arithmetic.  If
`regularCount = aoyagiTheorem2RegularVariableCount L H r`, endpoint bounds
identify the minimum shift with Aoyagi's regular term.  With extraction
supplied for `Cfull`, Lean builds the existing
`AoyagiTheorem2SuppliedChartFinalBoundary Cfull ...`.

Lean names:
`AoyagiSuppliedRegularSuspensionBoundary`,
`AoyagiSuppliedRegularSuspensionCertificate`,
`AoyagiSuppliedRegularSuspensionBoundary.full_exponentMinimum_eq_reduced_add_half_regularCount`,
`AoyagiSuppliedRegularSuspensionBoundary.full_exponentOrder_eq_reduced`,
`AoyagiSuppliedRegularSuspensionBoundary.full_exponentMinimum_eq_reduced_add_regularTerm`,
`AoyagiSuppliedRegularSuspensionBoundary.theorem2FiniteExponentFormulaHypothesis_of_regularVariableCount`,
and
`AoyagiSuppliedRegularSuspensionCertificate.theorem2SuppliedChartFinalBoundary_of_regularVariableCount`.

Nonclaims: no construction of `Cfull`, no proof of the abstract
source/ideal/coverage/Jacobian predicates, no analytic ideal transport,
no Aoyagi Lemma 1, no regular-coordinate additivity, no normal-crossing
production, no pole-order theorem, and no RLCT theorem beyond extraction for
the supplied full certificate.

Latest A2 canonical product-difference regular-chart source:
Proved a narrow source-predicate specialisation of the supplied
regular-suspension boundary.  The new predicate is the existing A2 local
source certificate

```text
PaperEndpointCanonicalProductDifferenceLocalSourceCertificate W B x0 Cedge r rEdge
```

viewed as `RegularChartSource Cred Cfull regularCount`.  The constructor
builds `AoyagiSuppliedRegularSuspensionBoundary` for this specialised source
predicate from that local source certificate plus supplied ideal transport,
coverage, Jacobian compatibility, and exponent-shift equality.

Lean names:
`AoyagiCanonicalProductDifferenceRegularChartSource` and
`AoyagiSuppliedRegularSuspensionBoundary.of_canonicalProductDifferenceRegularChartSource`.

Nonclaims: no scalar regular-coordinate list, no regular-count proof, no
construction of `Cfull`, no analytic ideal/germ transport, no chart coverage,
no Jacobian compatibility, no exponent-shift proof, no normal-crossing
production, no pole-order theorem, and no RLCT theorem.

Latest A2 regular-suspension coordinate index:
Proved the finite scalar-coordinate index for the p. 13 regular block
families.  The index is the disjoint union of entries of `Ctop - 1`, `F2`, and
`F3`, and its card is

```text
card ι * card ι + card ι * card ν + card μ * card ι.
```

Under explicit endpoint-cardinality equalities this rewrites to
`aoyagiTheorem2RegularVariableCount L H r`.  The endpoint-compatible theorem
derives the row/left and column/right residual cardinalities from the
fixed-base endpoint complement construction, base product rank, and dimension convention.
The local-certificate theorem projects centered continuity of `S.Ctop - 1`,
`-S.B`, and `lowerLeftBlock S.L` to every scalar coordinate.

Lean names:
`AoyagiRegularBlockCoordinateIndex`,
`AoyagiRegularBlockCoordinateIndex.card_eq_aoyagiTheorem2RegularVariableCount`,
`paperEndpointEndpointComplementIndex_card_eq_layerSubRank`,
`paperEndpointRegularBlockCoordinateIndex_card_eq_regularVariableCount`,
and
`PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.regularBlockScalarCoordinates_centered_continuousAt`,
`PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.regularBlockCoordinateIndex_card_eq_regularVariableCount`.

Nonclaims: no analytic regular-coordinate construction, no `Cfull`
construction, no four-block ideal split, no ideal transport, no coverage, no
Jacobian compatibility, no exponent shift, no normal-crossing production, no
pole-order theorem, and no RLCT theorem.

Latest A2 regular/residual ideal split:
Proved the scalar ideal regrouping behind the p. 13 regular/residual
separation.  The regular block-entry ideal is

```text
regularBlockEntryIdeal X F2 F3 =
  matrixEntryIdeal X ⊔ matrixEntryIdeal F2 ⊔ matrixEntryIdeal F3.
```

The four-block ideal splits definitionally as

```text
fourMatrixEntryIdeal X F2 F3 D =
  regularBlockEntryIdeal X F2 F3 ⊔ matrixEntryIdeal D.
```

The fixed-base canonical corollary applies this to
`S.Ctop - 1`, `-S.B`, `lowerLeftBlock S.L`, and residual `S.D`.

Lean names:
`regularBlockEntryIdeal`,
`fourMatrixEntryIdeal_eq_regularBlockEntryIdeal_sup_matrixEntryIdeal`,
`matrixEntryIdeal_triangularBlockProductDifference_eq_regular_sup_residual`,
`ChartLocalSuffixState.productDifferenceEntryIdeal_eq_regularBlockEntryIdeal_sup_matrixEntryIdeal`, and
`PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks.canonicalProductDifferenceEntryIdeal_eq_regularBlockEntryIdeal_sup_matrixEntryIdeal`.

Nonclaims: no analytic germ-ideal transport, no regular-suspension chart
construction, no coverage, no Jacobian compatibility, no normal crossings, no
pole-order theorem, and no RLCT theorem.  The residual `D` block remains
outside the regular-coordinate index.

Latest A2 regular-coordinate ideal bridge:
Proved that the scalar regular-coordinate values generate exactly the regular
block-entry ideal:

```text
AoyagiRegularBlockCoordinateIndex.entryIdeal X F2 F3 =
  regularBlockEntryIdeal X F2 F3.
```

Lean names:
`AoyagiRegularBlockCoordinateIndex.entryIdeal` and
`AoyagiRegularBlockCoordinateIndex.entryIdeal_eq_regularBlockEntryIdeal`, plus
`PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks.canonicalProductDifferenceEntryIdeal_eq_regularCoordinateIdeal_sup_matrixEntryIdeal`.

Nonclaims: no residual `D` coordinate in the scalar regular-coordinate ideal,
no analytic regular-coordinate chart, no analytic ideal/germ transport, no
coverage, no Jacobian compatibility, no normal-crossing production, no
pole-order theorem, and no RLCT theorem.

Latest A2 local source regular-coordinate ideal split:
Proved a local source-neighborhood version of the scalar regular/residual
ideal split.  From a
`PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate`, Lean
produces a neighborhood `U` such that every point in `U` lying in the
source-shaped rank stratum satisfies

```text
matrixEntryIdeal(productDifference)
  =
AoyagiRegularBlockCoordinateIndex.entryIdeal
  (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) ⊔ matrixEntryIdeal S.D.
```

Lean name:
`PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_regularCoordinateIdeal_source_neighborhood`.

Nonclaims: no source-rank openness, no analytic germ-ideal transport, no
regular-suspension chart construction, no coverage, no Jacobian compatibility,
no normal-crossing production, no pole-order theorem, and no RLCT theorem.

Latest A2 regular-coordinate ideal source predicate:
Proved the source-obligation packaging for a later supplied
regular-suspension chart.  The fixed-base predicate
`PaperEndpointFixedBaseRegularCoordinateIdealSourceNeighborhood` records the
same source-stratum guarded scalar regular-coordinate/residual ideal split as a
named source-side condition.  The regular-suspension predicate
`AoyagiCanonicalProductDifferenceRegularCoordinateIdealSource` existentially
chooses the fixed endpoint-base certificate and carries both the local source
certificate and that named neighborhood predicate.

Lean names:
`PaperEndpointFixedBaseRegularCoordinateIdealSourceNeighborhood`,
`PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.regularCoordinateIdealSourceNeighborhood`,
`AoyagiCanonicalProductDifferenceRegularCoordinateIdealSource`,
`aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource_of_localSourceCertificate`,
and
`AoyagiSuppliedRegularSuspensionBoundary.of_canonicalProductDifferenceRegularCoordinateIdealSource`.

Nonclaims: no source-rank openness, no analytic germ-ideal transport, no
construction of `Cfull`, no coverage, no Jacobian compatibility, no proof of
the finite exponent shift, no normal-crossing production, no pole-order
theorem, and no RLCT theorem.  The boundary constructor fills only
`regular_chart_source`; ideal transport, coverage, Jacobian compatibility, and
exponent shift remain supplied.

Latest A2 regular-coordinate ideal source existence:
Proved the raw-hypothesis constructor for the stronger source predicate.
From a continuous reversed-edge family based at `B`, supplied product rank,
supplied edge ranks, and supplied bounds `r <= rEdge p`, Lean builds
`AoyagiCanonicalProductDifferenceRegularCoordinateIdealSource` by composing
the canonical local source-certificate existence theorem with the
regular-coordinate ideal source predicate.

Lean name:
`exists_aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource`.

Nonclaims: no source-rank openness, no analytic germ-ideal transport, no
construction of `Cfull`, no ideal transport, no coverage, no Jacobian
compatibility, no exponent shift, no normal-crossing production, no pole-order
theorem, and no RLCT theorem.  The base inequality `r <= rEdge p` is still an
explicit input here; deriving it from rank equalities is the next A2
rank-bound target.

Latest A2 base product rank bounded by edge ranks:
Proved the finite-dimensional rank inequality saying the base total product
has rank at most every base edge rank.  Lean factors the reversed total product
through each edge and applies rank-of-composite inequalities.

Lean names:
`paperTotalMap_finrank_range_le_reverseEdge_finrank_range`,
`paperEndpointFixedBaseSourceRankStratum_selfBase_mem_of_rank_eq`,
`paperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate_of_isCompl_of_rank_eq`,
`exists_paperEndpointCanonicalProductDifferenceLocalSourceCertificate_of_rank_eq`,
and
`exists_aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource_of_rank_eq`.

Nonclaims: no exact-rank or source-rank openness, no analytic germ-ideal
transport, no construction of `Cfull`, no ideal transport, no coverage, no
Jacobian compatibility, no exponent shift, no normal-crossing production, no
pole-order theorem, and no RLCT theorem.

Latest A6 Theorem 2 supplied regular-suspension final bridge:
Proved chart-final handoff only.  Given Definition 3 source data, source-range
rank-width, a supplied regular-suspension certificate, the explicit regular
count equality, and reduced min/order obligations for each produced
`m,data`, Lean returns

```text
AoyagiTheorem2SuppliedChartFinalBoundary
  Cfull L ell H r C m data lambda poleOrder.
```

The source-rank theorem is a delegating wrapper that derives source-range
rank-width from `paperEndpointFixedBaseSourceRankStratum`.

Lean names:
`AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_suppliedRegularSuspension`
and
`AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_sourceRankStratum_suppliedRegularSuspension`.

Nonclaims: no bare exponent-data final-boundary theorem, no construction of
source data, no construction of `Cfull`, no proof of abstract
regular-suspension predicates, no analytic ideal transport, no Aoyagi
Lemma 1, no regular-coordinate additivity, no normal-crossing production, no
active-ratio/chart-count proof, no pole-order theorem, and no RLCT theorem
beyond extraction for `Cfull`.

Latest A2 fixed-base suffix-state field continuity handoff:
Proved a fixed-base endpoint-coordinate consumer of the generic suffix-state
continuity API.  From a continuous reversed-edge family `Cedge` and recursive
determinant-chart hypotheses at `x0`, Lean builds the fixed-base matrix
family and returns the basepoint `IsUnit Ctop.det` invariant plus
`ContinuousAt` for the deterministic suffix-state fields `L`, `B`, `Ctop`,
and `D` for every suffix ending at `Fin.last N`.

Lean name:
`paperEndpointFixedBaseContinuousEdges_recursiveSuffixState_fields_continuousAt`.

Nonclaims: no analytic regularity, no exact-rank/source-rank openness, no
chart coverage, no regular suspension, no ideal transport, no normal-crossing
production, no pole-order theorem, and no RLCT theorem.

Latest A2 canonical deterministic product-difference coefficient fields:
Proved a rank-free scalar entry-ideal handoff that uses the deterministic
suffix-state fields directly.  From a suffix-state block-diagonal invariant,
Lean derives the p. 13 product-difference entry-ideal equality with

```text
F2 = -S.B,  F3 = lowerLeftBlock S.L,  Ctop = S.Ctop,  D = S.D.
```

Lean names:
`ChartLocalSuffixState.productDifferenceEntryIdeal_eq_fourMatrixEntryIdeal`
and
`PaperEndpointFixedBaseProductReductionCertificate.productDifferenceEntryIdeal_eq_fourMatrixEntryIdeal_canonicalFields`.

Nonclaims: no source-rank wrapper, no exact-rank/source-rank openness, no
analytic regularity, no analytic germ-ideal transport, no chart coverage, no
normal-crossing production, no pole-order theorem, and no RLCT theorem.

Latest A2 canonical product-difference coefficient-field continuity:
Proved that the deterministic p. 13 coefficient fields are continuous
fixed-base local functions, and that they vanish at the self-base chain.  The
fields are

```text
S.Ctop - 1,  -S.B,  lowerLeftBlock S.L,  S.D.
```

Lean names:
`paperEndpointFixedBaseContinuousEdges_productDifferenceCoefficientFields_continuousAt`,
`paperEndpointFixedBaseContinuousEdges_selfBase_productDifferenceCoefficientFields_continuousAt`,
and
`paperEndpointFixedBaseContinuousEdges_selfBase_productDifferenceCoefficientFields_centered_continuousAt`.

The explicit-chart theorem assumes recursive determinant-chart hypotheses; the
self-base variants derive them from the base equality with the original
reversed chain.  Centering is proved by rewriting the self-base total matrix
as `fromBlocks 1 0 0 0`, using the lower-unitriangular form of the suffix
multiplier, and comparing blocks.

Reproduction:
`threads/03-block-product-reduction/reproduction-a2-canonical-product-difference-field-continuity.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-canonical-product-difference-field-continuity.md`.
Review:
`threads/03-block-product-reduction/review-a2-canonical-product-difference-field-continuity.md`.

Nonclaims: no analytic regularity, no exact-rank/source-rank openness, no
chart coverage, no analytic ideal or germ transport, no regular-suspension
certificate, no normal-crossing production, no pole-order theorem, and no RLCT
theorem.

Latest A2 canonical product-difference local certificate:
Proved a fixed-base local package binding the centered continuous canonical
fields to the pointwise product-difference/source-rank boundary.  The
pointwise predicate uses

```text
fourMatrixEntryIdeal (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) S.D
```

and records the residual-rank formulas `rank residualBlock_p = rEdge p - r`.
The local statement is relative to the source-shaped rank stratum via
`nhdsWithin`.

Lean names:
`PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks`,
`PaperEndpointFixedBaseProductReductionCertificate.toCanonicalProductDifferenceSourceRanks`,
`paperEndpointFixedBaseCanonicalProductDifferenceSourceRanks_selfBase_mem_nhdsWithin_source`,
`PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate`,
`paperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate_of_isCompl`,
`PaperEndpointCanonicalProductDifferenceLocalCertificate`, and
`exists_paperEndpointCanonicalProductDifferenceLocalCertificate`.

Reproduction:
`threads/03-block-product-reduction/reproduction-a2-canonical-product-difference-local-certificate.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-canonical-product-difference-local-certificate.md`.
Review:
`threads/03-block-product-reduction/review-a2-canonical-product-difference-local-certificate.md`.

Nonclaims: no exact-rank/source-rank openness, no analytic regularity, no
chart coverage, no analytic ideal or germ transport, no regular-suspension
certificate, no normal-crossing production, no pole-order theorem, and no RLCT
theorem.

Latest A6 Definition 3 `L=2` all-source triangle formula package:
Proved the explicit finite formula package for the all-source triangle branch.
Given reduced widths `w1,w2,w3`, the three strict triangle inequalities, a
source-range rank-width hypothesis, and a supplied positive-remainder
decomposition

```text
w1+w2+w3 = 2*ceilPred+a,  0<a<=2,
```

Lean constructs consecutive source data and explicit ceiling data with
`ceilWidth = ceilPred+1` and `aParam = a`, and proves the order formula,
selected pair sum, and finite Theorem 2 lambda expression.

Lean name:
`AoyagiDefinition3SourceData.exists_consecutive_three_widths_theorem2Formula_of_triangle_remainder_rankWidth`.

Nonclaims: no source-rank wrapper, no final socket, no repeated-positive
`ell=1` branch, no Eq5 payloads, no chart production, no pole-order theorem,
and no RLCT theorem.

Latest A6 Definition 3 `L=2`, `ell=1` selected-pair formula package:
Proved the safe repeated-positive finite formula interface.  The theorem
exposes the selected pair `C : AoyagiSelectedCutpoints 1` and assumes positive
selected values, selected-value cover, source-range rank-width, and
`u+v=ceilPred+1`.  It constructs source data and explicit ceiling data with
`ceilWidth=ceilPred+1`, `aParam=1`, and proves order `1`, pair sum `u*v`, and
finite lambda `regularTerm+u*v/2`.

Lean name:
`AoyagiDefinition3SourceData.exists_ell_one_selectedPair_theorem2Formula_of_cover_remainder_rankWidth`.

Nonclaims: no canonical repeated-branch formula, no source-rank wrapper, no
final socket, no Eq5 payloads, no chart production, no pole-order theorem, and
no RLCT theorem.

Latest A6 Definition 3 `ell=1` automatic ceiling and `L=2`
repeated-positive formula package:
Proved a source-moving finite refinement of the selected-pair formula.  The
new preferred exposed-pair theorem constructs the `ell=1` ceiling datum
directly:

```text
ceilWidth = u+v,
aParam = 1.
```

It proves order `1`, pair sum `u*v`, and finite lambda
`regularTerm+u*v/2` without a supplied `ceilPred` equation.  The
repeated-positive theorem then uses the `L=2` repeated-width branch to select
an `ell=1` pair by cases and returns the pair existentially.

Lean names:
`AoyagiDefinition3SourceData.exists_ell_one_selectedPair_theorem2Formula_of_cover_rankWidth`
and
`AoyagiDefinition3SourceData.exists_ell_one_theorem2Formula_of_L_eq_two_positive_repeated_rankWidth`.

The older
`AoyagiDefinition3SourceData.exists_ell_one_theorem2Formula_of_L_eq_two_positive_repeated_remainder_rankWidth`
is compatibility only.  Nonclaims: no unique/canonical selected pair, no
source-rank wrapper, no final socket, no Eq5 payloads, no chart production, no
pole-order theorem, and no RLCT theorem.

Latest A6 Definition 3 general `L`, `ell=1` selected-pair formula package:
Proved the arbitrary-depth version of the exposed-pair finite formula API.
The selected pair `C : AoyagiSelectedCutpoints 1` remains supplied, together
with positive selected values, value-level source-range cover, and source-range
rank-width.  Lean constructs Definition 3 source data, direct `ell=1` ceiling
data with

```text
ceilWidth = u+v,
aParam = 1,
```

and proves order `1`, pair sum `u*v`, Nat-width/nonnegativity/strictness
provenance, and finite lambda
`aoyagiTheorem2RegularTerm L H r + u*v/2`.

Lean name:
`AoyagiDefinition3SourceData.exists_ell_one_selectedPair_theorem2Formula_of_cover_rankWidth_general`.

Nonclaims: no canonical selected pair, no branch-independent formula for
arbitrary Definition 3 source data, no source-rank wrapper, no final socket, no
Eq5 payloads, no chart production, no pole-order theorem, and no RLCT theorem.

Latest A6 Definition 3 `ell=1` ceiling-data simplification:
Proved constructor-independent finite arithmetic for any
`AoyagiDefinition3CeilData 1 m`.  The residue bounds force `aParam=1`; the
selected-sum identity then gives `ceilWidth=sum_j m_j`; the order formula is
`1`; and the finite lambda formula simplifies to
`regularTerm + aoyagiSelectedWidthPairSum 1 m / 2`.  If the two selected
widths are `u,v`, the lambda formula is `regularTerm+u*v/2`.

Lean names:
`AoyagiDefinition3CeilData.aParam_eq_one_of_ell_eq_one`,
`AoyagiDefinition3CeilData.selectedSum_eq_ceilWidth_of_ell_eq_one`,
`AoyagiDefinition3CeilData.ceilWidth_eq_selectedSum_of_ell_eq_one`,
`AoyagiDefinition3CeilData.theorem2OrderFormula_eq_one_of_ell_eq_one`,
`AoyagiDefinition3CeilData.theorem2Lambda_fromCeilData_eq_regularTerm_add_pairSum_half_of_ell_eq_one`,
and
`AoyagiDefinition3CeilData.theorem2Lambda_fromCeilData_eq_regularTerm_add_selectedPair_half_of_ell_eq_one`.

Nonclaims: no selected-cutpoint/source-data construction, no branch choice, no
final-socket wrapper, no Eq5 payloads, no chart production, no pole-order
theorem, and no RLCT theorem.

Latest A6 Definition 3 `L=2` triangle parity formula package:
Proved a finite refinement of the all-source triangle formula package that
removes the supplied positive-remainder decomposition when parity is known.
For `T=w1+w2+w3`, the odd branch gives

```text
ceilWidth = T/2 + 1,
aParam = 1,
order = 2,
```

and the even branch gives

```text
ceilWidth = T/2,
aParam = 2,
order = 1.
```

Lean names:
`AoyagiDefinition3SourceData.exists_consecutive_three_widths_theorem2Formula_of_triangle_odd_rankWidth`
and
`AoyagiDefinition3SourceData.exists_consecutive_three_widths_theorem2Formula_of_triangle_even_rankWidth`.

Nonclaims: no `L>2` classification, no combined repeated/triangle theorem, no
source-rank wrapper, no final socket, no Eq5 payloads, no chart production, no
pole-order theorem, and no RLCT theorem.

Latest A2 regular-coordinate source data:
Proved a fixed-base source-data package for Aoyagi's p. 13 regular-coordinate
separation.  From a continuous reversed-edge family based at `B`, base product
rank `r`, base edge ranks `rEdge`, and the layer-dimension convention, Lean
chooses a total-kernel complement and packages the local source certificate,
the source-stratum guarded regular/residual ideal split, centered continuous
scalar regular coordinates, centered continuous scalar residual coordinates,
the cardinality equality with `aoyagiTheorem2RegularVariableCount N H r`, and
the residual endpoint entry count `(H 1-r)*(H(N+1)-r)`.

Lean names:
`PaperEndpointFixedBaseRegularBlockScalarCoordinatesCenteredContinuousAt`,
`PaperEndpointFixedBaseResidualBlockScalarCoordinatesCenteredContinuousAt`,
`AoyagiResidualBlockCoordinateIndex`,
`PaperEndpointFixedBaseRegularCoordinateSourceData`,
`PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.regularCoordinateSourceData`,
and
`exists_paperEndpointFixedBaseRegularCoordinateSourceData_of_rank_eq`.

Nonclaims: no exact-rank or source-rank openness, no analytic germ-ideal
transport, no regular-suspension chart construction, no coverage, no Jacobian
compatibility, no exponent shift, no normal crossings, no pole-order theorem,
and no RLCT theorem.

Latest A2 product-difference coordinate source data:
Lean now packages the cleaned p. 13 product-difference ideal-level family as
`AoyagiProductDifferenceCoordinateIndex`, combining the regular scalar
coordinates for `S.Ctop - 1`, `-S.B`, and `lowerLeftBlock S.L` with the
residual scalar coordinates for `S.D`.  It proves the combined scalar ideal is
the cleaned four-block entry ideal, projects centered continuity, exposes a
source-stratum guarded product-difference coordinate ideal neighborhood, and
adds the endpoint product-entry count `H 1 * H(N+1)` to
`PaperEndpointFixedBaseRegularCoordinateSourceData`.

Lean names:
`AoyagiProductDifferenceCoordinateIndex`,
`AoyagiProductDifferenceCoordinateIndex.entryIdeal_eq_fourMatrixEntryIdeal`,
`AoyagiProductDifferenceCoordinateIndex.matrixEntryIdeal_fromBlocks_neg_neg_sub_mul_eq_entryIdeal`,
`AoyagiProductDifferenceCoordinateIndex.value_centered_continuousAt`,
`AoyagiProductDifferenceCoordinateIndex.card_eq_endpointProductEntryCount`,
`paperEndpointProductDifferenceCoordinateIndex_card_eq_endpointProductEntryCount`,
`PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks.canonicalProductDifferenceEntryIdeal_eq_productDifferenceCoordinateIdeal`,
`PaperEndpointFixedBaseProductDifferenceCoordinateIdealSourceNeighborhood`,
`PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_productDifferenceCoordinateIdeal_source_neighborhood`,
`PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.productDifferenceScalarCoordinates_centered_continuousAt`,
and
`PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.productDifferenceCoordinateIndex_card_eq_endpointProductEntryCount`.

Nonclaims: no exact-rank or source-rank openness, no analytic coordinate
chart, no regular-suspension chart construction, no analytic germ-ideal
transport, no coverage, no transition regularity, no Jacobian compatibility,
no normal crossings, no pole-order theorem, and no RLCT theorem.

Latest A2 literal product-difference coordinate ideal bridge:
Lean now proves
`AoyagiProductDifferenceCoordinateIndex.matrixEntryIdeal_fromBlocks_neg_neg_sub_mul_eq_entryIdeal`.
It directly identifies the matrix-entry ideal of the literal signed/corrected
p. 13 block `fromBlocks X (-F2) (-F3) (D - F3*F2)` with
`AoyagiProductDifferenceCoordinateIndex.entryIdeal X F2 F3 D`.  This composes
the existing signed-block cleanup with
`AoyagiProductDifferenceCoordinateIndex.entryIdeal_eq_fourMatrixEntryIdeal`.
The only finiteness input is the summation index in `F3*F2`, and the
correction is `F3*F2`, not `F2*F3`.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-literal-product-difference-coordinate-ideal-bridge.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-literal-product-difference-coordinate-ideal-bridge.md`.
Review:
`threads/03-block-product-reduction/review-a2-literal-product-difference-coordinate-ideal-bridge.md`.

Latest A2 regular-suspension coordinate map source data:
Lean now packages the existing scalar p. 13 source-data fields as Pi-valued
coordinate maps for the regular block coordinates, the residual `D` block, and
the combined cleaned product-difference coordinate family.  From
`PaperEndpointFixedBaseRegularCoordinateSourceData`, Lean proves each map
vanishes at the base point and is continuous there.  This is only the
componentwise product-topology repackaging of the already proved scalar
centered-continuity fields.

Lean names:
`paperEndpointFixedBaseRegularBlockCoordinateMap`,
`paperEndpointFixedBaseResidualBlockCoordinateMap`,
`paperEndpointFixedBaseProductDifferenceCoordinateMap`,
`PaperEndpointFixedBaseRegularCoordinateSourceData.regularBlockCoordinateMap_centered_continuousAt`,
`PaperEndpointFixedBaseRegularCoordinateSourceData.residualBlockCoordinateMap_centered_continuousAt`,
and
`PaperEndpointFixedBaseRegularCoordinateSourceData.productDifferenceCoordinateMap_centered_continuousAt`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-regular-suspension-coordinate-map-source-data.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-regular-suspension-coordinate-map-source-data.md`.
Review:
`threads/03-block-product-reduction/review-a2-regular-suspension-coordinate-map-source-data.md`.

Nonclaims: no analytic coordinate chart, no local inverse, no source-rank
openness, no analytic germ-ideal transport, no chart coverage, no Jacobian
compatibility, no normal crossings, no pole-order theorem, and no RLCT theorem.

Latest A2 cleaned coordinate square-sum:
Lean now names the finite algebraic square-sum attached to a scalar coordinate
family and proves that the cleaned p. 13 product-difference coordinate family
splits as regular square-sum plus residual square-sum.  The fixed-base
product-difference coordinate map is also identified with `Sum.elim` of the
regular and residual coordinate maps, so the same square-sum split holds for
the source-side maps.

Lean names:
`aoyagiCoordinateSquareSum`,
`aoyagiCoordinateSquareSum_sumElim`,
`AoyagiProductDifferenceCoordinateIndex.coordinateSquareSum_eq_regular_add_residual`,
`paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_sumElim`,
and
`paperEndpointFixedBaseProductDifferenceCoordinateMap_squareSum_eq_regular_add_residual`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-cleaned-coordinate-square-sum.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-cleaned-coordinate-square-sum.md`.
Review:
`threads/03-block-product-reduction/review-a2-cleaned-coordinate-square-sum.md`.

Nonclaims: no equality with the literal signed/corrected p. 13 Frobenius loss,
no analytic generator transport or loss comparability, no analytic coordinate
chart, no chart coverage, no Jacobian compatibility, no normal crossings, no
pole-order theorem, and no RLCT theorem.

Latest A2 literal product-difference square-sum:
Lean now names the scalar coordinate family attached to the literal
signed/corrected p. 13 block
`fromBlocks X (-F2) (-F3) (D - F3*F2)` and proves its finite square-sum splits
as the regular square-sum plus the corrected residual square-sum for
`D - F3*F2`.

Lean names:
`AoyagiProductDifferenceCoordinateIndex.literalValue`,
`AoyagiProductDifferenceCoordinateIndex.literalValue_regular`,
`AoyagiProductDifferenceCoordinateIndex.literalValue_residual`, and
`AoyagiProductDifferenceCoordinateIndex.literalCoordinateSquareSum_eq_regular_add_correctedResidual`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-literal-product-difference-square-sum.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-literal-product-difference-square-sum.md`.
Review:
`threads/03-block-product-reduction/review-a2-literal-product-difference-square-sum.md`.

Nonclaims: no comparison between `D - F3*F2` and `D`, no local loss
comparability, no analytic generator transport, no regular-coordinate chart
construction, no Jacobian compatibility, no normal crossings, no pole-order
theorem, and no RLCT theorem.

Latest A2 finite literal-vs-cleaned loss comparison:
Lean proves finite ordered-ring square-sum comparison between the literal
signed/corrected p. 13 square-sum and the cleaned square-sum.  It first proves
finite coordinatewise sum/subtraction estimates, splits the regular
square-sum into the `X`, `F2`, and `F3` block square-sums, proves the
row-column Cauchy-Schwarz estimate
`squareSum(F3*F2) <= squareSum(F3) * squareSum(F2)`, and derives
`4*squareSum(F3*F2) <= regularSquareSum` from
`squareSum(F2)+squareSum(F3) <= 1`.  Under this hypothesis, Lean proves
factor-`2` comparison in both directions between the literal and cleaned
finite square-sums.

Lean names include
`AoyagiProductDifferenceCoordinateIndex.productCorrectionSquareSum_le_f3SquareSum_mul_f2SquareSum`,
`AoyagiProductDifferenceCoordinateIndex.four_mul_productCorrectionSquareSum_le_regular_of_f2_f3_squareSum_add_le_one`,
`AoyagiProductDifferenceCoordinateIndex.literalCoordinateSquareSum_le_two_mul_coordinateSquareSum_of_f2_f3_squareSum_add_le_one`,
and
`AoyagiProductDifferenceCoordinateIndex.coordinateSquareSum_le_two_mul_literalCoordinateSquareSum_of_f2_f3_squareSum_add_le_one`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-regular-suspension-loss-comparison-and-fubini-boundary.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-regular-suspension-loss-comparison-and-fubini-boundary.md`.
Review:
`threads/03-block-product-reduction/review-a2-regular-suspension-loss-comparison-and-fubini-boundary.md`.

Latest A2 continuity-to-small-loss neighborhood:
Lean proves the generic real topology behind the finite comparison's smallness
hypothesis.  For finite real coordinate families, centered `ContinuousAt`
implies eventually in the ambient filter `nhds x0` that the square-sum is at
most `1`; for two centered families, the sum of their square-sums is eventually
at most `1`.

Lean names:
`aoyagiCoordinateSquareSum_continuousAt`,
`aoyagiCoordinateSquareSum_eventually_le_one_of_continuousAt_zero`, and
`aoyagiCoordinateSquareSum_add_eventually_le_one_of_continuousAt_zero`, plus
the coordinatewise-data wrappers
`aoyagiCoordinateSquareSum_eventually_le_one_of_forall_centered_continuousAt`
and
`aoyagiCoordinateSquareSum_add_eventually_le_one_of_forall_centered_continuousAt`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-continuity-to-small-loss-neighborhood.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-continuity-to-small-loss-neighborhood.md`.
Review:
`threads/03-block-product-reduction/review-a2-continuity-to-small-loss-neighborhood.md`.

Nonclaims: no p. 13 source-stratum wrapper for the generic real neighborhood
shrink, no analytic coordinate chart, no Fubini/polar theorem, no
regular-coordinate RLCT shift, no chart coverage, no Jacobian compatibility,
no normal crossings, no pole-order theorem, and no RLCT theorem.

Latest A2 regular-coordinate F2/F3 smallness projection:
Lean specialises the generic two-family smallness theorem to the p. 13
regular-coordinate tags.  If every coordinate in
`AoyagiRegularBlockCoordinateIndex iota mu nu` is centered and continuous at
`x0`, then eventually in ambient `nhds x0` the `F2` and `F3` tagged
subfamilies have total square-sum at most `1`.

Lean name:
`AoyagiRegularBlockCoordinateIndex.f2_f3_squareSum_eventually_le_one_of_forall_centered_continuousAt`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-regular-coordinate-f2-f3-smallness-projection.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-regular-coordinate-f2-f3-smallness-projection.md`.
Review:
`threads/03-block-product-reduction/review-a2-regular-coordinate-f2-f3-smallness-projection.md`.

Nonclaims: no fixed-base source-data wrapper, no source-stratum neighborhood,
no analytic regular-coordinate status, no Fubini/polar shift, no chart
coverage, no Jacobian compatibility, no normal crossings, no pole-order
theorem, and no RLCT theorem.

Latest A2 fixed-base regular-coordinate F2/F3 smallness:
Lean now applies the p. 13 tag-projection smallness theorem to the actual real
fixed-base regular-coordinate map supplied by
`PaperEndpointFixedBaseRegularCoordinateSourceData`.  The ambient theorem
proves eventual `squareSum(F2)+squareSum(F3) <= 1` in `nhds x0`; the relative
theorem proves the same event in `nhdsWithin` the source-rank stratum by
filter weakening only.

Lean names:
`PaperEndpointFixedBaseRegularCoordinateSourceData.regularBlockCoordinateMap_f2_f3_squareSum_eventually_le_one`
and
`PaperEndpointFixedBaseRegularCoordinateSourceData.regularBlockCoordinateMap_f2_f3_squareSum_eventually_le_one_nhdsWithin_source`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-fixed-base-regular-coordinate-f2-f3-smallness.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-fixed-base-regular-coordinate-f2-f3-smallness.md`.
Review:
`threads/03-block-product-reduction/review-a2-fixed-base-regular-coordinate-f2-f3-smallness.md`.

Nonclaims: no source-rank openness, no analytic regular-coordinate chart, no
source coverage, no analytic ideal transport, no Fubini/polar shift, no normal
crossings, no pole-order theorem, and no RLCT theorem.

Latest A2 fixed-base literal-cleaned square-sum comparison:
Lean now defines the actual fixed-base literal signed/corrected scalar family
`paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap` and proves that
under real `PaperEndpointFixedBaseRegularCoordinateSourceData`, its square-sum
and the cleaned `paperEndpointFixedBaseProductDifferenceCoordinateMap`
square-sum are eventually mutually bounded by factor `2`, in both ambient
`nhds x0` and the source-rank `nhdsWithin` filter.  Directional wrappers expose
each inequality separately.

Lean names include
`PaperEndpointFixedBaseRegularCoordinateSourceData.literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two`,
`PaperEndpointFixedBaseRegularCoordinateSourceData.literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two_nhdsWithin_source`,
and the four directional projection wrappers with
`literalProductDifferenceCoordinateMap_squareSum...` /
`productDifferenceCoordinateMap_squareSum...`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-fixed-base-literal-cleaned-square-sum-comparison.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-fixed-base-literal-cleaned-square-sum-comparison.md`.
Review:
`threads/03-block-product-reduction/review-a2-fixed-base-literal-cleaned-square-sum-comparison.md`.

Nonclaims: no analytic ideal transport, no analytic chart construction, no
source coverage, no source-rank openness, no normal crossings, no pole-order
theorem, and no RLCT theorem.

Latest A2 one-step determinant-chart coordinate equivalence:
Lean now gives product-topology instances for the raw and chart one-step
product-reduction coordinate structures and proves the determinant-chart
subtype maps continuous in both directions.  The bundled homeomorphism is
`productReductionStepCoordinate_detChart_homeomorph` in
`ChartTopology.lean`, with supporting lemmas
`ProductReductionStepRawCoordinates.continuous_toChart_detChart_subtype`,
`ProductReductionStepRawCoordinates.continuous_detChart_toChart`,
`ProductReductionStepChartCoordinates.continuous_toRaw_detChart_subtype`, and
`ProductReductionStepChartCoordinates.continuous_detChart_toRaw`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-one-step-determinant-chart-coordinate-equivalence.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-one-step-determinant-chart-coordinate-equivalence.md`.
Review:
`threads/03-block-product-reduction/review-a2-one-step-determinant-chart-coordinate-equivalence.md`.

Nonclaims: no analytic regularity, no analytic Jacobian determinant
calculation, no source-rank openness, no source coverage, no ideal-germ
transport, no regular-suspension certificate, no normal crossings, no
pole-order theorem, and no RLCT theorem.

Latest A2 one-sided regular-suspension integrability:
Lean now proves the first ENNReal product-measure brick toward the regular
square-suspension theorem in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`.
For `s >= 0`,
`lintegral_rpow_neg_add_right_le_prod_fst` proves
`(a x + q y)^(-s) <= (a x)^(-s)` after integration over `mu.prod nu`.  The
finite-factor theorem
`lintegral_rpow_neg_add_right_lt_top_of_lintegral_rpow_neg_lt_top` uses
Tonelli's product formula to show that if `nu` is finite and
`∫ a^(-s) dmu < infinity`, then
`∫ (a x + q y)^(-s) d(mu.prod nu) < infinity`; the restricted theorem applies
the same result to `mu.restrict u` and `nu.restrict t` under `nu t < infinity`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-one-sided-regular-suspension-integrability.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-one-sided-regular-suspension-integrability.md`.
Review:
`threads/03-block-product-reduction/review-a2-one-sided-regular-suspension-integrability.md`.

Nonclaims: this does not define a local integrability threshold, prove the
regular-variable `+k/2` shift, prove a polar-coordinate estimate, prove a
bounded-density theorem, construct Aoyagi's p.13 analytic chart or Jacobian,
produce normal crossings, prove pole order, or prove RLCT.

Latest A2 radial finite-side integrability:
Lean now proves the punctured radial finite side in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`.
The radial model theorem
`integrable_norm_rpow_neg_indicator_Ioo` shows that
`1_(0,R)(||x||) * ||x||^(-t)` is integrable for a nontrivial
finite-dimensional real normed space with additive Haar measure when
`R>0` and `t < finrank_R(E)`.  The shifted quadratic theorem
`integrable_norm_sq_add_rpow_neg_indicator_Ioo` applies the comparison
`(||x||^2+a)^(-s) <= ||x||^(-2s)` on the punctured radial interval and proves
integrability under `a>=0`, `s>=0`, and `2*s < finrank_R(E)`.  The handoff
`lintegral_ofReal_norm_sq_add_rpow_neg_indicator_Ioo_lt_top` records
finiteness of the corresponding `ENNReal.ofReal` lower integral.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-radial-finite-side-integrability.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-radial-finite-side-integrability.md`.
Review:
`threads/03-block-product-reduction/review-a2-radial-finite-side-integrability.md`.

Nonclaims: this does not remove the puncture at the origin, prove a ball
integrability theorem, prove endpoint behavior, prove a lower/divergence side,
give uniform asymptotics in `a`, prove a bounded-density theorem, prove the
product-coordinate `+k/2` threshold theorem, construct Aoyagi's p.13 analytic
chart/Jacobian, produce normal crossings, prove pole order, or prove RLCT.

Latest A2 null-origin radial integrability:
Lean now proves a narrow a.e. representative transfer in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`.
The generic theorem `ae_eq_norm_indicator_Ioo_Iio` says that, for a nonatomic
measure, the radial indicator-extensions by zero on `(0,R)` and
`(-infinity,R)` agree almost everywhere.  The quadratic corollaries
`integrable_norm_sq_add_rpow_neg_indicator_Iio` and
`lintegral_ofReal_norm_sq_add_rpow_neg_indicator_Iio_lt_top` transfer the
finite-side result from the punctured theorem under the same hypotheses
`R>0`, `a>=0`, `s>=0`, and `2*s < finrank_R(E)`.  The open-ball wrappers
`norm_sq_add_rpow_neg_indicator_ball_eq_indicator_Iio`,
`integrable_norm_sq_add_rpow_neg_indicator_ball`, and
`lintegral_ofReal_norm_sq_add_rpow_neg_indicator_ball_lt_top` use only the
pointwise identity `x in Metric.ball 0 R iff ||x|| < R`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-null-origin-radial-integrability.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-null-origin-radial-integrability.md`.
Review:
`threads/03-block-product-reduction/review-a2-null-origin-radial-integrability.md`.

Nonclaims: no pointwise regularity at the origin, no closed-ball theorem or
boundary-sphere nullity, no endpoint behavior, no lower/divergence side, no
uniform asymptotics in `a`, no bounded-density theorem, no product-coordinate
`+k/2` threshold theorem, no Aoyagi p.13 analytic chart/Jacobian construction,
no normal crossings, no pole order, and no RLCT.

Latest A2 product below-critical integrability:
Lean now proves the first product-coordinate finite-side theorem in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`.
The theorem
`lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top` says that
for a finite base measure, additive Haar regular factor, a.e. nonnegative base
term `a : alpha -> R`, and strict regular-side inequality
`2*s < finrank_R(E)`, the ball-supported lower integral of
`(a(x)+||u||^2)^(-s)` over the product is finite.  The proof uses an a.e.
domination by the `a=0` regular-ball integrand and `lintegral_prod_mul` for the
majorant.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-product-below-critical-integrability.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-product-below-critical-integrability.md`.
Review:
`threads/03-block-product-reduction/review-a2-product-below-critical-integrability.md`.

Nonclaims: no regular-variable `+dim(E)/2` threshold shift, no theorem for
`s>=dim(E)/2`, no endpoint behavior, no lower/divergence side, no uniform
asymptotics, no bounded-density/prior theorem, no Aoyagi p.13 analytic
chart/Jacobian construction, no normal crossings, no pole order, and no RLCT.

Latest A2 product bounded-away integrability:
Lean now proves the away-from-residual-zero product estimate in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`.
The theorem
`lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_ae_pos_le`
says that for a finite base measure, additive Haar regular factor, positive
constant `epsilon`, a.e. lower bound `epsilon <= a(x)`, and `s>=0`, the
ball-supported lower integral of `(a(x)+||u||^2)^(-s)` over the product is
finite.  The proof dominates the integrand by the constant
`epsilon^(-s)` on the regular ball and factors that majorant by
`lintegral_prod_mul`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-product-bounded-away-integrability.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-product-bounded-away-integrability.md`.
Review:
`threads/03-block-product-reduction/review-a2-product-bounded-away-integrability.md`.
Threshold-shift route probe:
`threads/03-block-product-reduction/scout-a2-regular-square-threshold-shift-lean-route.md`.

Nonclaims: no singular-base theorem where `a(x)` approaches zero, no
regular-variable `+dim(E)/2` threshold shift, no endpoint behavior, no
lower/divergence side, no uniform asymptotics, no bounded-density/prior
theorem, no Aoyagi p.13 analytic chart/Jacobian construction, no normal
crossings, no pole order, and no RLCT.

Latest A2 Japanese-bracket supercritical integrability:
Lean now proves the global supercritical finite-side model in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`.
The theorems
`integrable_one_add_norm_sq_rpow_neg`,
`lintegral_ofReal_one_add_norm_sq_rpow_neg_lt_top`, and
`lintegral_ofReal_norm_sq_add_pos_rpow_neg_lt_top` say that if
`finrank_R(E)/2 < s`, then `(1+||x||^2)^(-s)` is integrable and has finite
`ENNReal.ofReal` lower integral, and for each fixed `a>0`,
`(a+||x||^2)^(-s)` has finite `ENNReal.ofReal` lower integral.  The proof uses
Mathlib's Japanese-bracket integrability theorem and compares the fixed
positive-parameter model against `min(a,1)^(-s)*(1+||x||^2)^(-s)`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-japanese-bracket-supercritical-integrability.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-japanese-bracket-supercritical-integrability.md`.
Review:
`threads/03-block-product-reduction/review-a2-japanese-bracket-supercritical-integrability.md`.

Nonclaims: no sharp `a^(finrank/2-s)` dependence, no product theorem with a
base function approaching zero, no regular-variable `+dim(E)/2` threshold
shift, no endpoint behavior, no lower/divergence side, no uniform asymptotics,
no bounded-density/prior theorem, no Aoyagi p.13 analytic chart/Jacobian
construction, no normal crossings, no pole order, and no RLCT.

Latest A2 sharp positive-parameter fiber scaling:
Lean now proves the fixed-positive-parameter Haar-scaling package in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`.  The theorems
`lintegral_comp_inv_smul_eq_mul_addHaar`,
`ofReal_add_norm_sq_pos_rpow_neg_eq_mul_one_add_norm_sq_inv_sqrt_smul`,
`lintegral_ofReal_add_norm_sq_pos_rpow_neg_eq_scale`,
`lintegral_ofReal_add_norm_sq_pos_rpow_neg_indicator_ball_le_scale`, and
`lintegral_ofReal_add_norm_sq_pos_rpow_neg_indicator_ball_lt_top_of_supercritical`
say that for `a>0`, the whole-space lower integral of
`(a+||u||^2)^(-s)` is exactly `a^(finrank/2-s)` times the
Japanese-bracket lower integral, and the ball-supported lower integral is
bounded by the same expression.  Under `finrank/2<s`, the right-hand side is
finite.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-sharp-positive-parameter-fiber-scaling.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-sharp-positive-parameter-fiber-scaling.md`.
Review:
`threads/03-block-product-reduction/review-a2-sharp-positive-parameter-fiber-scaling.md`.

Nonclaims: no variable-base product theorem, no residual-base integrability
of `a(x)^(finrank/2-s)`, no full regular-variable `+dim(E)/2` threshold
shift, no endpoint behavior, no lower/divergence side, no bounded-density or
prior theorem, no Aoyagi p.13 analytic chart/Jacobian construction, no normal
crossings, no pole order, and no RLCT.

Latest A2 variable-base product fiber integrability:
Lean now proves the first variable-base product theorem in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`.  The theorems
`lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_le_scale` and
`lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_ae_pos_of_base_lt_top`
say that if `a(x)>0` for base-a.e. `x`, `finrank_R(E)/2<s`, and
`∫⁻ x, ENNReal.ofReal (a(x)^(finrank_R(E)/2-s)) dmu < infinity`, then the
product lower integral of `(a(x)+||u||^2)^(-s)` over `alpha x ball(0,R)` is
finite.  No finite base measure or measurability hypothesis on `a` is used.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-variable-base-product-fiber-integrability.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-variable-base-product-fiber-integrability.md`.
Review:
`threads/03-block-product-reduction/review-a2-variable-base-product-fiber-integrability.md`.

Nonclaims: no proof of the residual-base integrability hypothesis, no theorem
for a positive-measure zero set of `a`, no endpoint behavior, no
lower/divergence side, no bounded-density or prior theorem, no Aoyagi p.13
analytic chart/Jacobian construction, no normal crossings, no pole order, and
no RLCT.

Latest A2 residual-power threshold-shift bridge:
Lean now proves the residual-power form of the variable-base product theorem
in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`.  The
theorems
`lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_le_residual_power_scale`
and
`lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top`
say that if `a(x)>0` for base-a.e. `x`, `0<t`, and
`∫⁻ x, ENNReal.ofReal (a(x)^(-t)) dmu < infinity`, then the product lower
integral of `(a(x)+||u||^2)^(-(t+finrank_R(E)/2))` over
`alpha x ball(0,R)` is finite.  The proof is the substitution
`s=t+finrank_R(E)/2` in the variable-base theorem, so
`finrank_R(E)/2-s=-t`.  No finite base measure or measurability hypothesis on
`a` is used.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-residual-power-threshold-shift-bridge.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-residual-power-threshold-shift-bridge.md`.
Review:
`threads/03-block-product-reduction/review-a2-residual-power-threshold-shift-bridge.md`.

Nonclaims: no proof that Aoyagi's reduced residual coordinates satisfy the
residual negative-power hypothesis, no theorem for a positive-measure zero set
of `a`, no endpoint behavior, no lower/divergence side or threshold equality,
no bounded-density or prior theorem, no Aoyagi p.13 analytic chart/Jacobian
construction, no normal crossings, no pole order, and no RLCT.

Latest A2 residual square-sum integrability socket:
Lean now specialises the residual-power threshold-shift bridge to Aoyagi's
finite coordinate square-sum convention in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean`.  The
theorems
`lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_le_residual_power_scale`,
`lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top`,
and
`lintegral_ofReal_residualBlockSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top`
say that if `a(x)=aoyagiCoordinateSquareSum (b x)` or the residual-block
version with `AoyagiResidualBlockCoordinateIndex.value (D x)` is a.e. strictly
positive, `0<t`, and its negative `t`-power lower integral is finite, then
the square-model product lower integral at exponent
`t+finrank_R(E)/2` is finite.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-residual-square-sum-integrability-socket.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-residual-square-sum-integrability-socket.md`.
Review:
`threads/03-block-product-reduction/review-a2-residual-square-sum-integrability-socket.md`.

Nonclaims: no proof that Aoyagi's reduced residual coordinates satisfy
positivity or residual negative-power integrability, no theorem for a
positive-measure zero set of the residual square-sum, no endpoint behavior, no
lower/divergence side or threshold equality, no bounded-density or prior
theorem, no Aoyagi p.13 analytic chart/Jacobian construction, no normal
crossings, no pole order, and no RLCT.

Latest A2 Euclidean coordinate square-sum base integrability:
Lean now proves the free-coordinate residual base theorem in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean`.  For
`x : EuclideanSpace ℝ eta`,
`aoyagiCoordinateSquareSum (fun i : eta => x i)` is `||x||^2`, so the
square-sum is positive away from the origin and positive a.e. for nonatomic
measures.  Lean proves finite local lower integral of its negative `t`-power
on `ball(0,R)` under `R>0`, `0<=t`, and `2*t < card eta`, and composes this
with the square-model product theorem.
Lean names:
`aoyagiEuclideanCoordinateSquareSum_pos_of_ne_zero`,
`ae_aoyagiEuclideanCoordinateSquareSum_pos`,
`ae_aoyagiEuclideanCoordinateSquareSum_pos_restrict`,
`lintegral_ofReal_euclideanCoordinateSquareSum_rpow_neg_indicator_ball_lt_top`,
`lintegral_ofReal_euclideanCoordinateSquareSum_rpow_neg_restrict_ball_lt_top`,
and
`lintegral_ofReal_euclideanCoordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-euclidean-coordinate-square-sum-base-integrability.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-euclidean-coordinate-square-sum-base-integrability.md`.
Review:
`threads/03-block-product-reduction/review-a2-euclidean-coordinate-square-sum-base-integrability.md`.

Nonclaims: no proof for Aoyagi's product residual `D=prod_s C^(s)`, no proof
that p.13 residual product coordinates are locally free Euclidean coordinates,
no zero-dimensional residual branch, no endpoint behavior, no lower/divergence
side or threshold equality, no bounded-density or prior theorem, no Aoyagi
p.13 analytic chart/Jacobian construction, no normal crossings, no pole order,
and no RLCT.

Latest A2 negative-power lower-bound comparison:
Lean now proves the model-loss comparison theorem in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`.  If `c>0`,
`0<=t`, `a(x)>0` a.e., `c*a(x)<=b(x)` a.e., and

```text
∫⁻ x, ENNReal.ofReal ((a x)^(-t)) dmu < infinity,
```

then

```text
∫⁻ x, ENNReal.ofReal ((b x)^(-t)) dmu < infinity.
```

Lean name:
`lintegral_ofReal_rpow_neg_lt_top_of_ae_pos_of_ae_const_mul_le`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-negative-power-lower-bound-comparison.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-negative-power-lower-bound-comparison.md`.
Review:
`threads/03-block-product-reduction/review-a2-negative-power-lower-bound-comparison.md`.

Nonclaims: no lower-bound construction for Aoyagi's product residual, no
monomial integrability theorem, no finite chart cover theorem, no density or
prior transport theorem, no endpoint behavior, no lower/divergence side or
threshold equality, no Aoyagi p.13 analytic chart/Jacobian construction, no
normal crossings, no pole order, and no RLCT.

Latest A2 positive-box monomial integrability:
Lean now proves the elementary positive-box monomial product theorem in
`lean/DLNFibre/DLN/Aoyagi/MonomialChartIntegrability.lean`.  For finite
coordinate index type `i`, radii `R_i>0`, and exponents `p_i>-1`,

```text
∫⁻ x, ENNReal.ofReal (prod_i x_i^(p_i))
  d Measure.pi (i |-> volume.restrict (0,R_i))
<
infinity.
```

It also proves the Aoyagi exponent-form corollary with
`p_i=h_i-2*t*k_i`, under the strict inequalities `2*t*k_i<h_i+1`.
Lean names:
`lintegral_ofReal_rpow_restrict_Ioo_lt_top`,
`lintegral_ofReal_monomialFactor_restrict_Ioo_lt_top`,
`lintegral_ofReal_fintype_rpow_positiveBox_lt_top`, and
`lintegral_ofReal_fintype_monomialFactor_positiveBox_lt_top`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-positive-box-monomial-integrability.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-positive-box-monomial-integrability.md`.
Review:
`threads/03-block-product-reduction/review-a2-positive-box-monomial-integrability.md`.

Nonclaims: no residual-loss lower-bound theorem, no density/prior upper-bound
theorem, no signed-box absolute-value theorem, no endpoint behavior, no
lower/divergence side or threshold equality, no finite chart cover theorem, no
Aoyagi p.13 analytic chart/Jacobian construction, no normal crossings, no pole
order, and no RLCT.

Latest A2 positive-box monomial domination:
Lean now proves direct lower-integral transfer from an a.e. upper bound by a
constant multiple of the positive-box monomial model in
`lean/DLNFibre/DLN/Aoyagi/MonomialChartIntegrability.lean`.  If `0<=A`,
`R_i>0`, `p_i>-1`, and

```text
f(x) <= A * prod_i x_i^(p_i)
```

for the product positive-box measure a.e., then `int^- ofReal(f)` is finite.
The Aoyagi wrapper takes `p_i=h_i-2*t*k_i` under
`2*t*k_i<h_i+1`.
Lean names:
`lintegral_ofReal_le_const_mul_fintype_rpow_positiveBox_lt_top` and
`lintegral_ofReal_le_const_mul_fintype_monomialFactor_positiveBox_lt_top`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-positive-box-monomial-domination.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-positive-box-monomial-domination.md`.
Review:
`threads/03-block-product-reduction/review-a2-positive-box-monomial-domination.md`.

Nonclaims: no residual-loss lower-bound theorem, no density/prior upper-bound
theorem, no derivation from separate loss and density estimates, no signed-box
absolute-value theorem, no endpoint behavior, no lower/divergence side or
threshold equality, no finite chart cover theorem, no Aoyagi p.13 analytic
chart/Jacobian construction, no normal crossings, no pole order, and no RLCT.

Latest A2 positive-box residual/density comparison:
Lean now derives the positive-box monomial domination hypothesis from explicit
separate a.e. loss and density bounds in
`lean/DLNFibre/DLN/Aoyagi/MonomialChartIntegrability.lean`.  On the product
positive-box measure, if `c>0`, `C>=0`, `t>=0`, `R_i>0`,
`2*t*k_i<h_i+1`, and a.e.

```text
c * prod_i x_i^(2*k_i) <= loss(x),
0 <= density(x),
density(x) <= C * prod_i x_i^(h_i),
```

then `int^- ofReal(loss(x)^(-t) * density(x))` is finite.  The proof first
records a.e. coordinate positivity for the positive-box product measure, then
proves the pointwise domination with constant `c^(-t)*C`, and finally invokes
the landed positive-box monomial domination theorem.
Lean names:
`ae_forall_pos_measure_pi_restrict_Ioo`,
`loss_rpow_neg_mul_density_le_const_mul_monomialFactor_of_pos`, and
`lintegral_ofReal_loss_rpow_neg_mul_density_positiveBox_lt_top`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-positive-box-residual-density-comparison.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-positive-box-residual-density-comparison.md`.
Review:
`threads/03-block-product-reduction/review-a2-positive-box-residual-density-comparison.md`.

Nonclaims: no signed-box or absolute-value theorem, no proof that Aoyagi's
actual product-residual charts satisfy the supplied bounds, no analytic
density/Jacobian transport theorem, no finite chart cover theorem, no endpoint
behavior, no lower/divergence side or threshold equality, no Aoyagi p.13
analytic chart/Jacobian construction, no normal crossings, no pole order, and
no RLCT.

Latest A2 signed-box residual/density comparison:
Lean now proves the signed-box absolute-value analogue of the positive-box
finite-side comparison in
`lean/DLNFibre/DLN/Aoyagi/MonomialChartIntegrability.lean`.  On the product
signed-box measure, if `c>0`, `C>=0`, `t>=0`, `R_i>0`,
`2*t*k_i<h_i+1`, and a.e.

```text
c * prod_i |x_i|^(2*k_i) <= loss(x),
0 <= density(x),
density(x) <= C * prod_i |x_i|^(h_i),
```

then `int^- ofReal(loss(x)^(-t) * density(x))` is finite.  The proof first
records a.e. coordinate nonvanishing for the signed-box product measure, then
proves one-dimensional and finite-product absolute-power integrability, then
derives the pointwise absolute-monomial domination with constant `c^(-t)*C`,
and finally invokes the signed-box domination theorem.
Lean names:
`ae_forall_abs_pos_measure_pi_restrict_Ioo_neg`,
`integrableOn_abs_rpow_Ioo_neg_pos`,
`lintegral_ofReal_abs_rpow_restrict_Ioo_neg_lt_top`,
`lintegral_ofReal_fintype_abs_rpow_signedBox_lt_top`,
`lintegral_ofReal_fintype_abs_monomialFactor_signedBox_lt_top`,
`lintegral_ofReal_le_const_mul_fintype_abs_rpow_signedBox_lt_top`,
`lintegral_ofReal_le_const_mul_fintype_abs_monomialFactor_signedBox_lt_top`,
`loss_rpow_neg_mul_density_le_const_mul_abs_monomialFactor_of_abs_pos`, and
`lintegral_ofReal_loss_rpow_neg_mul_density_signedBox_lt_top`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-signed-box-residual-density-comparison.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-signed-box-residual-density-comparison.md`.
Review:
`threads/03-block-product-reduction/review-a2-signed-box-residual-density-comparison.md`.

Nonclaims: no proof that Aoyagi's actual product-residual charts satisfy the
supplied bounds, no analytic density/Jacobian transport theorem, no finite
chart cover theorem, no endpoint behavior, no lower/divergence side or
threshold equality, no Aoyagi p.13 analytic chart/Jacobian construction, no
normal crossings, no pole order, and no RLCT.

Latest A2 regular-suspension local finite-integral bridge:
Lean now composes the p.13 uniform-in-fiber local measure handoff with the
p.13 bounded-density finite-side adapter in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`.  If the source
filter supplies uniform loss/density bounds on the regular-coordinate ball,
and the source stratum also has supplied residual square-sum positivity plus
finite `int^- ofReal(residualSquareSum^(-t))`, then Lean produces an open
neighborhood `U` such that the local product lower integral of
`loss^(-(t+regularCount/2))*density` is finite over
`(mu.restrict (U inter sourceStratum)).prod nu`.

Lean names:
`PaperEndpointFixedBaseRegularCoordinateSourceData.residualNegPowerIntegrableOn`
and
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top`.

Nonclaims: no measurable-source-stratum proof, no p.13 product chart, no
source/product coordinate identification, no original DLN loss comparison, no
density/Jacobian transport, no proof of residual positivity or residual-base
integrability, no normal crossings, no pole order, and no RLCT.

Latest A2 adapted product-difference local-measure handoff:
Lean now converts the positive self-base adapted fixed-base lower bound

```text
(c/2) * (regularSquareSum + residualSquareSum)
  <= adaptedProductDifferenceSquareSum
```

from the source-rank `nhdsWithin` filter into restricted-measure a.e. form,
and into a product-measure first-projection form.  The positive constant `c`
is preserved.

Lean names:
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_open_ae_restrict_source_half_regular_add_residual_squareSum_le_adaptedProductDifferenceSquareSum_selfBase`
and
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_open_ae_restrict_source_prod_fst_half_regular_add_residual_squareSum_le_adaptedProductDifferenceSquareSum_selfBase`.

Nonclaims: no original `lossDLN` comparison, no p.13 product chart, no
source/product coordinate identification, no density/Jacobian transport, no
residual integrability, no normal crossings, no pole order, and no RLCT.  The
original-loss audit requires an explicit positive local comparison from
original loss to the adapted fixed-base square-sum before any original-loss
handoff is stated.

Latest A2 adapted product-difference local finite-integral handoff:
Lean now proves a conditional finite-integral wrapper for a supplied product
edge-family `CedgeProd`.  If, uniformly on the source filter and on a fixed
regular-coordinate ball,

```text
c * (residualSquareSumBase(x) + squareSum(u))
  <= paperEndpointFixedBaseAdaptedProductDifferenceSquareSum(CedgeProd(x,u)),
```

and that adapted square-sum is identified with a chart loss, then the existing
p.13 finite-side theorem gives finite lower integral of

```text
1_{ball(0,R)}(u)
  * chartLoss(x,u)^(-(t+regularCount/2))
  * density(x,u)
```

over a sufficiently small restricted source neighborhood times the regular
coordinate measure.

Lean name:
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_chartLoss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_adaptedProductDifferenceSquareSum_identified`.

Nonclaims: no product chart construction, no source coverage theorem, no
coordinate identification proof, no Jacobian/prior density transport, no
residual positivity or residual integrability proof, no original `lossDLN`
comparison, no normal crossings, no pole order, and no RLCT.

Latest A2 local-source monomial-unit finite-integral wrapper:
Lean now proves that the local-source signed-box finite-integral theorem can
consume supplied monomial-times-unit residual and source-density data directly.
The theorem composes the elementary monomial-unit inequality package with the
local-source signed-box finite-integral handoff.

Lean name:
`exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_residualSource_signedBox_withDensity_monomialUnits_edgeMatrix`.

Nonclaims: no local chart construction, no source coverage, no pushforward
proof, no density/Jacobian formula, no concrete monomial-unit production, no
normal-crossing extraction, no pole order, and no RLCT.

Latest A2 selected-entry signed-box monomial-unit data:
Lean now proves the concrete selected-entry monomial-unit data expected by the
local-source signed-box consumer.

Lean names:
`SelectedEntrySignedBox.residual_eq_unit_mul_abs_monomial`,
`SelectedEntrySignedBox.sourceDensity_eq_abs_pivotFirstJacobian_det`,
`SelectedEntrySignedBox.sourceDensity_eq_unit_mul_abs_monomial`,
`SelectedEntrySignedBox.monomialUnitHypotheses`, and
`SelectedEntrySignedBox.monomialLower_sourceDensityBounds`, plus the
center-subtype API
`SelectedEntrySignedBox.CenterCoord.residual_eq_aoyagiCoordinateSquareSum_chartMap`,
`SelectedEntrySignedBox.CenterCoord.aoyagiCoordinateSquareSum_eq_residual_of_coord_readout`,
`SelectedEntrySignedBox.CenterCoord.monomialUnitHypotheses` and
`SelectedEntrySignedBox.CenterCoord.monomialLower_sourceDensityBounds`.

The coordinate index is `Option {i // i in center.erase pivot}`.  The pivot
coordinate has loss exponent `1`; the non-pivot residual coordinates have loss
exponent `0`.  The formal density is the absolute value of the formal
pivot-first determinant, so its pivot exponent is `(center.erase pivot).card`
and its other exponents are `0`.  The residual unit is bounded below by `1`,
and the formal density unit is exactly `1`.  The center-subtype API restates
the same data over `center -> R` with zero exponents away from the pivot.  It
now also proves the raw residual square-sum identity over center coordinates
and a source-neutral coordinate-readout bridge under an explicit finite
reindexing and pointwise coordinate readout.

Nonclaims: no analytic chart construction, source coverage, transition
regularity, source production, weighted pushforward, analytic
Jacobian/source-density transport, full loss comparison, normal-crossing
extraction, pole order, or RLCT.

Latest A2 selected-entry original-loss readout wrapper:
`SelectedEntryOriginalLossLocalMeasure.lean` now exposes the local
source-stratum original-loss endpoint with the raw scalar residual square-sum
hypothesis replaced by an explicit residual-coordinate readout and finite
reindexing equivalence.  This is API sharpening only: local source/image
equality and fixed-base residual readout remain supplied.

Latest A2 selected-entry residual-product matrix readout:
`SelectedEntryOriginalLossLocalMeasure.lean` now proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_residualProduct_eq_matrix`.
This converts a supplied matrix identity for the fixed-base suffix residual
product at `chartMap pivot y` into the pointwise selected-entry coordinate
readout expected by the original-loss wrapper.  It uses
`paperEndpointFixedBaseResidualBlockCoordinateMap_eq_residualProduct` and
`AoyagiResidualBlockCoordinateIndex.value_matrix`; it does not construct
`CedgeBase`, prove the residual-product matrix identity, construct the
residual-index equivalence, or prove source coverage.

Latest A2 selected-entry residual-product square-sum:
`SelectedEntryOriginalLossLocalMeasure.lean` now proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_residualProduct_eq_matrix`.
It composes the residual-product matrix readout bridge with the finite
selected-entry square-sum reindexing theorem, producing the scalar
`hresidual_eq` shape expected by local-source/original-loss sockets from the
sharper residual-product matrix identity.  This still leaves the matrix
identity, residual-index equivalence, source coverage, source-measure
identification, normal crossings, pole order, and RLCT supplied/unproved.

Latest A2 selected-entry prescribed-matrix readout:
`SelectedEntryOriginalLossLocalMeasure.lean` now proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_prescribedEdgeMatrix_residualProduct_eq_matrix`.
If future selected-entry source-chart algebra supplies a fixed-base matrix
family `Ebase x`, and its residual product at `chartMap pivot y` is the
selected-entry chart matrix, the theorem realises each `Ebase x` as continuous
fixed-base reverse edges and returns the pointwise residual-coordinate readout.
This is still a supplied-matrix bridge: no construction of `Ebase`, no proof
of the residual-product matrix identity, no residual-index equivalence, and no
source coverage.

Latest A2 single-edge residual-product realisation:
`ProductReduction.lean` now proves
`ChartLocalSuffixState.residualProduct_productCoordinateSingleEdge_eq`, and
`RegularSuspensionCoordinates.lean` proves
`paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean_residualProduct_eq`.
For the one-edge p.13 product-coordinate matrix
`[Ctop,-Ctop F2; -F3 Ctop, D + F3 Ctop F2]`, the transformed Schur residual is
`D` under `IsUnit Ctop.det`, and the suffix-state bridge identifies it with
the raw `residualProduct`.  This is finite one-edge algebra only: not a raw
lower-right-block identity, not a multi-edge arbitrary-terminal-residual
realisation theorem, and not source coverage, source-measure transport, normal
crossings, pole order, or RLCT.

Latest A2 single-edge source-dependent residual-matrix family:
`ChartTopology.lean` now proves `continuous_productCoordinateSingleEdgeMatrix`.
`RegularSuspensionCoordinates.lean` now defines
`paperEndpointFixedBaseSingleEdgeProductCoordinateEdgeFamilyOfResidualMatrixEuclidean`
and proves
`paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_singleEdgeProductCoordinateEuclidean_residualMatrix`
and
`continuousAt_paperEndpointFixedBaseSingleEdgeProductCoordinateEdgeFamilyOfResidualMatrixEuclidean`.
For `Dbase x`, the one-edge p.13 product-coordinate edge family reads regular
coordinates as `u` and residual coordinates as
`AoyagiResidualBlockCoordinateIndex.value (Dbase x)`, under the explicit
`IsUnit det(Ctop(u))` hypothesis; under `Continuous Dbase`, the realised edge
family is continuous at `(x₀,u₀)`.  This is one-edge finite algebra only: no
construction of `Dbase`, no source chart or source coverage, no source-measure
transport, no normal crossings, pole order, RLCT, or multi-edge
arbitrary-terminal-residual theorem.

Latest A2 single-edge selected-entry product-coordinate readout:
`SelectedEntryOriginalLossLocalMeasure.lean` now defines
`paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEdgeFamilyEuclidean`
and proves
`paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_singleEdgeSelectedEntryProductCoordinateEuclidean`
and
`continuousAt_paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEdgeFamilyEuclidean`.
This sets the one-edge `Dbase y` to the residual matrix built from
`SelectedEntrySignedBox.CenterCoord.chartMap pivot y` through a supplied
`residualCoordEquiv`.  Under `IsUnit det(Ctop(u))`, the readout has regular
coordinates `u` and residual coordinates equal to the selected-entry chart
coordinates after `residualCoordEquiv`.  This is one-edge finite coordinate
algebra only: the index equivalence and determinant condition are explicit,
and there is no inverse chart, source coverage, source-measure transport,
normal crossings, pole order, RLCT, or multi-edge arbitrary-terminal-residual
theorem.

Latest A2 single-edge selected-entry square-sum readout:
`SelectedEntryOriginalLossLocalMeasure.lean` now proves
`aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_singleEdgeSelectedEntryProductCoordinateEuclidean`.
It composes the one-edge selected-entry coordinate readout with finite
reindexing of `aoyagiCoordinateSquareSum`, giving the scalar identity
`aoyagiCoordinateSquareSum (residualBlockCoordinateMap (y,u)) =
SelectedEntrySignedBox.CenterCoord.residual pivot y` under the same explicit
`IsUnit det(Ctop(u))` hypothesis and supplied `residualCoordEquiv`.  This is
source-neutral one-edge finite algebra only: it does not construct source
coverage, source-stratum equality, source-measure transport, local lower
bounds, normal crossings, pole order, RLCT, or a multi-edge selected-entry
residual product.

Latest A2 single-edge selected-entry determinant-ball readout:
`SelectedEntryOriginalLossLocalMeasure.lean` now proves
`exists_pos_radius_le_forall_paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEuclidean_readout`.
For any `0<Rmax`, it chooses `0<R<=Rmax` using the existing determinant
neighborhood theorem for `Ctop(u)`, and on `Metric.ball 0 R` gives the
one-edge selected-entry regular readout, residual-coordinate readout, and
scalar square-sum readout without a separate pointwise determinant hypothesis.
This is source-neutral determinant-chart plumbing only: one-edge, local near
`u=0`, with `residualCoordEquiv` still supplied; no source coverage,
source-stratum equality, source-measure transport, local lower bound, normal
crossings, pole order, RLCT, or multi-edge selected-entry residual product is
proved.

Latest A2 selected-entry chart-image characterization:
`SelectedEntrySignedBoxMeasure.lean` now proves
`SelectedEntrySignedBox.CenterCoord.mem_chartMap_image_signedBoxSet_iff`.
For positive signed-box radii, membership in
`chartMap pivot '' signedBoxSet R` is equivalent to being the origin or lying
in the nonzero-pivot horn
`x pivot != 0`, `|x pivot| < R pivot`, and
`|x i / x pivot| < R i` for every non-pivot coordinate.  This is finite
selected-entry chart algebra only; it does not prove local source-stratum
coverage, source-measure identification, fixed-base residual readout, normal
crossings, pole order, or RLCT.

Latest A2 selected-entry finite sector cover:
`SelectedEntrySignedBoxMeasure.lean` now proves
`SelectedEntrySignedBox.CenterCoord.signedBoxSet_subset_iUnion_chartMap_image_signedBoxSet_of_one_lt`.
If `S i <= R i` and every target radius satisfies `1 < R i`, then
`signedBoxSet S` is contained in the union of all selected-entry chart images
`chartMap pivot '' signedBoxSet R`, by choosing a maximal absolute-value
pivot for nonzero points.  This is finite all-pivot sector geometry only; it
does not prove local source-stratum coverage, source/image equality,
residual-product matrix identity, source-measure identification, normal
crossings, pole order, or RLCT.

Latest A2 selected-entry finite-cover integral assembly:
`SelectedEntrySignedBoxLocalMeasure.lean` now proves
`lintegral_prod_restrict_lt_top_of_subset_iUnion_finite` and
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_selectedEntryCenter_signedBox_finiteCover_withDensity_edgeMatrix`.
`SelectedEntryOriginalLossLocalMeasure.lean` now proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_selectedEntryCenter_signedBox_finiteCover_withDensity_edgeMatrix_adaptedProductDifferenceSquareSum_lower`.
These assemble the per-pivot selected-entry chart-image finite-integral
theorems over the finite all-pivot sector cover of a smaller signed box near
`0`, and then instantiate the result for the original `lossDLN` via the
adapted-to-original loss comparison.  The reproduction and statement card are
at
`threads/03-block-product-reduction/reproduction-a2-selected-entry-finite-cover-integral-assembly.md`
and
`threads/03-block-product-reduction/statement-card-a2-selected-entry-finite-cover-integral-assembly.md`.
This does not prove source-rank-stratum coverage, source/image equality,
source-measure transport from original coordinates, analytic source-chart
production, normal crossings, pole order, or RLCT.

Latest A2 selected-entry local-source finite-integral handoff:
Lean now specializes the local-source monomial-unit finite-integral socket to
the center-indexed selected-entry signed box.

Lean name:
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_selectedEntryCenter_signedBox_withDensity_edgeMatrix`.

The theorem keeps the source chart, weighted pushforward, and residual
coordinate identity as explicit hypotheses, but discharges the residual-unit
identity, source-density unit identity, unit bounds, and coordinatewise
critical-exponent hypothesis using the selected-entry calculation.  The pivot
threshold is `2 * t < (center.erase pivot.1).card + 1`; non-pivot coordinates
are automatic because both their loss and density exponents are zero.

Nonclaims: no source chart construction, no source image/coverage theorem, no
weighted pushforward proof, no analytic Jacobian/source-density transport, no
original-loss comparison, no normal-crossing certificate, no pole-order
theorem, and no RLCT theorem.

Latest A2 local-source adapted-loss finite-integral socket:
Lean now proves the adapted-loss comparison finite-integral handoff over an
explicit local source.  The proof only multiplies the adapted lower bound by a
positive adapted-to-loss comparison constant before applying the local-source
p.13 theorem.

Lean name:
`exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_const_mul_adaptedProductDifferenceSquareSum_le_loss`.

Nonclaims: no adapted lower-bound proof, no original `lossDLN` comparison, no
local chart construction, no source coverage, no density/Jacobian transport,
no normal-crossing extraction, no pole order, and no RLCT.

Latest A2 original-loss local-source finite-integral socket:
Lean now proves that the local-source adapted-loss finite-integral socket
specializes to the concrete endpoint square-Frobenius `lossDLN` of a chain
matrix tuple.

Lean name:
`exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_adaptedProductDifferenceSquareSum_lower`.

The only discharged input is the adapted-square-sum-to-original-loss
comparison, obtained from finite endpoint basis comparison plus the adapted
Frobenius-loss/square-sum identity.  The local source, residual
positivity/integrability, adapted product-coordinate lower bound, and density
bounds remain hypotheses.

Nonclaims: no local source construction, chart construction, source coverage,
pushforward or Jacobian/source-density transport, residual/source-density
monomial-unit production, statistical/KL loss comparison, normal-crossing
extraction, pole order, or RLCT.

Latest A2 measurable local-source package:
Lean now proves that a fixed-base local source certificate supplies an explicit
measurable local source `source = U inter sourceRankStratum`; the edge-matrix
version derives source-rank-stratum measurability from the fixed-base
edge-matrix family.  At the regular-coordinate source-data level, the local
source has the same `nhdsWithin x0` filter as the full source-rank stratum.

Lean names:
`PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_measurable_localSource`,
`PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_measurable_localSource_of_measurable_edgeMatrix`,
and
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_measurable_localSource_nhdsWithin_of_measurable_edgeMatrix`.

Nonclaims: no signed-box chart construction, source image/coverage theorem,
pushforward or Jacobian/source-density identity, residual/source-density
monomial-unit production, normal-crossing extraction, pole order, or RLCT.

Latest A2 local-source product-family adapted lower bound:
Lean now proves that the explicit self-base multi-edge p.13 product-coordinate
adapted lower bound holds over the measurable local source extracted from the
source certificate.

Lean name:
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_measurable_localSource_pos_radius_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase`.

The theorem returns the local source, open neighborhood, source measurability,
basepoint membership, source-stratum inclusion, source-rank conclusions,
`nhdsWithin` equality, positive radius/constant, and the adapted lower bound
on `nhdsWithin x0 source`.

Nonclaims: no signed-box chart construction, source image/coverage theorem,
pushforward or Jacobian/source-density identity, original/KL loss comparison,
residual/source-density monomial-unit production, normal-crossing extraction,
pole order, or RLCT.

Latest A2 local-source original-loss product-family continuation:
Lean now proves that the measurable local-source product-family package
composes with the local-source original-loss finite-integral socket.  The
result returns the local source, source-rank data, `nhdsWithin` equality,
positive radius/constant, and a continuation for the concrete endpoint
square-Frobenius `lossDLN`.

Lean name:
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_measurable_localSource_forall_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_multiEdgeProductCoordinateEdgeFamily_selfBase`.

The continuation still requires residual positivity, residual negative-power
integrability, an additive Haar regular-coordinate measure, and local density
nonnegativity/boundedness on the returned `source`.

Nonclaims: no signed-box chart construction, source image/coverage theorem,
pushforward or Jacobian/source-density identity, residual/source-density
monomial-unit production, residual integrability proof, normal-crossing
extraction, pole order, or RLCT.

Latest A2 product-coordinate source-rank membership:
Lean now proves the elementary product-coordinate rank identities for the
p.13 right endpoint, middle edges, and left endpoint, and uses them to show
that the explicit multi-edge product-coordinate family preserves source-rank
stratum membership under the base product-reduction certificate and
`det Ctop` unit condition.  The local version chooses a small regular
coordinate radius and works eventually in `nhdsWithin` the base source-rank
stratum.

Lean names:
`ChartLocalSuffixState.rank_productCoordinateRightEndpointMatrix`,
`ChartLocalSuffixState.rank_productCoordinateMiddleMatrix`,
`ChartLocalSuffixState.rank_productCoordinateLeftEndpointMatrix`,
`paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_mem_sourceRankStratum`,
and
`exists_pos_radius_le_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_mem_sourceRankStratum_nhdsWithin_source`.

Reproduction and review:
`threads/03-block-product-reduction/reproduction-a2-product-coordinate-source-rank-membership.md`
and
`threads/03-block-product-reduction/review-a2-product-coordinate-source-rank-membership.md`.

Nonclaims: no source coverage, no local source/image equality, no exact-rank
openness, no inverse chart, no density/Jacobian transport, no normal-crossing
certificate, no pole-order theorem, and no RLCT theorem.

Latest A2 source-stratum local-subset local-source consumer:
Lean now proves the generic conditional finite-integral consumer

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_subset_localSource
```

in `RegularSuspensionLocalMeasure.lean`.  Given an open neighborhood `Ulocal`
with

```text
Ulocal ∩ sourceStratum ⊆ Ulocal ∩ localSource,
```

it shrinks the local-source finite-integral theorem's returned open set by
`Ulocal` and compares restricted product measures to obtain finiteness over
the source-rank stratum.  The theorem carries `[SFinite μ]` for that product
measure comparison.

Reproduction and review:
`threads/03-block-product-reduction/reproduction-a2-source-stratum-local-subset-local-source-finite-integral-consumer.md`
and
`threads/03-block-product-reduction/review-a2-source-stratum-local-subset-local-source-finite-integral-consumer.md`.

Nonclaims: no proof of the local inclusion, no source coverage, no local
source/image equality, no raw-Haar pushforward, no source-measure transport,
no density/Jacobian identity, no normal crossings, pole order, or RLCT.

Latest A2 p.13 local source coverage boundary:
Post-recovery xhigh source, Lean/API, and hardening scouts rechecked whether
Aoyagi pp. 10-13 or current Lean APIs support a genuine p.13 local
source-coverage/inverse theorem after the local-subset consumer.  They do not.
The paper supports Lemma 2 block elimination, Theorem 3 product normal form,
and the p.13 product-difference display, but does not state source/image
equality, a determinant-chart finite cover, a local inverse carrying passive
variables, source-measure pushforward, or density/Jacobian transport.  Lean
likewise proves forward p.13 source-rank image membership and conditional
local-source consumers, while reverse coverage remains supplied.

Audit:
`threads/03-block-product-reduction/source-audit-a2-p13-local-source-coverage-boundary.md`.

Decision: do not add further wrappers treating the local-subset consumer as
coverage.  Future A2 work must either prove a genuine p.13 source chart with
passive variables and transport, prove a smaller reverse rank/readback theorem,
or move to a different source-backed finite algebra slice.

Latest A2 product-coordinate residual-rank readback:
Lean now proves the pointwise reverse rank theorem

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_residualBlock_rank_of_mem_sourceRankStratum
```

in `RegularSuspensionCoordinates.lean`.  If the constructed p.13 multi-edge
product-coordinate family is already in the source-rank stratum at `(x,u)`,
and `det Ctop(u)` is a unit, then the base Schur residual block at every edge
has rank `rEdge p - r`.  The proof uses the p.13 endpoint/middle block-rank
formulas in reverse and the basepoint identification of the regular corner
size with `r`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-product-coordinate-residual-rank-readback.md`,
`threads/03-block-product-reduction/statement-card-a2-product-coordinate-residual-rank-readback.md`,
and
`threads/03-block-product-reduction/review-a2-product-coordinate-residual-rank-readback.md`.

Nonclaims: no source coverage, no local inverse, no exact-rank openness, no
source/image equality, no source-measure transport, no density/Jacobian
identity, no normal crossings, no pole order, and no RLCT.

Latest A2 selected-entry residual-factor readout boundary:
Lean now proves the finite handoff from compatible residual factors to the
selected-entry residual-product matrix identity.  If the fixed-base
transformed Schur residual blocks along `chartMap pivot y` are a supplied
factor family `Cfac y`, and the ordered product
`residualFactorProduct (Cfac y) last 0` is the selected-entry coordinate
matrix, then the fixed-base `residualProduct` is that same selected-entry
matrix.

Lean name:
`PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseResidualProduct_eq_selectedEntryCenter_matrix_of_residualFactorProduct_eq_matrix`.

Reproduction and review:
`threads/03-block-product-reduction/reproduction-a2-selected-entry-residual-factor-readout-boundary.md`
and
`threads/03-block-product-reduction/review-a2-selected-entry-residual-factor-readout-boundary.md`.

Nonclaims: no construction of `Cfac`, no factor-product identity proof, no
residual-index equivalence construction, no source/image equality,
source-measure transport, normal crossings, pole order, or RLCT.

Latest A2 selected-entry residual-factor constructor readout:
Lean now composes the supplied residual-factor constructor with the
selected-entry prescribed-matrix readout.  A supplied source-indexed family
`Cfac`, evaluated at `chartMap pivot y`, is threaded through the actual
fixed-base product-coordinate matrices; the constructor's residual-product
theorem reduces the readout socket to the supplied factor-product identity.

Lean name:
`PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_residualFactorProduct_eq_matrix`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-selected-entry-residual-factor-constructor-readout.md`,
`threads/03-block-product-reduction/statement-card-a2-selected-entry-residual-factor-constructor-readout.md`,
and
`threads/03-block-product-reduction/review-a2-selected-entry-residual-factor-constructor-readout.md`.

Nonclaims: no construction of `Cfac`, no factor-product selected-entry proof,
no residual-index equivalence construction, no source/image equality, no
source-measure transport, no normal crossings, pole order, or RLCT.

Latest A2 residual-factor product two-edge unfold:
Lean now proves that an explicit residual-factor product over two supplied
edges unfolds to the product of the right factor and the left factor, after
casting both factors to the canonical middle endpoint `(1 : Fin 3)`.

Lean name:
`ChartLocalSuffixState.residualFactorProduct_fin_two_eq_mul`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-residual-factor-product-two-edge-unfold.md`,
`threads/03-block-product-reduction/statement-card-a2-residual-factor-product-two-edge-unfold.md`,
and
`threads/03-block-product-reduction/review-a2-residual-factor-product-two-edge-unfold.md`.

Nonclaims: no concrete displayed Case 2 `Cfac`, no construction of global
compatible factors, no residual-index equivalence, no selected-entry matrix
identity, no source/image equality, no normal crossings, pole order, or RLCT.

Latest A2 Case 2 residual-factor product reindex:
Lean now proves that a supplied two-edge residual-factor product, with
explicit endpoint equivalences and supplied factor identities, reindexes to
Aoyagi's displayed Case 2 post-pivot free-`C'` product.

Lean name:
`case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_residualFactorProduct_submatrix`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-case2-residual-factor-product-reindex.md`,
`threads/03-block-product-reduction/statement-card-a2-case2-residual-factor-product-reindex.md`,
and
`threads/03-block-product-reduction/review-a2-case2-residual-factor-product-reindex.md`.

Nonclaims: no construction of `Cfac`, no fixed-base endpoint equivalence, no
selected-entry coordinate-matrix RHS identity, no source/image equality, no
source-measure transport, no normal crossings, pole order, or RLCT.

Latest A2 Case 2 residual-factor product selected-center matrix bridge:
Lean now proves that once the displayed post-pivot lower product is supplied
as the selected-center coordinate matrix after endpoint reindexing, the
unreindexed two-edge `residualFactorProduct` itself is exactly that
selected-center coordinate matrix.

Lean names:
`Matrix.eq_of_submatrix_equiv_eq` and
`residualFactorProduct_eq_centerCoordinateMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_submatrix`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-case2-residual-factor-product-selected-center-matrix.md`,
`threads/03-block-product-reduction/statement-card-a2-case2-residual-factor-product-selected-center-matrix.md`,
and
`threads/03-block-product-reduction/review-a2-case2-residual-factor-product-selected-center-matrix.md`.

Nonclaims: the displayed selected-center RHS identity is still supplied; no
construction of `Cfac`, no fixed-base endpoint equivalence, no source
production of `Cprime`, no source/image equality, no source-measure transport,
no normal crossings, pole order, or RLCT.

Latest A2 Case 2 residual-coordinate index pivot-entry equivalence:
Lean now proves that the p.13 scalar residual-coordinate index for a Case 2
residual block is equivalent to the finite set of candidate selected entries
in that block.

Lean name:
`case2ResidualBlockCoordinateIndexEquivPivotEntries`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-case2-residual-coordinate-index-pivot-entries.md`,
`threads/03-block-product-reduction/statement-card-a2-case2-residual-coordinate-index-pivot-entries.md`,
and
`threads/03-block-product-reduction/review-a2-case2-residual-coordinate-index-pivot-entries.md`.

Nonclaims: no selected-entry chart construction, no compatible `Cfac`, no
selected-entry matrix RHS identity, no source/image equality, no
source-measure transport, no normal crossings, pole order, or RLCT.

Latest A2 Case 2 residual-coordinate endpoint-equivalence composition:
Lean now proves that supplied row and column endpoint equivalences compose
with the Case 2 residual-coordinate index equivalence to give the full
`residualCoordEquiv` shape expected by the selected-entry readout socket.

Lean name:
`case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs`, with the
orientation wrapper
`case2ResidualBlockCoordinateIndexEquivPivotEntriesOfCase2EndpointEquivs`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-case2-residual-coordinate-endpoint-equivalence-composition.md`,
`threads/03-block-product-reduction/statement-card-a2-case2-residual-coordinate-endpoint-equivalence-composition.md`,
and
`threads/03-block-product-reduction/review-a2-case2-residual-coordinate-endpoint-equivalence-composition.md`.

Nonclaims: the row and column endpoint equivalences are still supplied; no
selected-entry chart construction, no compatible `Cfac`, no selected-entry
matrix RHS identity, no source/image equality, no source-measure transport,
no normal crossings, pole order, or RLCT.

Latest A2 fixed-base residual-factor family constructor:
Lean now defines the raw p.13 fixed-base matrix family from a supplied
compatible residual-factor family `Cfac`, rather than reading the factors from
a base edge family.  It proves that every transformed Schur residual block
visited by the suffix recursion is the supplied factor, and that the suffix
`residualProduct` is the ordered `residualFactorProduct Cfac`.

Lean names:
`paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfResidualFactorsEuclidean`,
`paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfResidualFactorsEuclidean_residualBlock_eq`,
and
`paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfResidualFactorsEuclidean_residualProduct_eq_residualFactorProduct`.

Reproduction and review:
`threads/03-block-product-reduction/reproduction-a2-fixed-base-residual-factor-family-constructor.md`
and
`threads/03-block-product-reduction/review-a2-fixed-base-residual-factor-family-constructor.md`.

Nonclaims: no construction of `Cfac` from source-chart data, no
selected-entry factor-product identity, no residual-index equivalence, no
source/image equality, source-measure transport, normal crossings, pole order,
or RLCT.

Latest A6 Definition 3 all-source strict rank-width:
Proved that in the explicit all-source branch, the strict selected inequalities
already force source-range rank-width.  For each source index `s`, the proof
sums the inequalities for the other `L` indices, cancels the positive `L`, and
gets `0 < H(s)-r`, hence `r <= H(s)`.

Lean names:
`AoyagiDefinition3SourceData.sourceRangeRankWidth_of_all_selected_strict` and
`AoyagiDefinition3SourceData.exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict`.

Nonclaims: no arbitrary branch selection, no branch-independent Theorem 2
payload, no closed form for `ceilWidth` or `aParam`, no source-rank/final
socket wrapper, no Eq5 payloads, no chart production, no pole-order theorem,
and no RLCT theorem.

Latest A6 Definition 3 `ell=1` source-data formula:
Proved that a supplied `AoyagiDefinition3SourceData L 1 H r C`, together with
source-range rank-width, supplies all hypotheses needed by the arbitrary-depth
`ell=1` selected-pair formula package.  The selected widths are
`u=H(C.cut 0)-r` and `v=H(C.cut 1)-r`, and the finite formula data has
`ceilWidth=u+v`, `aParam=1`, order `1`, pair sum `u*v`, and lambda
`regularTerm+u*v/2`.

Lean name:
`AoyagiDefinition3SourceData.exists_ell_one_theorem2Formula_of_sourceData_rankWidth_general`.

Nonclaims: no theorem infers `ell=1`, no canonical selected pair, no
branch-independent payload for arbitrary Definition 3 data, no source-rank or
final-socket wrapper, no Eq5 payloads, no chart production, no pole-order
theorem, and no RLCT theorem.

Latest A2 Case 2 displayed-product entrywise selected-center RHS:
Lean now proves that an entrywise selected-center readout for Aoyagi's
displayed post-pivot lower product implies the submatrix selected-center RHS,
and composes this with the unreindexed residual-factor product bridge.

Lean names:
`case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_centerCoordinateSubmatrix_of_entrywise`
and
`residualFactorProduct_eq_centerCoordinateMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-case2-displayed-product-entrywise-selected-center-rhs.md`,
`threads/03-block-product-reduction/statement-card-a2-case2-displayed-product-entrywise-selected-center-rhs.md`,
and
`threads/03-block-product-reduction/review-a2-case2-displayed-product-entrywise-selected-center-rhs.md`.

Nonclaims: the entrywise selected-center readout remains supplied; no
construction of `Cfac`, endpoint equivalences, `Cprime`, source/image
equality, source-measure transport, normal crossings, pole order, or RLCT.

Latest A2 Case 2 displayed-product successor source-chart map:
Lean now proves that an entrywise successor source-chart-map readout for
Aoyagi's displayed post-pivot lower product implies the corresponding full
matrix identity on the successor `(S,J+1)` residual-coordinate matrix.

Lean name:
`case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_successorSourceChartMapMatrix_of_entrywise`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-case2-displayed-product-successor-source-chart-map.md`,
`threads/03-block-product-reduction/statement-card-a2-case2-displayed-product-successor-source-chart-map.md`,
and
`threads/03-block-product-reduction/review-a2-case2-displayed-product-successor-source-chart-map.md`.

Nonclaims: the entrywise successor source-chart readout remains supplied; no
selected-center readout, construction of `Cfac`, endpoint/source data,
`Cprime`, source/image equality, source-measure transport, normal crossings,
pole order, or RLCT.

Latest A2 Case 2 displayed-product entry expansion:
Lean now proves the finite matrix-product formula for each entry of Aoyagi's
displayed post-pivot lower product `D_(J+1) * C'_+`.

Lean name:
`case2DisplayedPostPivotFreeTwoEdgeFactorProduct_apply` and
`case2DisplayedPostPivotFreeTwoEdgeFactorProduct_apply_eq_sum_freeCprime`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-case2-displayed-product-entry-expansion.md`,
`threads/03-block-product-reduction/statement-card-a2-case2-displayed-product-entry-expansion.md`,
and
`threads/03-block-product-reduction/review-a2-case2-displayed-product-entry-expansion.md`.

Nonclaims: no selected-center readout, successor source-chart readout,
endpoint equivalence, construction of `Cfac`, source production of `Cprime`,
source/image equality, source-measure transport, normal crossings, pole order,
or RLCT.

Latest A2 Case 2 source-chart CenterCoord alignment:
Lean now proves that Aoyagi's displayed Case 2 source-chart map for the old
center is definitionally the same as
`SelectedEntrySignedBox.CenterCoord.chartMap` at the displayed pivot.

Lean name:
`case2DisplayedSourceChartMap_eq_selectedEntrySignedBoxCenterCoord_chartMap_apply`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-case2-source-chart-centercoord-alignment.md`,
`threads/03-block-product-reduction/statement-card-a2-case2-source-chart-centercoord-alignment.md`,
and
`threads/03-block-product-reduction/review-a2-case2-source-chart-centercoord-alignment.md`.

Nonclaims: no post-pivot product readout, successor source-chart readout,
endpoint equivalence, source image, source-measure transport, normal
crossings, pole order, or RLCT.

Latest A2 Case 2 successor readout CenterCoord matrix:
Lean now proves that a supplied entrywise successor source-chart readout for
the displayed Case 2 post-pivot lower product gives the successor
selected-entry `CenterCoord.chartMap` matrix for the unreindexed two-edge
residual-factor product.

Lean name:
`residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-case2-successor-readout-centercoord-matrix.md`,
`threads/03-block-product-reduction/statement-card-a2-case2-successor-readout-centercoord-matrix.md`,
and
`threads/03-block-product-reduction/review-a2-case2-successor-readout-centercoord-matrix.md`.

Nonclaims: the successor readout, endpoint equivalences, compatible factors,
`Cprime` production, source/image equality, source-measure transport, normal
crossings, pole order, and RLCT remain supplied or open.

Latest A2 Case 2 concrete two-edge factor family:
Lean now defines the concrete displayed Case 2 two-edge endpoint family
`tau -> Case2ResidualColIndex n S (J+1) -> Case2ResidualRowIndex n S (J+1)`
and proves that its `residualFactorProduct` is exactly
`case2DisplayedPostPivotFreeTwoEdgeFactorProduct`.  A downstream specialization
also proves the successor selected-entry `CenterCoord.chartMap` matrix theorem
for this concrete family from the still-supplied entrywise successor readout.

Lean names:
`case2PostPivotTwoEdgeDomain`,
`case2PostPivotFreeTwoEdgeFactorFamily`,
`residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_freeTwoEdgeFactorProduct`,
and
`residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_entrywise`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-case2-concrete-two-edge-factor-family.md`,
`threads/03-block-product-reduction/statement-card-a2-case2-concrete-two-edge-factor-family.md`,
and
`threads/03-block-product-reduction/review-a2-case2-concrete-two-edge-factor-family.md`.

Nonclaims: the successor readout, source production of `Cprime`, successor
source data, source/image equality, source-measure transport, normal crossings,
pole order, and RLCT remain supplied or open.

Latest A2 Case 2 paper-Cprime source-following product:
Lean now proves that, for Aoyagi's paper `C' = Q^-1 C`, the concrete Case 2
two-edge residual-factor product is the source residual block at `(S,J+1)`
times the formula-level successor following factor restricted to the same next
residual domain.

Lean name:
`residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_paperCprime_eq_sourceResidualBlock_successorFollowingFactor`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-case2-paper-cprime-source-following-factor-product.md`,
`threads/03-block-product-reduction/statement-card-a2-case2-paper-cprime-source-following-factor-product.md`,
and
`threads/03-block-product-reduction/review-a2-case2-paper-cprime-source-following-factor-product.md`.

Nonclaims: no successor `yNext`, selected-entry readout, source production of
successor chart data/suffixes/terminal rows, source/image equality, chart
coverage, normal crossings, pole order, or RLCT.

Latest A2 Case 2 post-pivot compatible residual-factor identity audit:
`threads/03-block-product-reduction/reproduction-a2-case2-post-pivot-compatible-residual-factor-identity.md`
kills the unqualified source claim that `D_(J+1) * C'_+` is already the
successor selected-entry `CenterCoord.chartMap` matrix. Aoyagi pp. 19-21
support the `Q/P` algebra, the paper-`C'` lower-tail identity, and the
post-pivot product, but the next selected-entry chart is on `D_(J+1)`, not on
the product with the following factor. The successor entrywise readout,
endpoint equivalence, source data, source/image equality, normal crossings,
pole order, and RLCT remain supplied or open. Post-recovery Lean/API recheck
also records that a finite inverse-chart repair would require a nonzero fixed
successor pivot; existing all-pivot coverage can choose some pivot and does
not provide the fixed successor pivot `(J+2,J+2)`. Review:
`threads/03-block-product-reduction/review-a2-case2-post-pivot-compatible-residual-factor-identity.md`.

Latest A2 Schur-core formal Jacobian unit:
Lean now proves the fixed-`B` Schur-core formal tangent map from Aoyagi Lemma 2
and Theorem 3 is invertible, and that its determinant is a unit in the finite
side-index case.

Lean names:
`SchurCoreTangent`,
`schurCoreFormalJacobian`,
`schurCoreFormalJacobianInverse`,
`schurCoreFormalJacobianEquiv`,
and
`schurCoreFormalJacobian_det_isUnit`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-schur-core-formal-jacobian-unit.md`,
`threads/03-block-product-reduction/statement-card-a2-schur-core-formal-jacobian-unit.md`,
and
`threads/03-block-product-reduction/review-a2-schur-core-formal-jacobian-unit.md`.

Nonclaims: no nonlinear analytic derivative theorem, source-measure
pushforward, density transport, exact determinant exponent/sign, full p.13
product-step Jacobian, normal crossings, pole order, or RLCT.

Latest A2 product-step fixed-passive formal Jacobian unit:
Lean now proves that the fixed-passive p. 13 one-step formal tangent map is a
linear equivalence, and that its finite determinant is a unit.

Lean names:
`ProductStepFixedPassiveRawTangent`,
`ProductStepFixedPassiveChartTangent`,
`productStepFixedPassiveFormalJacobian`,
`productStepFixedPassiveFormalJacobianInverse`,
`productStepFixedPassiveFormalJacobianEquiv`,
and
`productStepFixedPassiveFormalJacobian_det_isUnit`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-product-step-fixed-passive-formal-jacobian-unit.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-fixed-passive-formal-jacobian-unit.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-fixed-passive-formal-jacobian-unit.md`.

Nonclaims: this slice varies only `C1`, old `F3`, `A2`, and `A4`, with `D`,
`A1`, and `A3` fixed. It is not the full p. 13 product-step Jacobian, not an
analytic derivative theorem, not source-measure pushforward or density
transport, and not normal crossings, pole order, or RLCT.

Latest A2 full product-step formal Jacobian formulas:
Lean now records the full p. 13 one-step formal tangent formulas, including
the `dD`, `dA1`, and `dA3` terms, and a chart-output reorder equivalence for
future determinant statements.

Lean names:
`ProductReductionStepRawTangent`,
`ProductReductionStepChartTangent`,
`productReductionStepFormalJacobianFormula`,
`productReductionStepFormalJacobianInverseFormula`,
and
`productReductionStepChartTangentRawOrderEquiv`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-product-step-full-formal-jacobian-formulas.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-full-formal-jacobian-formulas.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-full-formal-jacobian-formulas.md`.

Nonclaims: no bundled full `LinearMap`, no full raw/chart `LinearEquiv`, no
determinant-unit theorem, no analytic derivative theorem, no source-measure
pushforward or density transport, and no normal crossings, pole order, or
RLCT.

Latest A2 product-step inverse Jacobian density:
Lean now proves local continuity, positivity, and positive lower/upper
eventual bounds for the chart-side reciprocal density
`|det D Phi(Phi^{-1}(y))|^{-1}` on the raw-shaped target determinant chart.

Lean names:
`continuousAt_productReductionStepChartRawOrderToRawTopologyTuple_of_mem_rawDetChartSet`,
`productReductionStepRawOrderInverseJacobianDensity`,
`productReductionStepRawOrderInverseJacobianDensity_pos`,
`continuousAt_productReductionStepRawOrderInverseJacobianDensity_of_mem_rawDetChartSet`,
`exists_pos_eventually_le_productReductionStepRawOrderInverseJacobianDensity_nhds`,
and
`exists_pos_eventually_productReductionStepRawOrderInverseJacobianDensity_le_nhds`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-product-step-inverse-jacobian-density.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-inverse-jacobian-density.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-inverse-jacobian-density.md`.

Nonclaims: this is not an unweighted source-measure pushforward theorem, not
original DLN source/prior transport, not source coverage, not normal
crossings, not pole order, and not RLCT.

Latest A2 full product-step bundled formal linear maps:
Lean now bundles the full p. 13 forward and inverse formal tangent formulas as
`LinearMap`s and proves that applying these maps is exactly the already
reviewed tuple formula.

Lean names:
`productReductionStepFormalJacobian`,
`productReductionStepFormalJacobian_apply`,
`productReductionStepFormalJacobianInverse`,
and
`productReductionStepFormalJacobianInverse_apply`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-product-step-full-linear-maps.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-full-linear-maps.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-full-linear-maps.md`.

Nonclaims: no full raw/chart `LinearEquiv`, no determinant-unit theorem, no
analytic derivative theorem, no source-measure pushforward or density
transport, and no normal crossings, pole order, or RLCT.

Latest A2 p.13 regular-coordinate inverse-density handoff:
Lean now defines the concrete left-endpoint raw-shaped target tuple for the
explicit p. 13 regular-coordinate family:

```text
(Ctop(u), Dtail(x), F3(u), Ctop(u), F2(u), 0, C0(x)).
```

Lean proves centered determinant-chart membership, self-base continuity, and
continuity/positivity of the chart-side inverse product-step Jacobian density
along this tuple.

Lean names:
`paperEndpointFixedBaseP13RawOrderTuple`,
`paperEndpointFixedBaseP13RawOrderTuple_mem_rawDetChartSet`,
`paperEndpointFixedBaseP13RawOrderTuple_mem_rawDetChartSet_center`,
`continuousAt_paperEndpointFixedBaseP13RawOrderTuple_selfBase`,
`continuousAt_paperEndpointFixedBaseP13RawOrderTuple_inverseJacobianDensity_selfBase`,
and
`paperEndpointFixedBaseP13RawOrderTuple_inverseJacobianDensity_pos_center`.

## A2 retained-passive small-box chart-produced residual bound

Status: Proved in Lean locally; focused build passed; independent xhigh review
passed for the fixed-radius and continuous-density small-box wrappers.

Claim: for the concrete selected-entry chart-produced retained-passive source
measure, the residual square-sum is bounded by `Rreg^2` a.e. on the
retained-passive p.13 local-source restriction whenever the signed-box radii
are bounded by `delta` and

```text
delta^2 * (1 + #(center.erase pivot) * delta^2) <= Rreg^2.
```

Lean declarations:

```text
residualSquareSum_le_sq_ae_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_of_residual_eq_of_smallBox
residualSquareSum_le_sq_ae_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceEdgeFamilyOfData_chartProducedMeasure_of_smallBox
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure_of_smallBox
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure_continuousAt_pos_density_of_smallBox
```

The last theorem is the positive continuous-density version.  It chooses
`R <= Rmax` first, then requires the selected-entry small-box scalar inequality
at `R^2`, with `delta` quantified after the produced `R`.

Kill condition: reject any use that treats a bound at `Rmax` as a bound at a
smaller produced radius, or that applies the theorem to an arbitrary source
measure rather than the selected-entry chart-produced measure.

Nonclaims: no radius choice, no source-rank coverage, no loss/density
comparison proof, no external source-prior/Jacobian transport, no normal
crossings, pole order, or RLCT.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-small-box-chart-produced-residual-bound.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-small-box-chart-produced-residual-bound.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-small-box-chart-produced-residual-bound.md`
passed by xhigh `Carson the 2nd` for the fixed-radius slice and xhigh
`Huygens the 3rd` for the continuous-density small-box wrapper.

## A2 Case 2 endpoint-transport continuous-density small-box two-sided iff

Status: Proved in Lean locally; focused build passed.

Claim: for the explicit endpoint-transported continuing Case 2 selected-entry
source chart, the generic retained-passive positive-continuous-density
small-box source-stratum iff applies with all abstract retained-passive inputs
discharged by the concrete Case 2 construction.

Lean declaration:

```text
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_continuousAt_pos_density_of_smallBox
```

The theorem keeps endpoint equivalences, fixed-base source data, `[SFinite nu]`,
`nu.IsAddHaarMeasure`, positive `Rmax/cLreg/CLreg/t`, positive continuity of
the density at `(base,0)`, and both source-stratum loss comparison bounds at
`Rmax` explicit.  It returns `R dρ Dρ` and only then quantifies `delta`,
checking the selected-entry small-box scalar inequality at `R^2`.

Kill condition: reject any downstream use that treats this as source-rank
coverage, source/image equality, original source-prior transport, Jacobian
comparison, normal crossings, pole order, or RLCT.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-case2-endpoint-transport-continuous-density-small-box-two-sided-iff.md`
and
`threads/03-block-product-reduction/statement-card-a2-case2-endpoint-transport-continuous-density-small-box-two-sided-iff.md`.
Review:
`threads/03-block-product-reduction/review-a2-case2-endpoint-transport-continuous-density-small-box-two-sided-iff.md`
passed by xhigh `Poincare the 3rd`.
Focused build, `scripts/sorries`, `git diff --check`, touched Lean-file
forbidden-marker scan, and direct axiom probe passed; the theorem reports only
`[propext, Classical.choice, Quot.sound]`.

## A2 Case 2 source-stratum-supported continuous-density small-box two-sided iff

Status: Proved in Lean locally; focused build passed.

Claim: under the explicit uniform Case 2 rank equations, the
endpoint-transported chart-produced source measure is supported on the
source-rank stratum, so the Case 2 continuous-density small-box iff can be
restated over `mu.restrict U` and `residualNegPowerIntegrableOn ... U mu t`.

Lean declaration:

```text
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_continuousAt_pos_density_of_smallBox_restrict_open_of_sourceRankSupport
```

Kill condition: reject any downstream use that treats the explicit rank
equations as proved coverage, source/image equality, exact-rank openness,
original source-prior transport, Jacobian comparison, normal crossings, pole
order, or RLCT.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-case2-source-stratum-supported-continuous-density-small-box-two-sided-iff.md`,
`threads/03-block-product-reduction/statement-card-a2-case2-source-stratum-supported-continuous-density-small-box-two-sided-iff.md`,
and
`threads/03-block-product-reduction/review-a2-case2-source-stratum-supported-continuous-density-small-box-two-sided-iff.md`.
Focused build, `scripts/sorries`, `git diff --check`, touched Lean-file
forbidden-marker scan, and direct axiom probe passed; the theorem reports only
`[propext, Classical.choice, Quot.sound]`.

## A2 retained-passive Ctop tail endpoint substitution

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-product-step-regular-coordinate-inverse-density.md`
and
`threads/03-block-product-reduction/statement-card-a2-product-step-regular-coordinate-inverse-density.md`.

Reproduction check: xhigh scouts `Gauss the 2nd` and `Nash the 2nd`
confirmed the tuple order, `A1 = Ctop(u)`, determinant-chart membership, and
API shape.  Xhigh reviewer `Descartes the 2nd` accepted the Lean slice after
the `_center` positivity rename and aggregate-comment fix; review at
`threads/03-block-product-reduction/review-a2-product-step-regular-coordinate-inverse-density.md`.

Nonclaims: no source coverage, original DLN source/prior transport,
unweighted measure transport, normal crossings, pole order, or RLCT.

Latest A2 p.13 product-step inverse-density finite-integral handoff:
Lean now specializes two existing p.13 local finite-integral handoffs to the
concrete chart-side inverse product-step Jacobian density along the
left-endpoint regular-coordinate tuple.

Lean names:
`exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_continuousAt_selfBase`
and
`exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_selfBase`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-product-step-inverse-density-finite-integral-handoff.md`
and
`threads/03-block-product-reduction/statement-card-a2-product-step-inverse-density-finite-integral-handoff.md`.
Review:
`threads/03-block-product-reduction/review-a2-product-step-inverse-density-finite-integral-handoff.md`.

Nonclaims: no source coverage, p.13 product chart construction, product-step
pushforward identity, original source/prior transport, signed-box density
identification, normal crossings, pole order, or RLCT.

Latest A2 original-loss product-step inverse-density handoff:
`OriginalLossLocalMeasure.lean` now specializes the original-loss edge-matrix
product-family finite-integral front end to the concrete chart-side inverse
product-step Jacobian density along `paperEndpointFixedBaseP13RawOrderTuple`.
Lean name:
`exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase`.
Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-original-loss-product-step-inverse-density-handoff.md`
and
`threads/03-block-product-reduction/statement-card-a2-original-loss-product-step-inverse-density-handoff.md`.
Review:
`threads/03-block-product-reduction/review-a2-original-loss-product-step-inverse-density-handoff.md`.

Nonclaims: no p.13 source/product chart construction, source coverage,
product-step/source pushforward, signed-box density identification, original
prior transport, normal crossings, pole order, or RLCT.

Latest A2 suffix-step raw-order inverse-density handoff:
Lean now defines the arbitrary suffix-step raw-shaped target tuple obtained by
applying the raw-order product-step coordinate map to
`ChartLocalSuffixState.stepRawCoordinates`.  It proves determinant-chart
membership, raw and target tuple continuity, and chart-side inverse-density
continuity/positivity for arbitrary suffix steps.

Lean names:
`continuousAt_productReductionStepTopologyTupleToChartRawOrder_of_mem_rawDetChartSet`,
`chartLocalSuffixStateStepRawOrderTargetTuple`,
`chartLocalSuffixStateStepRawOrderTargetTuple_mem_rawDetChartSet`,
`continuousAt_chartLocalSuffixState_stepRawCoordinates_topologyTuple`,
`continuousAt_chartLocalSuffixStateStepRawOrderTargetTuple_of_raw`,
`continuousAt_chartLocalSuffixStateStepRawOrderTargetTuple`,
`continuousAt_chartLocalSuffixStateStepRawOrderTargetTuple_inverseJacobianDensity`,
`continuousAt_chartLocalSuffixStateStepRawOrderTargetTuple_inverseJacobianDensity_of_fields`,
and
`chartLocalSuffixStateStepRawOrderTargetTuple_inverseJacobianDensity_pos`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-suffix-step-raw-order-inverse-density.md`
and
`threads/03-block-product-reduction/statement-card-a2-suffix-step-raw-order-inverse-density.md`.
Review:
`threads/03-block-product-reduction/review-a2-suffix-step-raw-order-inverse-density.md`.

Nonclaims: no source coverage, product-chart construction for the original DLN
source, product-step pushforward identity, original source/prior transport,
signed-box density identification, normal crossings, pole order, or RLCT.

Latest A2 raw-order inverse-density pushforward:
Lean now proves the raw determinant-chart unweighted pushforward identity for
the p.13 product-step map.  For an additive Haar measure `m` on the raw tuple
space,

```text
Measure.map productReductionStepTopologyTupleToChartRawOrder
  (m.restrict productReductionStepRawDetChartSet)
=
(m.restrict productReductionStepRawDetChartSet).withDensity
  (fun y => ofReal (productReductionStepRawOrderInverseJacobianDensity y)).
```

Lean names:
`productReductionStepRawOrderInverseJacobianDensity_apply_chartMap`,
`productReductionStepRawOrderJacobianAbsDet_mul_inverseJacobianDensity_apply_chartMap`,
and
`map_productReductionStepRawOrder_restrict_detChart_eq_withDensity_inverseJacobian`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-product-step-raw-order-inverse-density-pushforward.md`
and
`threads/03-block-product-reduction/statement-card-a2-product-step-raw-order-inverse-density-pushforward.md`.
Review:
`threads/03-block-product-reduction/review-a2-product-step-raw-order-inverse-density-pushforward.md`.

Nonclaims: this is raw product-chart Haar transport only.  It is not original
DLN source/prior transport, source coverage, p.13 source-chart construction,
signed-box density identification, regular-suspension construction, normal
crossings, pole order, or RLCT.

Latest A2 p.13 raw product-step preimage:
Lean now defines the raw source tuple

```text
(I,Dtail(x),F3(u),Ctop(u),-Ctop(u)*F2(u),0,C0(x))
```

and proves that, under `IsUnit det(Ctop(u))`, it lies in the raw source
determinant chart and maps under `productReductionStepTopologyTupleToChartRawOrder`
to the existing p.13 raw-shaped target tuple

```text
(Ctop(u),Dtail(x),F3(u),Ctop(u),F2(u),0,C0(x)).
```

Lean names:
`paperEndpointFixedBaseP13RawPreimageTuple`,
`paperEndpointFixedBaseP13RawPreimageTuple_mem_rawDetChartSet`,
`paperEndpointFixedBaseP13RawPreimageTuple_mem_rawDetChartSet_center`,
and
`productReductionStepTopologyTupleToChartRawOrder_paperEndpointFixedBaseP13RawPreimageTuple`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-p13-raw-product-step-preimage.md`
and
`threads/03-block-product-reduction/statement-card-a2-p13-raw-product-step-preimage.md`.
Review passed at
`threads/03-block-product-reduction/review-a2-p13-raw-product-step-preimage.md`.
Xhigh review found no correctness or scope issues.

Nonclaims: this is raw product-chart algebra only.  It is not source coverage,
p.13 source-chart construction from original DLN coordinates, source/prior
transport, signed-box density identification, product-measure pushforward,
regular-suspension certification, normal crossings, pole order, or RLCT.

Latest A2 p.13 product-coordinate left-step raw preimage:
Lean now defines the constructed source-dependent p.13 multi-edge
product-coordinate matrix family and proves that its actual left-endpoint
suffix-step raw coordinates are exactly

```text
(I,Dtail(x),F3(u),Ctop(u),-Ctop(u)*F2(u),0,C0(x)).
```

Under `IsUnit det(Ctop(u))`, the corresponding raw-order suffix-step target
tuple is the explicit p.13 raw-shaped target tuple

```text
(Ctop(u),Dtail(x),F3(u),Ctop(u),F2(u),0,C0(x)).
```

Lean names:
`paperEndpointFixedBaseP13ProductCoordinateMatrixFamily`,
`p13ProductCoordinateLeftStepRawTopologyTuple_eq_rawPreimageTuple`, and
`p13ProductCoordinateLeftStepRawOrderTargetTuple_eq_rawOrderTuple`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-p13-product-coordinate-left-step-raw-preimage.md`
and
`threads/03-block-product-reduction/statement-card-a2-p13-product-coordinate-left-step-raw-preimage.md`.
Review:
`threads/03-block-product-reduction/review-a2-p13-product-coordinate-left-step-raw-preimage.md`
passed after low-severity naming and stale-note repairs.

Nonclaims: this is pointwise finite product-coordinate algebra only.  It is
not source coverage, p.13 source-chart construction from original DLN
coordinates, source/prior transport, signed-box density identification,
product-measure pushforward, regular-suspension certification, normal
crossings, pole order, or RLCT.

Latest A2 p.13 left-step raw tuple measurability:
Lean now proves that the explicit p.13 raw preimage tuple and the actual
constructed left-step raw tuple are measurable from fixed-base edge-matrix
measurability.  It adds suffix-recursion projections for the residual product
and residual block, then derives raw-tuple measurability and a.e.
measurability for `p13ProductCoordinateLeftStepRawTopologyTuple`.  The
conditional p.13 inverse-Jacobian consumer now has a wrapper that takes
fixed-base edge-matrix measurability plus the same explicit raw pushforward
hypothesis, deriving the raw tuple a.e.-measurability input internally.

Lean names:
`measurable_chartLocalSuffixState_residualProduct_real`,
`measurable_chartLocalSuffixState_residualBlock_real`,
`measurable_paperEndpointFixedBaseP13RawPreimageTuple_of_measurable_edgeMatrix`,
`aemeasurable_paperEndpointFixedBaseP13RawPreimageTuple_of_measurable_edgeMatrix`,
`measurable_p13ProductCoordinateLeftStepRawTopologyTuple_of_measurable_edgeMatrix`,
`aemeasurable_p13ProductCoordinateLeftStepRawTopologyTuple_of_measurable_edgeMatrix`,
and
`map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map_of_measurable_edgeMatrix`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-p13-left-step-raw-tuple-measurability.md`,
`threads/03-block-product-reduction/statement-card-a2-p13-left-step-raw-tuple-measurability.md`,
and
`threads/03-block-product-reduction/review-a2-p13-left-step-raw-tuple-measurability.md`.

Nonclaims: this does not prove the supplied raw pushforward.  It is not source
coverage, original DLN source/prior transport, signed-box density
identification, product-measure pushforward, regular-suspension
certification, normal crossings, pole order, or RLCT.

Latest A2 p.13 left-step section-image measure:
After xhigh source, Lean/API, and pen-and-paper checks of the p.13 raw-Haar
boundary, Lean now proves the honest section-level measure identity
`map_p13RawOrderTuple_eq_map_leftStepRawOrder_image_of_measurable_edgeMatrix`.
Under fixed-base edge-matrix measurability and a.e. raw determinant-chart
support for the actual left-step raw tuple `X`, the p.13 target tuple `Y`
satisfies

```text
Measure.map Y eta = Measure.map Phi (Measure.map X eta).
```

This uses the pointwise p.13 raw-preimage algebra plus measure-map
functoriality on the section image.  It deliberately does not identify
`Measure.map X eta` with full raw Haar and does not add a density conclusion.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-p13-left-step-section-image-measure.md`
and
`threads/03-block-product-reduction/statement-card-a2-p13-left-step-section-image-measure.md`.
Review:
`threads/03-block-product-reduction/review-a2-p13-left-step-section-image-measure.md`
passed with no blocking findings.

Latest A2 p.13 left-step local raw-det support:
Lean now proves that the actual p.13 left-step raw section lands in the raw
determinant chart throughout a sufficiently small regular-coordinate ball.
The pointwise theorem rewrites the actual left-step tuple to the explicit raw
preimage tuple and uses the determinant-unit hypothesis for `Ctop(u)`; the
small-ball theorem obtains that hypothesis from continuity at `u=0`; and the
a.e. corollaries convert regular-coordinate ball support into raw-chart
support.  Lean names:
`p13ProductCoordinateLeftStepRawTopologyTuple_mem_rawDetChartSet`,
`exists_pos_radius_le_forall_p13ProductCoordinateLeftStepRawTopologyTuple_mem_rawDetChartSet`,
`ae_p13ProductCoordinateLeftStepRawTopologyTuple_mem_rawDetChartSet_of_ae_regular_mem_ball`,
and
`exists_pos_radius_le_ae_p13LeftStepRaw_mem_rawDetChartSet_of_ae_regular_mem_ball`.
Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-p13-left-step-local-raw-det-support.md`,
`threads/03-block-product-reduction/statement-card-a2-p13-left-step-local-raw-det-support.md`,
and
`threads/03-block-product-reduction/review-a2-p13-left-step-local-raw-det-support.md`.
Nonclaims: no raw-Haar/full-chart pushforward, no source/image equality, no
source/prior transport, no signed-box density identification, no
regular-suspension certificate, no normal crossings, no pole order, and no
RLCT.

Latest A2 p.13 left-step small-ball section image:
Lean now proves the section-image measure identity under fixed-base
edge-matrix measurability and local regular-coordinate ball support.  For
every `Rmax > 0`, there is `0 < R <= Rmax` such that any local `(x,u)` measure
supported a.e. on `u in ball(0,R)` satisfies
`Measure.map Y eta = Measure.map Phi (Measure.map X eta)`, where `X` is the
actual p.13 left-step raw section, `Y` is the p.13 raw-order target tuple,
and `Phi` is the raw-order product-step map.  Lean name:
`exists_pos_radius_le_map_p13RawOrderTuple_eq_map_leftStepRawOrder_image_of_ae_regular_mem_ball`.
Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-p13-left-step-small-ball-section-image.md`,
`threads/03-block-product-reduction/statement-card-a2-p13-left-step-small-ball-section-image.md`,
and
`threads/03-block-product-reduction/review-a2-p13-left-step-small-ball-section-image.md`.
Nonclaims: no full raw-Haar pushforward, no original source/prior transport,
no source coverage, no density identification, no normal crossings, no pole
order, and no RLCT.

Latest A5 Lemma 5 first-nonbase cardinal bound:
Lean now proves
`aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase_candidates_card_le` in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean`.  For a finite supplied
candidate set whose terminal chains satisfy the binary-prefix-delta endpoint
and sum hypotheses, the deterministic first-nonbase-or-base selector maps
each candidate into the counted-datum set.  If that selector is supplied
injective on the candidate set, Lean derives
`candidates.card <= a*(ell-a)+1` from the already-proved counted-datum
codomain count.

Reproduction and statement card:
`threads/05-arithmetic-tail/reproduction-lemma5-first-nonbase-cardinal-bound-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-first-nonbase-cardinal-bound.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-first-nonbase-cardinal-bound-a5.md`.

Follow-up order-notation handoff:
`aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase_candidates_card_le_theorem2OrderFormula`
is proved in
`lean/DLNFibre/DLN/Aoyagi/Lemma5FirstNonbaseOrderBridge.lean`.  Under
`data : AoyagiDefinition3CeilData ell m`, it specializes the same supplied
first-nonbase hypotheses to `a=data.aParam`, `M=data.ceilWidth` and rewrites
the bound as `candidates.card <= data.theorem2OrderFormula`.  Reproduction
and statement card:
`threads/05-arithmetic-tail/reproduction-lemma5-first-nonbase-order-formula-bound-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-first-nonbase-order-formula-bound.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-first-nonbase-order-formula-bound-a5.md`.

Nonclaims: no source vector construction, no canonical source classifier, no
injectivity proof, no back-to-label or no-extra terminal-minimum theorem, no
Eq3/Eq4/Eq5 branch construction, no finite minimum-to-`lambda` equality, no
pole order, no normal crossings, and no RLCT.

Latest A4 Case 2 finite raw-pivot chart-family boundary:
Lean now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.finiteRawPivotChartFamilyBoundary`
in `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`.  It supplies
`Case2ResidualBlockChartFamilyBoundary` with nontrivial finite predicates:
`Case2FiniteRawPivotChartRegular` records residual-block pivot membership, the
standard selected-entry formula, and finite center-ideal principalization; and
`Case2FiniteRawPivotTransitionRegular` records source/target pivot membership
plus the concrete finite affine overlap pair.

Reproduction, statement card, and review:
`threads/04-blow-up-certificate/reproduction-case2-finite-raw-pivot-chart-family-boundary-a4.md`,
`threads/04-blow-up-certificate/statement-card-a4-case2-finite-raw-pivot-chart-family-boundary.md`,
and
`threads/04-blow-up-certificate/review-case2-finite-raw-pivot-chart-family-boundary-a4.md`.

Nonclaims: finite selected-entry algebra only.  No analytic chart coverage,
analytic transition regularity, source/suffix production, source measure or
density identification, normal crossings, pole order, or RLCT.

Latest A2 p.13 passive-variable local source chart boundary:
The audit at
`threads/03-block-product-reduction/reproduction-a2-p13-passive-variable-local-source-chart-boundary.md`
records that Lemma 2, as used in Theorem 3's induction, supports the
one-step Schur/product-coordinate formulas already formalised in Lean, but it
does not by itself supply a retained-passive multi-step source chart.  The
full one-step raw determinant chart, the p.13 reduced section, and the
hypothetical retained-passive source chart are distinct objects.  No Lean
theorem was added.

Nonclaims: no local source chart, no local inverse, no source-rank coverage,
no source-measure pushforward, no density/Jacobian identity, no normal
crossings, no pole order, and no RLCT.

Latest A2 product-step A1 formal inverse:
Lean now proves
`productReductionStepCoordinate_left_inverse_of_isUnit_A1` and
`productReductionStepCoordinate_right_inverse_of_isUnit_A1` in
`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`.  These are record-level
formal inverse laws for the p.13 one-step coordinate change under only
`IsUnit A1.det`; the older determinant-chart inverse names remain wrappers
for chart-domain use.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-product-step-a1-formal-inverse.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-a1-formal-inverse.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-a1-formal-inverse.md`.

Nonclaims: finite coordinate algebra only.  No weakening of derivative or
measure determinant-chart hypotheses, no source coverage, no source-measure
transport, no density/Jacobian identity, no normal crossings, no pole order,
and no RLCT.

Latest A2 product-step formal Jacobian A1 unit:
Lean now proves A1-only versions of the full p.13 formal tangent equivalence
and raw-order finite determinant-unit theorem in
`lean/DLNFibre/DLN/Aoyagi/ProductReductionStepJacobian.lean`.  The formal
inverse-composition laws use only `IsUnit A1.det`; terms containing
`(C1*A1)^-1` cancel additively and are not used through a `Ctop` determinant
unit hypothesis.

Lean names:
`productReductionStepFormalJacobianInverseFormula_formula_chartBase_of_isUnit_A1`,
`productReductionStepFormalJacobianFormula_inverseFormula_chartBase_of_isUnit_A1`,
`productReductionStepFormalJacobianEquiv_of_isUnit_A1`,
`productReductionStepFormalJacobianEquiv_of_isUnit_A1_apply`,
`productReductionStepFormalJacobianEquiv_of_isUnit_A1_symm_apply`,
`productReductionStepFormalJacobianRawOrderEquiv_of_isUnit_A1`,
`productReductionStepFormalJacobianRawOrderEquiv_of_isUnit_A1_apply`,
and
`productReductionStepFormalJacobianRawOrder_det_isUnit_of_isUnit_A1`.

The older determinant-chart names remain wrappers with the old visible
`hC1 hA1` call shape.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-product-step-formal-jacobian-a1-unit.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-formal-jacobian-a1-unit.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-formal-jacobian-a1-unit.md`.

Nonclaims: finite formal tangent algebra only.  No weakening of analytic
derivative/measure determinant-chart hypotheses, no source coverage, no
source-measure transport, no density/Jacobian identity for the original DLN
source, no normal crossings, no pole order, and no RLCT.

Latest A5 Eq5 endpoint first-nonbase upper bound:
Lean now proves
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_eq5EndpointChain_firstInteriorNonbase`
in `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`.  For a supplied
terminal-candidate family, explicit Eq5 endpoint-chain data for every label in
`TC.terminalMinimumLabels` give the upper bound
`TC.terminalMinimumLabels.card <= a*(N+1-a)+1`, provided the deterministic
first-nonbase-or-base selector is supplied injective on
`TC.terminalMinimumLabels`.

Reproduction and statement card:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-minimum-counted-datum-classifier-source-attempt-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-first-nonbase-upper-bound.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-first-nonbase-upper-bound-a5.md`.

The same reproduction records the source obstruction: Aoyagi Lemma 5, PDF
pp. 24-27, gives the interval-count shape but not a Lean-level
`TC.TerminalMinimumCountDatumClassifier`, classifier injectivity, or
back-to-label map for arbitrary terminal-minimum labels.

Nonclaims: no source-backed classifier, no proof of selector injectivity,
no branch-label injectivity, no back-to-label/no-extra theorem, no terminal
exactness, no pole order, no normal crossings, and no RLCT.

Latest A2 retained-passive Ctop determinant chart:
Lean now proves the recursive Ctop tracking theorem in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`.  The new names are
`ChartLocalSuffixState.step_retainedPassiveFixedBaseEdgeMatrix_Ctop`,
`ChartLocalSuffixState.suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix_castSucc`,
and
`ChartLocalSuffixState.suffixState_Ctop_det_isUnit_retainedPassiveFixedBaseEdgeMatrix`.
Under the retained-passive fixed-base reconstruction, the deterministic
suffix-state recursion satisfies `Ctop_p = Ctop_{p+1} * A1_p`, and all
recursive `Ctop` determinants are units if `F2_last=0` and every `det(A1_p)`
is a unit.

Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-ctop-det-chart.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-ctop-det-chart.md`.

Nonclaims: finite suffix-state determinant-chart bookkeeping only.  No active
endpoint recovery for `A1_0` or `A3_last`, no retained-passive coordinate
domain with active `Ctop_0` plus passive `A1_p` for `p > 0`, no source-rank
coverage, no source/image equality, no source-measure pushforward, no
density/Jacobian theorem, no normal crossings, no pole order, and no RLCT.

Latest A2 retained-passive A1 readback:
Lean now proves the constructor-side theorem
`ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrix_A1_eq_suffixState_Ctop_inv_mul_Ctop`
in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`.  For the full
reconstructed determinant-unit `A1` family, adjacent suffix-state top blocks
recover the supplied factor by `A1_p = Ctop_{p+1}^-1 * Ctop_p`.

Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-a1-readback.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-a1-readback.md`.

Nonclaims: this is not yet the retained-passive coordinate-domain endpoint
theorem.  At `p=0`, `A1_0` is still supplied and determinant-unit; Lean has not
yet constructed it from active `Ctop_0=I+X` and passive `A1_p` for `p>0`.
No `A3_last` recovery, source-rank coverage, source/image equality,
source-measure pushforward, density/Jacobian theorem, normal crossings, pole
order, or RLCT is proved.

Latest A2 retained-passive D/L recurrences:
Lean now proves the retained-passive Schur residual, residual-field, and
one-step lower-unitriangular recurrences in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`.  Main names:
`ChartLocalSuffixState.schurResidualBlock_retainedPassiveTransformedEdge`,
`ChartLocalSuffixState.step_retainedPassiveFixedBaseEdgeMatrix_D`,
`ChartLocalSuffixState.suffixState_D_retainedPassiveFixedBaseEdgeMatrix`,
`ChartLocalSuffixState.step_retainedPassiveFixedBaseEdgeMatrix_L`, and
`ChartLocalSuffixState.step_retainedPassiveFixedBaseEdgeMatrix_lowerLeftBlock_L`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-d-l-recurrence.md`,
`threads/03-block-product-reduction/statement-card-a2-retained-passive-d-l-recurrence.md`,
and
`threads/03-block-product-reduction/review-a2-retained-passive-d-l-recurrence.md`.

Nonclaims: no iterated `F3_0` finite-sum formula, no `A3_last` solve, no
retained-passive coordinate-domain theorem, no source-rank coverage, no
source/image equality, no source-measure pushforward, no density/Jacobian
theorem, no normal crossings, no pole order, and no RLCT.

Latest A2 retained-passive lower-left L recursion:
Lean now proves the actual suffix-state lower-left recurrence in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`:
`ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_castSucc`
and
`ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_castSucc_currentCtop`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-l-lowerleft-recursion.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-l-lowerleft-recursion.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-l-lowerleft-recursion.md`.

Nonclaims: one-edge recursive bookkeeping only.  No iterated finite-sum formula
for `F3_0`, no `A3_last` solve, no retained-passive coordinate-domain theorem,
no source-rank coverage, no source/image equality, no source-measure
pushforward, no density/Jacobian theorem, no normal crossings, no pole order,
and no RLCT.

Latest A2 retained-passive lower-left L tail sum:
Lean now proves the iterated finite lower-left formula in recursive-tail form
in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`.  Main names:
`ChartLocalSuffixState.retainedPassiveLowerLeftTailSum`,
`ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_eq_tailSum`,
`ChartLocalSuffixState.suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix`,
`ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum`,
`ChartLocalSuffixState.retainedPassiveLowerLeftTailSum_eq_productTailSum`, and
`ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_eq_productTailSum`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-l-tail-sum.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-l-tail-sum.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-l-tail-sum.md`.

Nonclaims: recursive finite algebra only.  No `A3_last` solve, no
retained-passive coordinate-domain theorem, no source-rank coverage, no
source/image equality, no source-measure pushforward, no density/Jacobian
theorem, no normal crossings, no pole order, and no RLCT.

Latest A2 retained-passive final-edge endpoint solve:
Lean now proves the local nonempty-edge endpoint cancellation in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`.  Main names:
`ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_last` and
`ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_last_eq_of_A3_eq_neg_target_mul_Ctop`.
At the final edge, the explicit product tail unfolds to
`-(I*A3_last*Ctop_last^-1)`, and if `det(Ctop_last)` is a unit and
`A3_last=-G*Ctop_last`, the final tail is `G`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-a3-last-endpoint-solve.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-a3-last-endpoint-solve.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-a3-last-endpoint-solve.md`.

Nonclaims: local final-summand algebra only.  It does not construct the full
prefix target `G=F3_0+prefix`, the retained-passive coordinate domain, source
coverage, source/image equality, source-measure pushforward, density/Jacobian
transport, normal crossings, pole order, or RLCT.

Latest A2 retained-passive `A3_last` prefix target:
Lean now proves the finite source-tail target theorem in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`.  Main names:
`ChartLocalSuffixState.retainedPassiveA3WithoutLast`,
`ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_eq_withoutLast_add_last`,
and
`ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_zero_eq_target_of_A3_last_eq`.
The final-zeroed tail is the signed earlier contribution.  If
`A3_last=-(F3-EarlyTail)*Ctop_last` and `det(Ctop_last)` is a unit, the full
source product tail is `F3`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-a3-last-prefix-target.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-a3-last-prefix-target.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-a3-last-prefix-target.md`.

Nonclaims: finite tail algebra only.  No full retained-passive coordinate
domain, no active `Ctop_0`/`A1_0` reconstruction, no determinant-unit
neighborhood theorem, no source coverage, no source/image equality, no
source-measure pushforward, no density/Jacobian theorem, no normal crossings,
no pole order, and no RLCT.

Latest A2 retained-passive `A1_0` endpoint target:
Lean now proves the finite top-left endpoint solve in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`.  Main names:
`ChartLocalSuffixState.retainedPassiveA1TailAfterFirst`,
`ChartLocalSuffixState.retainedPassiveA1TailAfterFirst_mul_first`,
`ChartLocalSuffixState.retainedPassiveA1TailAfterFirst_det_isUnit_of_passive`,
`ChartLocalSuffixState.retainedPassiveCtopProduct_zero_eq_target_of_A1_zero_eq`,
`ChartLocalSuffixState.retainedPassiveA1_zero_det_isUnit_of_A1_zero_eq_tail_inv_mul`,
`ChartLocalSuffixState.retainedPassiveA1_det_isUnit_of_A1_zero_eq_tail_inv_mul`,
and
`ChartLocalSuffixState.suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix_zero_eq_target_of_A1_zero_eq`.
If `Tail=A1_last*...*A1_1`, Lean proves
`residualFactorProduct A1 last 0 = Tail*A1_0`; with
`A1_0=Tail^-1*Ctop`, the product is `Ctop`.  The tail determinant-unit
hypothesis is derived from passive unit hypotheses for all `p != 0`, so
`det(Ctop)` unit gives a full determinant-unit `A1` family and the suffix-state
endpoint `(suffixState E last 0).Ctop=Ctop`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-a1-first-endpoint-target.md`,
`threads/03-block-product-reduction/statement-card-a2-retained-passive-a1-first-endpoint-target.md`,
and
`threads/03-block-product-reduction/review-a2-retained-passive-a1-first-endpoint-target.md`.

Nonclaims: finite top-left endpoint algebra only.  No full retained-passive
coordinate-domain theorem, no `F2` readback packaging, no combined
`A3_last`/`F3` source-map theorem, no source-rank coverage, no source/image
equality, no measure pushforward, no density/Jacobian theorem, no normal
crossings, no pole order, and no RLCT.

Latest A2 retained-passive active endpoint package:
Lean now proves
`ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrix_activeEndpointFields_eq_targets`
in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`.  Under the
solved endpoint formulas `A1_0=Tail^-1*Ctop` and
`A3_last=-(F3-EarlyTail)*CtopLast`, plus `F2_last=0`, passive `A1_p` unit
hypotheses for `p != 0`, and `det(Ctop)` unit, the constructed fixed-base edge
family has source-left readbacks `-S_0.B=F2_0`, `S_0.Ctop=Ctop`, and
`lowerLeft(S_0.L)=F3`, and every edge has the prescribed transformed block at
the suffix state `S_{p+1}`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-active-endpoint-package.md`,
`threads/03-block-product-reduction/statement-card-a2-retained-passive-active-endpoint-package.md`,
and
`threads/03-block-product-reduction/review-a2-retained-passive-active-endpoint-package.md`.

Nonclaims: endpoint fixed-base packaging only.  No bundled coordinate-domain
structure, no two-sided local inverse, no source-rank coverage, no source/image
equality, no measure pushforward, no density/Jacobian theorem, no normal
crossings, no pole order, and no RLCT.

Latest A2 retained-passive transformed-edge readbacks:
Lean now proves the per-edge readbacks for the retained-passive transformed
block and its fixed-base deterministic transformed-edge instance in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`.  Main names:
`ChartLocalSuffixState.retainedPassiveTransformedEdge_readbacks` and
`ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrices_transformedEdge_readbacks`.
For
`M_p=[A1_p,-A1_p F2_p; A3_p,C_p-A3_p F2_p]`, Lean proves
`topLeft(M_p)=A1_p`, `upperRight(M_p)=-A1_p*F2_p`,
`-A1_p^-1*upperRight(M_p)=F2_p` under `IsUnit det(A1_p)`,
`lowerLeft(M_p)=A3_p`, and `schurResidualBlock(M_p)=C_p`.  The fixed-base
corollary first rewrites the deterministic transformed edge to `M_p`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-transformed-edge-readbacks.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-transformed-edge-readbacks.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-transformed-edge-readbacks.md`.

Nonclaims: per-edge finite readback only.  No bundled coordinate-domain
structure, no two-sided local inverse, no source-rank coverage, no source/image
equality, no measure pushforward, no density/Jacobian theorem, no normal
crossings, no pole order, and no RLCT.

Latest A2 retained-passive fixed-base readback package:
Lean now proves
`ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrix_activeEndpointAndEdgeReadbacks_eq_targets`
in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`.  Under the
same solved-endpoint hypotheses as the active endpoint package, the fixed-base
edge family reads back source-left active fields `-S_0.B=F2_0`,
`S_0.Ctop=Ctop`, and `lowerLeft(S_0.L)=F3`, and every deterministic
transformed edge reads back `A1_p`, `F2_p`, `A3_p`, and `C_p`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-fixed-base-readback-package.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-fixed-base-readback-package.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-fixed-base-readback-package.md`.

Nonclaims: finite fixed-base packaging only.  No bundled coordinate-domain
structure, no two-sided local inverse, no source-rank coverage, no source/image
equality, no measure pushforward, no density/Jacobian theorem, no normal
crossings, no pole order, and no RLCT.

Latest A2 retained-passive solved family constructors:
Lean now defines the solved endpoint families in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`.  Main names:
`ChartLocalSuffixState.retainedPassiveSolvedA1`,
`ChartLocalSuffixState.retainedPassiveA1TailAfterFirst_solvedA1`,
`ChartLocalSuffixState.retainedPassiveSolvedA1_zero_eq_tail_inv_mul`,
`ChartLocalSuffixState.retainedPassiveSolvedA1_passive_det_isUnit`,
`ChartLocalSuffixState.retainedPassiveSolvedA3`,
`ChartLocalSuffixState.retainedPassiveA3WithoutLast_solvedA3`,
`ChartLocalSuffixState.retainedPassiveSolvedA3_last_eq_target`, and
`ChartLocalSuffixState.retainedPassiveSolvedFixedBaseEdgeMatrix_readbacks_eq_targets`.
The solved `A1` family keeps passive seed blocks away from `0` and sets
`A1_0=Tail^-1*Ctop`; the solved `A3` family keeps passive seed blocks away
from the final edge and sets `A3_last=-(F3-EarlyTail)*CtopLast`.  The wrapper
readback theorem no longer takes the `A1_0` or `A3_last` endpoint equations as
hypotheses.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-solved-family-constructors.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-solved-family-constructors.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-solved-family-constructors.md`.

Nonclaims: constructor-side finite source-map layer only.  No bundled
coordinate-domain structure, no two-sided local inverse, no source-rank
coverage, no source/image equality, no measure pushforward, no density/Jacobian
theorem, no normal crossings, no pole order, and no RLCT.

Latest A2 retained-passive coordinate-data source map:
Lean now defines
`ChartLocalSuffixState.RetainedPassiveCoordinateData` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`, with fields
`A1seed`, `F2`, `A3seed`, `C`, `Ctop`, and `F3`.  Its projections
`solvedA1`, `solvedA3`, and `edgeMatrix` build the solved full families and the
retained-passive fixed-base edge family.  The theorem
`ChartLocalSuffixState.RetainedPassiveCoordinateData.edgeMatrix_readbacks_eq_targets`
proves the source-left active readbacks and per-edge transformed-edge readbacks
from this bundled data under `F2_last=0`, passive `A1seed` unit hypotheses, and
`det(Ctop)` unit.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-coordinate-data-source-map.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-coordinate-data-source-map.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-coordinate-data-source-map.md`.

Nonclaims: finite algebraic source-map object only.  No open coordinate domain,
topology, measure, Jacobian, two-sided local inverse, source-rank coverage,
source/image equality, normal crossings, pole order, or RLCT.

Latest A2 retained-passive recoverable readbacks:
Lean now proves
`ChartLocalSuffixState.RetainedPassiveCoordinateData.edgeMatrix_recoverableReadbacks_eq_targets`
and
`ChartLocalSuffixState.RetainedPassiveCoordinateData.edgeMatrix_recoverable_ext`
in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`.  The first
theorem reads back the recoverable retained-passive coordinate fields from
`data.edgeMatrix`: source-left `F2_0`, `Ctop`, `F3`; per-edge `A1seed_p` for
`p != 0`, `F2_{p.castSucc}`, `A3seed_p` for `p != Fin.last M`, and `C_p`.
The second theorem proves the corresponding finite extensionality result for
two data objects with equal edge families.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-recoverable-readbacks.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-recoverable-readbacks.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-recoverable-readbacks.md`
passed.

Nonclaims: no full equality of coordinate-data records.  The dummy fields
`A1seed 0` and `A3seed (Fin.last M)` are not recoverable.  No open coordinate
domain, topology, measure, Jacobian, source-rank coverage, source/image
equality, normal crossings, pole order, or RLCT is proved.

Latest A2 retained-passive nonredundant coordinate data:
Lean now defines the dummy-free coordinate object
`ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`.  It stores the
actual retained-passive finite coordinates: passive `A1` fields indexed by
`Fin M`, nonterminal `F2` fields indexed by `Fin (M+1)`, passive `A3` fields
indexed by `Fin M`, all residual `C` fields, `Ctop`, and `F3`.

The embedding into `RetainedPassiveCoordinateData` fills only canonical
non-coordinate slots: `A1seed 0=0`, `A3seed (Fin.last M)=0`, and
`F2full (Fin.last (M+1))=0`.  The theorem
`RetainedPassiveNonredundantCoordinateData.edgeMatrix_readbacks_eq_targets`
recovers all stored fields from the edge family under passive `A1passive`
unit hypotheses and `det(Ctop)` unit.  The theorem
`RetainedPassiveNonredundantCoordinateData.edgeMatrix_ext` proves full
record equality for the nonredundant object from equal edge families, with the
same side conditions on both records.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-nonredundant-coordinate-data.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-nonredundant-coordinate-data.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-nonredundant-coordinate-data.md`
passed.

Nonclaims: finite coordinate algebra only.  No open coordinate domain,
topology, determinant-unit neighborhood, source-rank coverage,
source/image equality, measure pushforward, density/Jacobian theorem, normal
crossings, pole order, or RLCT is proved.

Latest A2 retained-passive determinant-chart domain:
Lean now defines
`ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.detChart` and
`detChartSet` in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`.
The predicate is exactly `IsUnit Ctop.det` plus pointwise
`IsUnit (A1passive p).det` for passive `A1` blocks.

Theorems `edgeMatrix_readbacks_eq_targets_of_detChart` and
`edgeMatrix_ext_of_detChart` repackage the finite readback and extensionality
theorems on this domain.  The theorem `injOn_edgeMatrix_detChartSet` proves
source-map injectivity on the determinant-domain set.

Lean also adds `RetainedPassiveCoordinatesTopology.lean`, with a product
topology on the nonredundant coordinate fields and the openness theorem
`isOpen_detChartSet`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-det-chart-domain.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-det-chart-domain.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-det-chart-domain.md`
passed.

Nonclaims: no image openness, continuity of `edgeMatrix`, source-rank
coverage, source/image equality, measure pushforward, density/Jacobian
theorem, normal crossings, pole order, or RLCT is proved.

Latest A2 retained-passive projection continuity:
Lean now proves the elementary continuity of all stored nonredundant coordinate
field projections and of the dummy-slot component maps `A1seed`, `F2full`, and
`A3seed` in `RetainedPassiveCoordinatesTopology.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-projection-continuity.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-projection-continuity.md`.

Nonclaims: projection-continuity setup only.  No continuity of `solvedA1`,
`solvedA3`, `toCoordinateData`, or `edgeMatrix`; no image openness,
source-rank coverage, source/image equality, measure pushforward,
density/Jacobian theorem, normal crossings, pole order, or RLCT is proved.

Latest A2 retained-passive solved-A1 continuity:
Lean now proves continuity of the passive top-left tail product and
componentwise continuity of the solved full `A1` family on the nonredundant
determinant-chart subtype in `RetainedPassiveCoordinatesTopology.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-solved-a1-continuity.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-solved-a1-continuity.md`.

Nonclaims: no continuity of `solvedA3`, `toCoordinateData`, or `edgeMatrix`;
no image openness, source-rank coverage, source/image equality, measure
pushforward, density/Jacobian theorem, normal crossings, pole order, or RLCT
is proved.

Latest A2 retained-passive solved-A3 continuity:
Lean now proves componentwise continuity of the solved full `A3` family on the
nonredundant determinant-chart subtype, together with the finite residual
product, solved-`A1` product, determinant-unit, and lower-left tail-sum
continuity lemmas needed for the final component.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-solved-a3-continuity.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-solved-a3-continuity.md`.

Nonclaims: endpoint-family continuity only.  No continuity of `edgeMatrix`;
no image openness, source-rank coverage, source/image equality, measure
pushforward, density/Jacobian theorem, normal crossings, pole order, or RLCT
is proved.

Latest A2 retained-passive edge-matrix continuity:
Lean now proves
`RetainedPassiveNonredundantCoordinateData.continuous_edgeMatrix_detChart_subtype_apply`
and
`RetainedPassiveNonredundantCoordinateData.continuous_edgeMatrix_detChart_subtype`
in `RetainedPassiveCoordinatesTopology.lean`.

The per-edge theorem proves continuity of `data.1.edgeMatrix p` on
`{data // data.detChart}` by unfolding the fixed-base retained-passive source
edge and composing the solved-`A1`, solved-`A3`, `F2full`, and `C` continuity
lemmas through block-matrix operations.  The family theorem is the Pi-topology
wrapper.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-edge-matrix-continuity.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-edge-matrix-continuity.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-edge-matrix-continuity.md`
passed.

Nonclaims: source-map continuity on the determinant-chart subtype only.  No
image openness, local homeomorphism, source-rank coverage, source/image
equality, measure pushforward, density/Jacobian theorem, normal crossings,
pole order, or RLCT is proved.

Latest A2 retained-passive source-readback object:
Lean now defines
`RetainedPassiveNonredundantCoordinateData.sourceReadbackSuffixState`,
`sourceReadbackTransformedEdge`, and `sourceReadback`, plus the fieldwise
helper `ext_fields`, in `RetainedPassiveCoordinates.lean`.

The readback object assigns to an arbitrary retained-passive-shaped edge
family the nonredundant coordinate fields read from deterministic suffix states
and transformed edges.  Lean proves
`sourceReadback_edgeMatrix_eq`: for any `data` with `data.detChart`,
`sourceReadback data.edgeMatrix = data`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-source-readback-object.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-source-readback-object.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-source-readback-object.md`
passed.

Nonclaims: total finite readback and inverse-on-image only.  No arbitrary
edge-family image membership, image openness, local homeomorphism,
source-rank coverage, source/image equality, measure pushforward,
density/Jacobian theorem, normal crossings, pole order, or RLCT is proved.

Latest A2 retained-passive source-readback continuity:
Lean now defines
`RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart`, requiring
the transformed edge at every deterministic readback suffix-state step to lie
in `identityCornerDetChart`.

Lean proves `continuousAt_sourceReadbackSuffixState_fields`,
`continuousAt_sourceReadbackTransformedEdge`,
`continuousAt_sourceReadback`, and
`continuous_sourceReadback_sourceRecursiveDetChart_subtype` in
`RetainedPassiveCoordinatesTopology.lean`.  The primary theorem is
`ContinuousAt (fun x => sourceReadback (E x)) x0` from `ContinuousAt E x0`
and the recursive determinant predicate at `E x0`; the subtype theorem is
only the pointwise corollary.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-source-readback-continuity.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-source-readback-continuity.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-source-readback-continuity.md`
passed.

Nonclaims: finite source-readback continuity only.  No arbitrary edge-family
image membership, image openness, local homeomorphism, source-rank coverage,
source/image equality, measure pushforward, density/Jacobian theorem, normal
crossings, pole order, or RLCT is proved.

Latest A2 retained-passive source-recursive reconstruction spine:
Lean now proves the first right-inverse algebra for arbitrary edge families
satisfying `sourceRecursiveDetChart`.  The source suffix `Ctop` determinants
are units at every visited suffix state, so `sourceReadback E` satisfies the
retained-passive `detChart`.  The full source-readback right field satisfies
`F2full i = -S_i.B`, and the solved full `A1` family equals
`topLeftCorner (sourceReadbackTransformedEdge E p)` for every edge.

The generic Schur reassembly lemma
`DLNFibre.DLN.Aoyagi.fromBlocks_schurReadbacks_eq` has been placed in
`ProductReduction.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-source-recursive-reconstruction-spine.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-source-recursive-reconstruction-spine.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-source-recursive-reconstruction-spine.md`
passed after API cleanup.

Nonclaims: no solved-`A3` endpoint reconstruction and no full
`edgeMatrix (sourceReadback E) = E` theorem yet.  No image openness, local
homeomorphism, source-rank coverage, source/image equality, measure
pushforward, density/Jacobian theorem, normal crossings, pole order, or RLCT
is proved.

Latest A2 retained-passive source right inverse:
Lean now proves the finite right-inverse theorem
`RetainedPassiveNonredundantCoordinateData.edgeMatrix_sourceReadback_eq_of_sourceRecursiveDetChart`
in `RetainedPassiveCoordinates.lean`.

The supporting new algebra proves the lower-left suffix recurrence, source
`D` and solved-`A1` product readbacks, actual lower-left tail-sum readback,
solved-`A3` recovery from transformed source lower-left blocks, transformed
edge reassembly from Schur readbacks, and final upper-unitriangular
cancellation.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-source-right-inverse.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-source-right-inverse.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-source-right-inverse.md`
passed with API cleanup.

Nonclaims: image membership is proved only for the explicit
`sourceRecursiveDetChart` domain.  No openness, local homeomorphism,
source-rank coverage, equality with the whole source image, measure
pushforward, density/Jacobian theorem, normal crossings, pole order, or RLCT
is proved.

Latest A2 retained-passive source-recursive chart homeomorphism:
Lean now proves
`RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart_edgeMatrix_of_detChart`,
`continuous_edgeMatrix_sourceRecursiveDetChart_subtype`,
`continuous_sourceReadback_detChart_subtype`, and
`detChart_sourceRecursiveDetChart_homeomorph`.

The forward map is `data.edgeMatrix` from `{data // data.detChart}` to the
explicit source-recursive determinant chart.  The inverse map is
`sourceReadback E`.  The inverse laws are the previously proved finite
left/right inverse theorems.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-source-recursive-chart-homeomorph.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-source-recursive-chart-homeomorph.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-source-recursive-chart-homeomorph.md`
passed.

Nonclaims: this is a homeomorphism of named subtypes only.  No ambient
openness of the source-recursive chart, equality with the whole source image,
source-rank coverage, measure pushforward, density/Jacobian theorem, normal
crossings, pole order, or RLCT is proved.

Latest A2 retained-passive source-recursive chart openness:
Lean now defines
`RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChartSet` and
proves `sourceRecursiveDetChartSet_mem_nhds` and
`isOpen_sourceRecursiveDetChartSet`.

The proof uses `sourceRecursiveDetChart_iff` to remove the irrelevant suffix
proof argument, continuity of `sourceReadbackTransformedEdge` at points of the
chart, openness of the selected determinant chart, and finite intersection of
edge-wise neighborhoods.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-source-recursive-chart-openness.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-source-recursive-chart-openness.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-source-recursive-chart-openness.md`
passed.

Nonclaims: no equality with the whole source image, source-rank coverage,
measure pushforward, density/Jacobian theorem, normal crossings, pole order,
or RLCT is proved.

Latest A2 retained-passive open partial homeomorphism:
Lean now defines
`RetainedPassiveNonredundantCoordinateData.detChartSet_sourceRecursiveDetChartSet_homeomorph`
and
`RetainedPassiveNonredundantCoordinateData.detChart_sourceRecursiveDetChart_openPartialHomeomorph`
in `RetainedPassiveCoordinatesTopology.lean`.

The open partial homeomorphism has source `detChartSet`, target
`sourceRecursiveDetChartSet`, forward map `edgeMatrix`, and inverse map
`sourceReadback`.  Its map-source, map-target, and inverse-law fields are the
existing finite retained-passive chart theorems, while its source and target
are the already proved open sets.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-open-partial-homeomorph.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-open-partial-homeomorph.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-open-partial-homeomorph.md`
passed by xhigh `Helmholtz the 3rd`.

Nonclaims: this is a local chart object for the explicit retained-passive
chart only.  No equality with the whole source image, source-rank coverage,
measure pushforward, density/Jacobian theorem, normal crossings, pole order,
or RLCT is proved.

Latest A2 retained-passive source-readback residual readout:
Lean now proves
`paperEndpointFixedBaseResidualBlockCoordinateMap_eq_sourceReadback_residualFactorProduct`
in `RetainedPassiveLocalSource.lean`.

Status: Proved.

Claim: for a fixed-base retained-passive-shaped edge family `E`, the p.13
residual block coordinate map is the scalar-entry map of
`residualFactorProduct (sourceReadback E).C (Fin.last (M + 1)) 0`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-source-readback-residual-readout.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-source-readback-residual-readout.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-source-readback-residual-readout.md`
passed by xhigh `Descartes the 3rd`.

Kill condition: using this as a selected-entry residual readout still requires
an entrywise identification of the retained-passive residual-factor product
with selected-entry chart coordinates.  The theorem does not provide that
identification.

Nonclaims: no selected-entry source chart, source image equality,
pushforward/Jacobian theorem, original-loss comparison, normal crossings, pole
order, or RLCT is proved.

Latest A2 retained-passive selected-entry source-readback residual-factor
handoff:
Lean now proves the algebraic readout theorem
`aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_sourceReadback_residualFactorProduct_eq_matrix`
and the local-measure consumer
`exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceReadback_residualFactorProduct_eq_matrix`
in `RetainedPassiveLocalMeasure.lean`.

Status: Proved.

Claim: the raw selected-entry residual square-sum hypothesis in the retained-
passive selected-entry handoff can be replaced by a retained-passive
source-readback residual-factor product matrix identity plus a residual-
coordinate equivalence to the selected center.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-selected-entry-source-readback-residual-factor-handoff.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-selected-entry-source-readback-residual-factor-handoff.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-selected-entry-source-readback-residual-factor-handoff.md`
passed by xhigh `Newton the 3rd`.

Kill condition: the supplied matrix identity must target
`SelectedEntrySignedBox.CenterCoord.chartMap pivot y`, not raw `y`.  It must
also use an equivalence covering the whole endpoint residual coordinate index.

Nonclaims: no proof of that matrix identity from a concrete Case 2 source
construction, no source chart construction, no source image equality, no
pushforward/Jacobian theorem, no original-loss comparison, no normal crossings,
pole order, or RLCT is proved.

Latest A2 retained-passive coordinate-data edge-matrix residual-factor bridge:
Lean now proves
`sourceReadback_paperEndpointFixedBaseEdgeMatrix_eq_retainedPassiveData_of_edgeMatrix_eq`
in `RetainedPassiveLocalSource.lean`, plus
`sourceReadback_residualFactorProduct_eq_matrix_of_retainedPassiveCoordinateData_edgeMatrix`
and
`aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_retainedPassiveCoordinateData_edgeMatrix`
in `RetainedPassiveLocalMeasure.lean`.

Status: Proved.

Claim: if fixed-base p.13 edge matrices along a source chart are realized as
the `edgeMatrix` of retained-passive coordinate data in the determinant chart,
then source readback recovers that data.  Consequently the selected-entry
source-readback residual-factor matrix identity can be reduced to the
data-level identity for `(retainedData y).C`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-coordinate-data-edge-matrix-residual-factor-bridge.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-coordinate-data-edge-matrix-residual-factor-bridge.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-coordinate-data-edge-matrix-residual-factor-bridge.md`
passed by xhigh `Curie the 3rd`.

Kill condition: the edge realization must be the exact fixed-base edge matrix
family used in the residual-coordinate readout, and each retained datum must
satisfy `detChart`.

Nonclaims: no construction of `retainedData`, no Case 2 entrywise product
identity, no source chart construction, no source image equality, no
pushforward/Jacobian theorem, no original-loss comparison, no normal crossings,
pole order, or RLCT is proved.

Latest A2 retained-passive Case 2 selected-entry bridge:
Lean now proves
`residualFactorProduct_retainedPassiveCoordinateData_eq_selectedEntryCenter_matrix_of_case2PostPivot_entrywise`
and
`residualFactorProduct_retainedPassiveCoordinateData_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2PostPivot_entrywise`
in `RetainedPassiveCase2SelectedEntryChartBridge.lean`.

Status: Proved.

Claim: for a two-edge retained-passive coordinate datum, the selected-entry
residual-factor matrix identity follows from the finite Case 2 product bridge
once `data.C 1` is identified with the post-pivot residual block, `data.C 0`
is identified with the free following factor, and the displayed post-pivot
product is supplied entrywise as selected-center coordinates.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-case2-selected-entry-bridge.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-case2-selected-entry-bridge.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-case2-selected-entry-bridge.md`
passed by xhigh `Darwin the 3rd`.

Kill condition: the theorem is only two-edge (`Fin 3` endpoints).  A longer
retained-passive suffix still needs an explicit slicing or transport theorem.
The successor theorem targets the `(S,J+1)` residual center and pivot
`(J+2,J+2)`.

Nonclaims: no retained-passive coordinate datum is constructed, no entrywise
product readout is proved from source construction, no longer suffix is
transported to the two-edge chain, and no source chart/source image,
pushforward/Jacobian, original-loss comparison, normal crossings, pole order,
or RLCT is proved.

Latest A2 retained-passive Case 2 synthetic two-edge data:
Lean now defines `case2PostPivotRetainedPassiveData` and proves
`case2PostPivotRetainedPassiveData_detChart` and
`case2PostPivotRetainedPassiveData_hdataFactor_of_entrywise` in
`RetainedPassiveCase2SelectedEntryChartBridge.lean`.

The same final identity is also exposed under the content-named alias
`case2PostPivotRetainedPassiveData_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_entrywise`.

Status: Proved; reviewed.

Claim: the concrete post-pivot Case 2 two-edge factor family can be packaged
as a retained-passive nonredundant coordinate datum with identity determinant
fields, and the existing concrete Case 2 selected-entry product bridge gives
the retained-passive data-level `hdataFactor` identity for that synthetic
datum under the explicit entrywise successor-source readout.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-case2-synthetic-data.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-case2-synthetic-data.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-case2-synthetic-data.md`
passed by xhigh `Ampere the 3rd`.

Kill condition: the datum is synthetic and two-edge.  It may not be used as
the retained data of a source chart or as a slice of a longer retained-passive
suffix unless separate edge-realization or suffix-transport hypotheses are
proved.

Nonclaims: no source chart, fixed-base edge realization, longer-suffix
transport, entrywise product readout, pushforward/Jacobian theorem,
original-loss comparison, normal crossings, pole order, or RLCT is proved.

Latest A2 retained-passive fixed-base edge realisation:
Lean now proves
`paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOf_retainedPassiveEdgeMatrix`
and
`sourceReadback_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOf_retainedPassiveEdgeMatrix_eq`
in `RetainedPassiveLocalSource.lean`.

Status: Proved; reviewed.

Claim: if a fixed-base continuous reverse-edge family is constructed from a
retained-passive datum's own `edgeMatrix`, then fixed-base edge-matrix
extraction recovers `data.edgeMatrix`; if additionally `data.detChart`, then
source readback recovers `data`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-fixed-base-edge-realisation.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-fixed-base-edge-realisation.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-fixed-base-edge-realisation.md`
passed by xhigh `Pasteur the 4th`.

Kill condition: the theorem applies only when the edge family is the
prescribed fixed-base realization of `data.edgeMatrix`.  It may not be used as
Case 2 source production, as an endpoint-index alignment theorem, or as a
longer retained-passive suffix transport theorem.

Nonclaims: no retained-passive datum is constructed, no Case 2 successor
entrywise readout is proved, no source chart/source image equality,
pushforward/Jacobian theorem, original-loss comparison, normal crossings, pole
order, or RLCT is proved.

Latest A2 retained-passive Case 2 pivot-nonzero source readout:
Lean now proves a fixed-pivot selected-entry inverse and uses it to derive the
Case 2 successor-source entrywise readout from a supplied nonzero value of the
displayed post-pivot product at the fixed successor pivot `(J+2,J+2)`.

Status: Proved; reviewed.

Claim: given `eNext : tau ~= Case2ResidualColIndex n S (J+1)` and nonzero
value of `case2DisplayedPostPivotFreeTwoEdgeFactorProduct` at the reindexed
successor pivot `(J+2,J+2)`, there exists `yNext` such that the displayed
post-pivot product is the successor selected-entry source chart map.  Hence
the synthetic retained-passive two-edge datum satisfies the corresponding
successor selected-entry residual-factor matrix identity.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-case2-pivot-nonzero-source-readout.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-case2-pivot-nonzero-source-readout.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-case2-pivot-nonzero-source-readout.md`
passed by xhigh `Schrodinger the 4th` after documentation edits.

Kill condition: the theorem still requires the fixed successor pivot nonzero
condition and the endpoint equivalence.  It may not be used as proof that the
successor pivot is nonzero, as source chart production, or as longer-suffix
transport.

Nonclaims: no retained-passive source data is produced, no fixed-base endpoint
alignment or longer suffix transport is proved, and no source image,
pushforward/Jacobian, original-loss comparison, normal crossings, pole order,
or RLCT is proved.

Latest A2 adjacent two-edge residual-factor transport:
Lean now proves generic finite product lemmas for
`ChartLocalSuffixState.residualFactorProduct`: one-edge products reduce to the
visited factor, adjacent two-edge products reduce to the ordered product of
the two visited factors, and reindexed adjacent two-edge products reduce to
the product of the two reindexed factors.

Status: Proved; reviewed.

Claim: for a supplied residual-factor family `C`, an adjacent window
`p.castSucc.castSucc <= p.succ.succ` has product
`C p.succ * C p.castSucc` in the correct right-to-left order. After endpoint
equivalences at the right, middle, and left endpoints, the corresponding
submatrix is the product of the reindexed factors.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-adjacent-two-edge-residual-factor-transport.md`
and
`threads/03-block-product-reduction/statement-card-a2-adjacent-two-edge-residual-factor-transport.md`.
Review:
`threads/03-block-product-reduction/review-a2-adjacent-two-edge-residual-factor-transport.md`
passed by xhigh `Zeno the 4th`.

Kill condition: this theorem applies only to the explicit supplied factor
product over an adjacent window. It may not be used to identify a full
retained-passive endpoint product with that window unless outside factors or
full-to-window transport are separately supplied.

Nonclaims: no fixed-base endpoint alignment, Case 2 factor identity,
successor selected-entry readout, pivot nonzero provenance, source chart,
source image, pushforward/Jacobian theorem, original-loss comparison, normal
crossings, pole order, or RLCT is proved.

Latest A2 adjacent-window Case 2 selected-entry consumer:
Lean now composes the generic adjacent-window residual-factor transport with
the displayed Case 2 post-pivot product and selected-entry readout APIs.

Status: Proved; reviewed.

Claim: for a supplied longer residual-factor family `C` and adjacent index
`p`, if endpoint equivalences identify the row, middle, and column endpoints
with the Case 2 post-pivot row, residual-column, and free-column domains, and
if the two adjacent factors reindex to the displayed post-pivot residual block
and following factor, then the adjacent product is the displayed Case 2 lower
product.  With either entrywise readout or supplied fixed successor pivot
nonzero, Lean upgrades the adjacent product to the successor selected-entry
center-coordinate matrix.  The retained-passive wrapper applies this to
`data.C`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-adjacent-window-case2-selected-entry-consumer.md`
and
`threads/03-block-product-reduction/statement-card-a2-adjacent-window-case2-selected-entry-consumer.md`.
Review:
`threads/03-block-product-reduction/review-a2-adjacent-window-case2-selected-entry-consumer.md`
passed by xhigh `Herschel the 4th`.

Kill condition: this is conditional adjacent-window algebra.  It may not be
used as fixed-base endpoint alignment, as full-suffix collapse, as proof of
the factor identities for a source-readback family, or as proof of the fixed
successor pivot nonzero condition.

Nonclaims: no endpoint equivalence, full retained-passive suffix transport,
fixed-base source production, pivot nonzero provenance, source image,
pushforward/Jacobian theorem, original-loss comparison, normal crossings,
pole order, or RLCT is proved.

Latest A2 source-readback per-factor residual block:
Lean now exposes the definitional field identity
`sourceReadback_C_eq_schurResidualBlock_sourceReadbackTransformedEdge` in
`RetainedPassiveCoordinates.lean`.

Status: Proved; reviewed.

Claim: for any retained-passive-shaped source edge family `E` and edge index
`p`, `(sourceReadback E).C p` equals the Schur residual block of
`sourceReadbackTransformedEdge E p`.  The proof is `rfl` and needs no
determinant-chart hypothesis.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-source-readback-per-factor-residual-block.md`
and
`threads/03-block-product-reduction/statement-card-a2-source-readback-per-factor-residual-block.md`.
Review:
`threads/03-block-product-reduction/review-a2-source-readback-per-factor-residual-block.md`
passed by xhigh `Pascal the 4th`.

Kill condition: this is only a named per-factor readback identity.  It may
not be used as a displayed Case 2 factor identity, endpoint equivalence,
full-suffix collapse, fixed pivot nonzero proof, or analytic source
production.

Nonclaims: no source chart, source image, pushforward/Jacobian theorem,
original-loss comparison, normal crossings, pole order, or RLCT is proved.

Latest A2 retained-passive source-map factor readout:
Lean now proves a concrete source-map factor identity for retained-passive
data and two synthetic Case 2 specializations.

Status: Proved; reviewed.

Claim: if `data.detChart`, then
`schurResidualBlock (sourceReadbackTransformedEdge data.edgeMatrix p) =
data.C p`.  For `case2PostPivotRetainedPassiveData`, edge `1` reads out
`case2DisplayedPostPivotResidualBlock`, and edge `0` reads out
`case2DisplayedPostPivotFreeFollowingFactor`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-source-map-factor-readout.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-source-map-factor-readout.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-source-map-factor-readout.md`
passed by xhigh `Confucius the 4th`.

Kill condition: the Case 2 specializations are synthetic two-edge source-map
facts.  They may not be used as real fixed-base endpoint equivalences, source
chart production, full endpoint product collapse, selected-entry entrywise
readout, or fixed pivot nonzero provenance.

Nonclaims: no source image, pushforward/Jacobian theorem, original-loss
comparison, normal crossings, pole order, or RLCT is proved.

Latest A2 retained-passive raw-order Jacobian density interface:
Lean now defines `topologyTupleEdgeRawOrderFDerivAbsDet` in
`RetainedPassiveCoordinatesDerivative.lean` and proves
`topologyTupleEdgeRawOrderFDerivAbsDet_pos_of_mem_topologyTupleDetChartSet`,
`eventually_topologyTupleEdgeRawOrderFDerivAbsDet_pos_nhds`,
`exists_pos_eventually_le_topologyTupleEdgeRawOrderFDerivAbsDet_nhds_of_continuousAt`,
and
`exists_pos_eventually_topologyTupleEdgeRawOrderFDerivAbsDet_le_nhds_of_continuousAt`.

Status: Proved; reviewed.

Claim: the forward absolute determinant of
`fderiv ℝ topologyTupleEdgeRawOrder z` is strictly positive at
retained-passive tuple determinant-chart points, and eventually positive near
such points.  If continuity of this absolute determinant function is supplied
at a base point, it has positive local lower and upper bounds there.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-raw-order-jacobian-density-interface.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-raw-order-jacobian-density-interface.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-raw-order-jacobian-density-interface.md`
accepted by xhigh `Laplace the 4th`.

Kill condition: local quantitative lower bounds depend on the explicit
`ContinuousAt` hypothesis; do not infer them from pointwise determinant
unitness alone.

Nonclaims: no continuity of the retained-passive derivative family, no closed
determinant formula, no inverse-density formula, no measure pushforward, no
source-density identity, no normal crossings, no pole order, and no RLCT is
proved.

Latest A2 retained-passive raw-order C1 and density continuity:
Lean now proves a forward `C^1` chain for `topologyTupleEdgeRawOrder` and
uses it to discharge continuity of the Frechet derivative and of
`topologyTupleEdgeRawOrderFDerivAbsDet`.  It also adds no-extra-hypothesis
local positive lower/upper bounds for the forward absolute determinant density
at tuple determinant-chart points.

Status: Proved; reviewed.

Lean names include
`contDiffAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet`,
`continuousAt_fderiv_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet`,
`continuousAt_fderiv_topologyTupleEdgeRawOrder_apply_of_mem_topologyTupleDetChartSet`,
`continuousAt_topologyTupleEdgeRawOrderFDerivAbsDet_of_mem_topologyTupleDetChartSet`,
`exists_pos_eventually_le_topologyTupleEdgeRawOrderFDerivAbsDet_nhds`, and
`exists_pos_eventually_topologyTupleEdgeRawOrderFDerivAbsDet_le_nhds`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-raw-order-c1-density-continuity.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-raw-order-c1-density-continuity.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-raw-order-c1-density-continuity.md`
accepted by xhigh `Wegener the 4th`.

Kill condition: this proves continuity and local bounds for the already-defined
forward absolute determinant density only.  It must not be read as a closed
determinant formula, inverse-density measurability theorem, or source-prior
transport theorem.

Nonclaims: no explicit determinant formula, inverse-density measurability,
original source-prior transport, selected-entry target-image equality,
source-rank coverage, normal crossings, pole order, or RLCT is proved.

Latest A2 retained-passive raw-order weighted change of variables:
Lean now adds `RetainedPassiveCoordinatesMeasure.lean` and imports it from
`DLNFibre.lean`.  It proves
`nullMeasurableSet_topologyTupleDetChartSet`,
`map_topologyTupleEdgeRawOrder_restrict_detChart_withDensity_abs_det`,
`map_topologyTupleEdgeRawOrder_withDensity_absDet_eq_restrict_rawSourceChart`,
and the corresponding apostrophe convenience wrappers discharging the
null-measurability hypothesis from the Borel/open-chart fact.

Status: Proved; reviewed.

Claim: for any additive Haar measure on the retained-passive raw tuple space,
the raw-order chart map pushes the source measure restricted to the tuple
determinant chart and weighted by
`ENNReal.ofReal (topologyTupleEdgeRawOrderFDerivAbsDet z)` to the additive
Haar measure restricted to the image, equivalently to the raw-order
source-recursive determinant chart.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-raw-order-weighted-cov.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-raw-order-weighted-cov.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-raw-order-weighted-cov.md`
accepted by xhigh `Aristotle the 4th`.

Kill condition: this is only a forward weighted Jacobian change-of-variables
identity.  It may not be used as an unweighted pushforward, inverse-density
formula, source-prior density identity, or original DLN source-measure theorem
without additional hypotheses/proofs.

Nonclaims: no explicit determinant formula, no determinant-density continuity,
no local bounded-density estimate, no inverse Jacobian density, no original DLN
source pushforward, no normal crossings, no pole order, and no RLCT is proved.

Latest A2 retained-passive inverse Jacobian density:
Lean now defines `topologyTupleEdgeRawOrderInverseJacobianDensity` in
`RetainedPassiveCoordinatesMeasure.lean` and proves
`topologyTupleEdgeRawOrderInverseJacobianDensity_apply_chartMap`,
`topologyTupleEdgeRawOrderFDerivAbsDet_mul_inverseJacobianDensity_apply_chartMap`,
`topologyTupleEdgeRawOrderInverseJacobianDensity_pos_of_mem_rawSourceChart`,
and
`map_topologyTupleEdgeRawOrder_restrict_detChart_eq_withDensity_inverseJacobian_of_aemeasurable`.

Status: Proved; reviewed.

Claim: the chart-side inverse density is the reciprocal of the forward
absolute determinant after raw-order source readback.  On the determinant
chart it cancels the forward density pointwise.  Under explicit
a.e.-measurability hypotheses for the forward density, inverse density, and
composed inverse density, the unweighted restricted source Haar measure pushes
forward to the raw-order target-chart Haar measure weighted by this inverse
density.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-inverse-jacobian-density.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-inverse-jacobian-density.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-inverse-jacobian-density.md`
accepted by xhigh `Raman the 4th` after a docstring repair.

Kill condition: the inverse-density pushforward theorem is conditional; do not
use it as an unconditional measure transport theorem unless the required
a.e.-measurability hypotheses are separately proved or supplied.

Nonclaims: no explicit determinant formula, no determinant-density continuity
or measurability, no source-prior density identity, no original DLN source
pushforward, no normal crossings, no pole order, and no RLCT is proved.

Latest A2 retained-passive composed weighted COV:
Lean now proves
`map_comp_topologyTupleEdgeRawOrder_withDensity_absDet_eq_map_restrict_rawSourceChart`,
`map_topologyTupleEdgeMatrix_withDensity_absDet_eq_map_edgeFamilyOfRawOrderTuple`,
`map_comp_topologyTupleEdgeRawOrder_restrict_detChart_eq_map_invJac_of_aemeasurable`,
and
`map_topologyTupleEdgeMatrix_restrict_detChart_eq_map_edgeFamily_invJac_of_aemeasurable`
in `RetainedPassiveCoordinatesMeasure.lean`.

Status: Proved; reviewed.

Claim: the retained-passive raw-order COV theorems can be composed with
downstream a.e.-measurable maps, and in particular with the raw-order
edge-family decoder, producing chart-coordinate edge-family measure identities.
The inverse-density versions retain all explicit determinant-density
measurability hypotheses.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-composed-weighted-cov.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-composed-weighted-cov.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-composed-weighted-cov.md`
accepted by xhigh `Harvey the 4th`.

Kill condition: these theorems are only measure-map composition.  Do not use
them as local-source coverage, original source-prior transport, or unconditional
inverse-density transport.

Nonclaims: no determinant formula, no determinant-density continuity or
measurability, no source-prior density theorem, no original DLN source
pushforward, no local-source coverage, no normal crossings, no pole order, and
no RLCT is proved.

Latest A2 retained-passive raw-order local-source COV bridge:
Lean now proves
`paperEndpointFixedBaseRetainedPassiveP13LocalSource_mem_of_edgeFamilyOfRawOrderTuple_realization`
in `RetainedPassiveLocalSource.lean` and
`measure_map_restrict_retainedPassiveP13LocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_absDet_of_realization`
in `RetainedPassiveLocalMeasure.lean`.

Status: Proved; reviewed.

Claim: if a supplied realization map `sourceChart` sends every raw-order target
point `y in T` to retained-passive parameters whose fixed-base edge matrices
are `edgeFamilyOfRawOrderTuple y`, then the chart-produced measure
`mu = Measure.map sourceChart (m.restrict T)` restricts to the retained-passive
p.13 local source as the weighted raw-order source-side map
`sourceChart o topologyTupleEdgeRawOrder`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-raw-order-local-source-cov-bridge.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-raw-order-local-source-cov-bridge.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-raw-order-local-source-cov-bridge.md`
accepted by xhigh `Parfit the 4th`.

Kill condition: this theorem starts from the raw-target pushforward through a
supplied realization map.  Do not use it as construction or transport of the
original DLN source prior.

Nonclaims: no determinant-density continuity, inverse-density measurability,
original source-prior transport, selected-entry target-image equality,
source-rank coverage, normal crossings, pole order, or RLCT is proved.

Latest A2 retained-passive unconditional inverse-density COV:
Lean now proves
`nullMeasurableSet_topologyTupleRawOrderSourceRecursiveDetChartSet`,
`continuousAt_topologyTupleEdgeRawOrderInverseJacobianDensity_of_mem_rawSourceChart`,
`continuousAt_topologyTupleEdgeRawOrderInverseJacobianDensity_comp_of_mem_rawSourceChart`,
`map_topologyTupleEdgeRawOrder_restrict_detChart_eq_withDensity_inverseJacobian`,
`map_comp_topologyTupleEdgeRawOrder_restrict_detChart_eq_map_invJac`, and
`map_topologyTupleEdgeMatrix_restrict_detChart_eq_map_edgeFamily_invJac` in
`RetainedPassiveCoordinatesMeasure.lean`.

Status: Proved; reviewed.

Claim: the retained-passive raw-order map pushes Haar measure restricted to
the tuple determinant chart to Haar measure restricted to the raw-order target
chart weighted by the target-side inverse Jacobian density.  The explicit
a.e.-measurability hypotheses from the earlier conditional theorem are now
discharged internally from forward density continuity, inverse-chart
continuity, positivity, and chart openness.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-unconditional-inverse-density-cov.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-unconditional-inverse-density-cov.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-unconditional-inverse-density-cov.md`
accepted by xhigh `Heisenberg the 4th`.

Kill condition: this is still chart-coordinate inverse-density transport for
additive Haar measure on tuple coordinates.  Do not use it as an explicit
determinant formula, source-prior density theorem, original DLN source
pushforward, or selected-entry image theorem.

Nonclaims: no explicit determinant formula, original source-prior transport,
selected-entry target-image equality, source-rank coverage, normal crossings,
pole order, or RLCT is proved.

Latest A2 retained-passive canonical local-source COV:
Lean now proves
`measure_map_restrict_retainedPassiveP13CanonicalLocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_absDet`
in `RetainedPassiveLocalMeasure.lean`.

Status: Proved; reviewed.

Claim: the canonical fixed-base source edge-family chart obtained from
`ofTopologyTuple (topologyTupleEdgeRawOrderInverse y)` realizes the raw-order
edge family on `T` and is a.e.-measurable on `m.restrict T`, so the earlier
retained-passive local-source COV theorem applies with `Cedge = id` and no
external realization map.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-canonical-local-source-cov.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-canonical-local-source-cov.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-canonical-local-source-cov.md`
accepted by xhigh `Sartre the 4th`.

Kill condition: this theorem is only for the chart-produced measure
`Measure.map sourceChart (m.restrict T)`.  Do not use it as the original DLN
source prior or as selected-entry/source-rank coverage.

Nonclaims: no selected-entry target-image equality, original source-prior
transport, source-rank coverage, explicit determinant formula, normal
crossings, pole order, or RLCT is proved.

## A2 retained-passive raw-order determinant formula

Status: Reproduced; rectangular determinant API Lean-proved; not yet
Lean-proved as an explicit retained-passive factorization.

Claim: the forward absolute determinant of the retained-passive raw-order map
on the determinant chart should be

```text
|det Tail|^(-|rho|)
* |det LastTop|^(|kappa'_(M+1)|)
* product_{p : Fin (M+1)} |det (A p)|^(|kappa'_p|).
```

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-raw-order-determinant-formula.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-raw-order-determinant-formula.md`.

Checked convention: `LastTop = solvedA1 (Fin.last M)`, so it is the last
passive top block when `M > 0` and `Ctop` when `M = 0`.  This is distinct
from `Tail = retainedPassiveA1TailAfterFirst A`, which is empty/`1` at
`M = 0`.

Lean support now proved:
`linearMap_det_mulLeftLinearMap` and `linearMap_det_mulRightLinearMap` in
`lean/DLNFibre/DLN/Aoyagi/MatrixLinearDeterminant.lean`, and the edge-local
pair determinant `edgeLocalFCPairLinearMap_det_eq`:

```text
det ((F,C) |-> (-(A+H*G)F+HC, -GF+C))
  = det(-A)^(|kappa|)
```

in the displayed `(F,C)` input/output order.

Kill conditions:

- If source review shows Aoyagi p.13 uses a different retained-passive
  coordinate source convention, this is only a local Lean-chart calculation.
- If a Lean derivative factorization cannot triangularize the map with edge
  factors `A p`, the proposed formula must be repaired before formalization.
- Do not consume this as a source-prior transport theorem, selected-entry
  target-image theorem, source-rank coverage theorem, normal-crossing theorem,
  pole-order theorem, or RLCT theorem.

## A2 fixed-passive formal Jacobian determinant

Status: Proved in Lean; reproduced on paper; reviewed.

Claim: the one-step fixed-passive p.13 formal Jacobian has determinant

```text
det(A1)^(|rho|) * det(-A1^{-1})^(|nu|)
```

in raw-to-chart orientation.  Lean proves this as
`productStepFixedPassiveFormalJacobian_det_eq`, after first proving the
factorization
`productStepFixedPassiveFormalJacobian_eq_shear_comp_diagonal` and the
intermediate multiplication-block determinant theorem
`productStepFixedPassiveFormalJacobian_det_eq_multiplication_blocks`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-fixed-passive-formal-jacobian-determinant.md`
and
`threads/03-block-product-reduction/statement-card-a2-fixed-passive-formal-jacobian-determinant.md`.
Review:
`threads/03-block-product-reduction/review-a2-fixed-passive-formal-jacobian-determinant.md`
accepted by xhigh `Arendt the 4th`.

Kill condition: if this theorem is used inside the retained-passive total
determinant calculation, first match orientation and endpoint conventions.
The retained-passive total formula has additional `Tail`, edge-local `A p`,
and `LastTop` factors.

Nonclaims: no analytic `fderiv` theorem, retained-passive total determinant
formula, source-prior transport, normal crossings, pole order, or RLCT is
proved by this slice.

## A2 edge-local `(F,C)` pair determinant

Status: Proved in Lean; reproduced on paper; reviewed.

Claim: for fixed `A : Matrix rho rho K`, `H : Matrix rho mu K`, and
`G : Matrix mu rho K`, the finite linear map

```text
(F, C) |->
  (-(A + H*G) * F + H*C,
   -G*F + C)
```

on `Matrix rho kappa K x Matrix mu kappa K`, in the displayed coordinate
order, has determinant

```text
(-A).det ^ Fintype.card kappa.
```

Lean proves this as `edgeLocalFCPairLinearMap_det_eq`, with the formula lemma
`edgeLocalFCPairLinearMap_apply`, in
`lean/DLNFibre/DLN/Aoyagi/MatrixLinearDeterminant.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-edge-local-fc-pair-determinant.md`
and
`threads/03-block-product-reduction/statement-card-a2-edge-local-fc-pair-determinant.md`.
Review:
`threads/03-block-product-reduction/review-a2-edge-local-fc-pair-determinant.md`
accepted by xhigh `Lagrange the 4th`.

Kill condition: if a later retained-passive assembly changes the input or
output product ordering, account for the resulting product-space permutation
sign before using this determinant factor.

Nonclaims: no full retained-passive determinant formula, analytic `fderiv`
theorem, source-prior transport, density/pushforward theorem, normal
crossings, pole order, or RLCT is proved by this slice.

## A2 retained-passive actual derivative passive A3 identity

Status: Proved in Lean; reproduced on paper; reviewed.

Claim: for a retained-passive tuple `z` in the determinant chart, tangent
vector `v`, and passive index `p : Fin M`, the actual Frechet derivative of
`topologyTupleEdgeRawOrder` leaves the stored passive lower-left coordinate
unchanged:

```text
((fderiv R topologyTupleEdgeRawOrder z) v).A3passive p = v.A3passive p.
```

Lean proves this as `fderiv_topologyTupleEdgeRawOrder_A3passive_apply` and
also proves the matching point-specialized formal raw-order component bridge
`rawEdgeTupleA3_fderiv_topologyTupleEdgeRawOrder_castSucc_eq_formalRawOrderJacobianAt`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-actual-derivative-a3passive-identity.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-actual-derivative-a3passive-identity.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-actual-derivative-a3passive-identity.md`
accepted by xhigh `Mendel the 5th`.

Kill condition: this claim must stay restricted to passive `p : Fin M`, or
equivalently raw edge `p.castSucc`.  The terminal lower-left coordinate
`Fin.last M` is the solved `F3` endpoint and is not covered by this identity.

Nonclaims: no terminal `F3` derivative identity, full equality with
`retainedPassiveFormalRawOrderJacobianAt`, determinant equality,
measure/Jacobian-density theorem, normal crossings, pole order, or RLCT is
proved by this slice.

## A2 retained-passive actual derivative C formal component bridge

Status: Proved in Lean; same reproduction as the C-unshear derivative.

Claim: after the lower-left target shear by the fixed basepoint `F2`
coefficient, the actual Frechet derivative's `C` component agrees with the
`C` component of `retainedPassiveFormalRawOrderJacobianAt`.

Lean proves this as
`C_unshear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`, using
`fderiv_topologyTupleEdgeRawOrder_C_unshear_apply` and the formal raw-order
apply formula.

Kill condition: this theorem is a sheared component bridge only.  It must not
be read as equality of the unsheared actual derivative with the formal map.

Nonclaims: no full analytic derivative factorization, determinant equality,
measure/Jacobian-density theorem, normal crossings, pole order, or RLCT is
proved by this bridge.

## A2 retained-passive actual derivative F2 formal component bridge

Status: Proved in Lean; reproduced on paper; xhigh implementation review
passed.

Claim: after the top-left and successor-`F2` shear corrections, the actual
Frechet derivative's `F2` component agrees with the `F2` component of
`retainedPassiveFormalRawOrderJacobianAt`.

Lean proves the component identity as
`fderiv_topologyTupleEdgeRawOrder_F2_shear_apply` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`, and the
formal component bridge as
`F2_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-actual-derivative-f2-shear-bridge.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-actual-derivative-f2-shear-bridge.md`.

Review:
`threads/03-block-product-reduction/review-a2-retained-passive-actual-derivative-f2-shear-bridge.md`.

Kill condition: the correction term
`- d(coord.F2 p.succ)(v) * coord.C p` is essential.  Dropping it leaves an
uncancelled successor-`F2` variation.  The theorem must keep the full
`F2full` endpoint convention or explicitly split terminal/nonterminal cases.

Nonclaims: no global determinant-one shear linear equivalence, full analytic
derivative factorization, determinant equality, measure/Jacobian-density
theorem, normal crossings, pole order, or RLCT is proved by this bridge.

## A2 retained-passive F3 positive-tail dEarly consumers

Status: Proved in Lean; controller pen-and-paper reproductions written;
focused and full builds passed; sorry scan, whitespace check, axiom audits,
and independent xhigh implementation reviews passed.

Claim: in the positive-tail retained-passive `F3` bridge whose terminal
`dLast` factor is already target-staged, the first-index zero-current
`dEarly` recurrence can be substituted without expanding the remaining
recursive derivative.  For tail length `M+1`, with

```text
q0 = 0 : Fin (M+1),
p0 = q0.castSucc,
r0 = q0.succ,
qLast = Fin.last M,
```

Lean proves
`F3_tail_pos_dEarly_zero_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`
and the corresponding recovery theorem
`F3_tail_pos_dEarly_zero_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3`.
The expanded `dEarly` leaves `dPsucc`, `dTail`, `dCnext`, and `(fderiv
Nextfun z) v` explicit.  The recovery theorem uses the same staged expression
and right-multiplies by `(-(coord.solvedA1 (Fin.last (M+1))))^-1`.

For tail length `(M+1)+1`, the first recursive `Nextfun` term is then consumed
once more using the successor-index `dEarly` theorem at

```text
s0 = 0 : Fin (M+1),
q1 = s0.succ,
u1 = s0.castSucc,
p1 = q1.castSucc,
r1 = q1.succ.
```

Lean proves
`F3_tail_pos_pos_dEarly_zero_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`
and the recovery theorem
`F3_tail_pos_pos_dEarly_zero_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3`.
The successor tangent is `v.1 u1`, not `v.1 q1`; `dPsucc1`, `Psucc1`, and
the next recursive derivative remain explicit.

For tail length `((M+1)+1)+1`, the remaining `NextNextfun` derivative is
consumed once more using the successor-index `dEarly` theorem at

```text
t0 = 0 : Fin (M+1),
s1 = t0.succ,
q2 = s1.succ,
u2 = s1.castSucc,
p2 = q2.castSucc,
r2 = q2.succ.
```

Lean proves
`F3_tail_pos_pos_pos_dEarly_zero_next_succ_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`
and the recovery theorem
`F3_tail_pos_pos_pos_dEarly_zero_next_succ_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3`.
The second successor tangent is `v.1 u2`, not `v.1 q2`; `dPsucc`,
`dPsucc1`, `dPsucc2`, `Psucc*`, and the next recursive derivative remain
explicit.

Reproduction, statement cards, and reviews:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-f3-positive-tail-dearly-substitution.md`,
`threads/03-block-product-reduction/statement-card-a2-retained-passive-f3-positive-tail-dearly-substitution.md`,
`threads/03-block-product-reduction/review-a2-retained-passive-f3-positive-tail-dearly-substitution.md`,
`threads/03-block-product-reduction/reproduction-a2-retained-passive-f3-two-positive-tail-next-succ-substitution.md`,
`threads/03-block-product-reduction/statement-card-a2-retained-passive-f3-two-positive-tail-next-succ-substitution.md`,
`threads/03-block-product-reduction/review-a2-retained-passive-f3-two-positive-tail-next-succ-substitution.md`,
`threads/03-block-product-reduction/reproduction-a2-retained-passive-f3-three-positive-tail-nextnext-succ-substitution.md`,
`threads/03-block-product-reduction/statement-card-a2-retained-passive-f3-three-positive-tail-nextnext-succ-substitution.md`,
and
`threads/03-block-product-reduction/review-a2-retained-passive-f3-three-positive-tail-nextnext-succ-substitution.md`.

Kill condition: if the two-positive theorem covers the one-positive-tail case,
the three-positive theorem covers shorter tails, either successor step uses
the wrong tangent (`v.1 q1` or `v.1 q2`), rewrites `dPsucc*`, terminal-cleans
`Psucc1`/`Psucc2`, commutes matrix factors, or distributes the outer
`- dEarly * terminalSolvedA1`, it is not the intended slice.

Nonclaims: no full positive-tail `F3` target staging, no closed finite-sum
formula for `dEarly`, no determinant equality, no measure transport, no
normal crossings, no pole order, and no RLCT.

## A2 retained-passive F3 zero-tail target-staged shear

Status: Proved in Lean; controller pen-and-paper reproduction written;
focused and full builds passed; sorry scan, whitespace check, and axiom audit
passed; independent xhigh implementation review passed.

Claim: in the one-edge retained-passive case `M = 0`, the terminal `F3`
component bridge can be rewritten using the target-staged Ctop expression:

```text
Dzv.F3 + coord.F3 * targetCtop = formal.F3,
```

where

```text
targetCtop =
  Dzv.Ctop
    - retainedPassiveTargetRecoveredSuccessorF2At(z,Dzv)(0) * coord.solvedA3(0)
    - coord.F2(0.succ) * rawEdgeTupleA3(Dzv,0).
```

The corresponding recovery theorem is

```text
(Dzv.F3 + coord.F3 * targetCtop) * (-(coord.Ctop))^{-1} = v.F3.
```

Lean proves this as
`F3_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`
and
`F3_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3`
in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-f3-mzero-target-staged-shear.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-f3-mzero-target-staged-shear.md`.

Review:
xhigh `Bernoulli` passed the implementation review, recorded at
`threads/03-block-product-reduction/review-a2-retained-passive-f3-mzero-target-staged-shear.md`.

Kill condition: if the theorem treats terminal `rawEdgeTupleA3` as zero,
uses a source-staged `Ctop` tangent in the advertised expression, uses the
passive `Tail` instead of the right factor `coord.Ctop` in recovery, or
claims anything for `0 < M`, it is not the intended one-edge theorem.

Nonclaims: no positive-tail `F3` target staging, no derivative recurrence for
`Early`, no whole-tuple target-side normalization, no target-side
determinant-one `LinearEquiv`, no determinant equality, no
measure/Jacobian-density theorem, no normal crossings, pole order, or RLCT.

## A2 retained-passive F3 positive-tail dLast target-staged shear

Status: Proved in Lean; controller pen-and-paper reproduction written; focused
and full builds passed; sorry/whitespace/axiom audits passed; independent xhigh
implementation review passed.

Claim: in positive-tail retained-passive `F3` component bridge, for a supplied
terminal passive index `q : Fin M` with `q.succ = Fin.last M`, the terminal
top-factor derivative can be replaced by the target-staged passive `A1`
expression:

```text
dLast_z(v) =
  Dzv.A1passive(q)
    - retainedPassiveTargetRecoveredSuccessorF2At(z,Dzv)(q.succ)
        * coord.solvedA3(q.succ)
    - coord.F2(q.succ.succ) * rawEdgeTupleA3(Dzv,q.succ).
```

Substituting only this factor into the landed `F3` bridge gives

```text
Dzv.F3
  - dEarly_z(v) * coord.solvedA1(Fin.last M)
  + (coord.F3 - Early(z)) * targetLast
= formal.F3.
```

The corresponding recovery right-multiplies by
`(-(coord.solvedA1(Fin.last M)))^{-1}`.

Lean proves this as
`fderiv_retainedPassive_toCoordinateData_solvedA1_succ_apply`,
`F3_tail_pos_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`,
and
`F3_tail_pos_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3`
in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-f3-positive-tail-dlast-target-staged.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-f3-positive-tail-dlast-target-staged.md`.

Review:
xhigh `Raman` passed the implementation review, recorded at
`threads/03-block-product-reduction/review-a2-retained-passive-f3-positive-tail-dlast-target-staged.md`.

Kill condition: if the theorem target-stages or expands `dEarly`, treats
terminal `rawEdgeTupleA3` as zero, uses the first passive tail as `Last`, or
claims full positive-tail `F3` target staging, it is not the intended slice.

Nonclaims: no full positive-tail `F3` target staging, no derivative recurrence
for `Early`, no whole-tuple target-side normalization, no target-side
determinant-one `LinearEquiv`, no determinant equality, no
measure/Jacobian-density theorem, no normal crossings, pole order, or RLCT.

## A2 retained-passive dEarly recursive derivative unfold

Status: Proved in Lean locally; controller pen-and-paper reproduction written;
focused module build and full `DLNFibre` build passed; `scripts/sorries`,
`git diff --check`, and axiom audit passed; xhigh math/Lean/hardener scout
checks and implementation review passed.

Claim: the derivative of the lower-left product-tail sum used as `Early`
unfolds recursively.  For arbitrary `p : Fin (M + 1)`, the Frechet derivative
of

```text
retainedPassiveLowerLeftProductTailSum A_y B_y C_y p.val
```

is the derivative of the current summand

```text
fun y => -(Cprod y * A3p y * (Pcast y)^-1)
```

plus the derivative of the successor tail.  The current summand derivative is
kept explicit.

Lean proves this as
`fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_apply` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-dearly-recursive-unfold.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-dearly-recursive-unfold.md`.

Review:
xhigh `Faraday` passed the implementation review, recorded at
`threads/03-block-product-reduction/review-a2-retained-passive-dearly-recursive-unfold.md`.

Kill condition: if the theorem replaces `retainedPassiveA3WithoutLast` by the
solved terminal lower-left block, commutes matrix factors, or claims source
staging, target staging, determinant equality, measure transport, normal
crossings, pole order, or RLCT, it is not the intended slice.

Nonclaims: no full positive-tail `F3` target staging, no source or target
staging for `dD`, `dG`, or `dP`, no whole-tuple target-side normalization, no
target-side determinant-one `LinearEquiv`, no determinant equality, no
measure/Jacobian-density theorem, no normal crossings, pole order, or RLCT.

## A2 retained-passive dEarly product-rule derivative unfold

Status: Proved in Lean locally; controller pen-and-paper reproduction written;
focused module build and full `DLNFibre` build passed; `scripts/sorries`,
`git diff --check`, and axiom audit passed; xhigh math and Lean-terrain scout
checks passed; implementation review passed.

Claim: the derivative of the current summand in the retained-passive lower-left
tail recurrence expands by the noncommutative product rule and the matrix
inverse derivative.  For arbitrary `p : Fin (M + 1)`, if

```text
E_p = -(D_p * G_p * P_p^-1) + E_next,
```

then

```text
dE_p =
  -dD_p * G_p * P_p^-1
  -D_p * dG_p * P_p^-1
  +D_p * G_p * P_p^-1 * dP_p * P_p^-1
  +dE_next.
```

Lean proves this as
`fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_apply` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-dearly-product-rule-unfold.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-dearly-product-rule-unfold.md`.

Review:
xhigh `Wegener` passed the implementation review, recorded at
`threads/03-block-product-reduction/review-a2-retained-passive-dearly-product-rule-unfold.md`.

Kill condition: if the theorem commutes factors, uses solved terminal `A3`
instead of `retainedPassiveA3WithoutLast`, or claims source staging, target
staging, determinant equality, measure transport, normal crossings, pole
order, or RLCT, it is not the intended slice.

Nonclaims: no source or target staging for `dD`, `dG`, or `dP`, no full
positive-tail `F3` target staging, no whole-tuple target-side normalization,
no target-side determinant-one `LinearEquiv`, no determinant equality, no
measure/Jacobian-density theorem, no normal crossings, pole order, or RLCT.

## A2 retained-passive dEarly product-rule dG substitution

Status: Proved in Lean locally; controller pen-and-paper reproduction written;
focused module build passed; xhigh review passed; `scripts/sorries`,
`git diff --check`, full `DLNFibre` build, and theorem axiom audit passed.

Claim: in the retained-passive `dEarly` product-rule recurrence, at a
nonterminal current edge `p = q.castSucc`, the `A3p` derivative factor is
source-staged:

```text
dA3p_z(v) = v.2.2.1 q.
```

Thus the existing product-rule term

```text
- Cprod(z) * dA3p_z(v) * Pcast(z)^{-1}
```

is rewritten as

```text
- Cprod(z) * v.2.2.1 q * Pcast(z)^{-1}.
```

Lean proves the endpoint helper
`fderiv_retainedPassiveA3WithoutLast_apply` and the product-rule substitution
theorem
`fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dG_castSucc_apply`
in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-dearly-product-rule-dg-substitution.md`
`threads/03-block-product-reduction/statement-card-a2-retained-passive-dearly-product-rule-dg-substitution.md`,
and
`threads/03-block-product-reduction/review-a2-retained-passive-dearly-product-rule-dg-substitution.md`.

Kill condition: if this is read as staging `dCprod` or `dPcast`, if the
matrix factor order is changed, or if it is advertised as target staging,
determinant equality, measure transport, normal crossings, pole order, or
RLCT, it is not the intended slice.

Nonclaims: no `dCprod` staging, no `dPcast` staging, no target staging, no
full positive-tail `F3` target staging, no determinant theorem, no measure
theorem, no normal crossings, pole order, or RLCT.

## A2 retained-passive dEarly terminal dPcast substitution

Status: Proved in Lean locally; controller pen-and-paper reproduction written;
focused module build passed; xhigh review passed; `scripts/sorries`,
`git diff --check`, full `DLNFibre` build, and theorem axiom audit passed.

Claim: in the terminal retained-passive `dEarly` recurrence, after the
terminal `dCprod` and `dG` simplifications, the explicit `dPcast` contribution
is rewritten using the solved-`A1` residual-product product rule.  At
`q = Fin.last M`, with `p = q.castSucc`, the terminal contribution

```text
Cprod(z) * A3p(z) * Pcast(z)^-1 * dPcast_z(v) * Pcast(z)^-1
```

is rewritten as

```text
Cprod(z) * A3p(z) * Pcast(z)^-1
  * (dPsucc_z(v) * solvedA1_z(p)
      + Psucc(z) * d(solvedA1 p)_z(v))
  * Pcast(z)^-1.
```

Lean proves this as
`fderiv_retainedPassiveLowerLeftProductTailSum_last_product_dCprod_dG_dPcast_apply`
in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-dearly-terminal-dpcast-substitution.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-dearly-terminal-dpcast-substitution.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-dearly-terminal-dpcast-substitution.md`.

Kill condition: if the theorem uses `r.succ` rather than `p.succ` for
`Psucc`, changes the noncommutative factor order, moves the rightmost
`Pcast(z)^-1` inside the substituted sum, replaces `d(solvedA1 p)_z(v)` by a
passive source tangent, or advertises determinant equality, measure transport,
normal crossings, pole order, or RLCT, it is not the intended slice.

Nonclaims: no derivative formula for `solvedA1 0`, no source-staging of
`dPcast`, no terminal `Psucc` cleanup, no target staging, no determinant
theorem, no measure theorem, no normal crossings, pole order, or RLCT.

## A2 retained-passive dEarly dPcast substitution

Status: Proved in Lean locally; controller pen-and-paper reproduction written;
focused module build passed; xhigh review passed; `scripts/sorries`,
`git diff --check`, full `DLNFibre` build, and theorem axiom audit passed.

Claim: in the already `dCprod`/`dG`-staged retained-passive `dEarly`
recurrence, the explicit `dPcast` term is rewritten using the solved-`A1`
residual-product product rule.  For `q : Fin M`, define
`p = q.castSucc`.  Then the inverse-derivative contribution

```text
Cprod(z) * A3p(z) * Pcast(z)^-1 * dPcast_z(v) * Pcast(z)^-1
```

is rewritten as

```text
Cprod(z) * A3p(z) * Pcast(z)^-1
  * (dPsucc_z(v) * solvedA1_z(p)
      + Psucc(z) * d(solvedA1 p)_z(v))
  * Pcast(z)^-1.
```

Lean proves this as
`fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_dPcast_castSucc_apply`
in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-dearly-dpcast-substitution.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-dearly-dpcast-substitution.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-dearly-dpcast-substitution.md`.

Kill condition: if the theorem instantiates the solved-`A1` helper at
`q.succ` or uses `r.succ` for `Psucc`, changes the noncommutative factor
order, moves the rightmost `Pcast(z)^-1` inside the substituted sum, replaces
`d(solvedA1 p)_z(v)` by a passive source tangent, or advertises determinant
equality, measure transport, normal crossings, pole order, or RLCT, it is not
the intended slice.

Nonclaims: no derivative formula for `solvedA1 0`, no complete source-staging
of `dPcast`, no iteration of `dPsucc`, no closed finite-sum formula, no target
staging, no determinant theorem, no measure theorem, no normal crossings, pole
order, or RLCT.

## A2 retained-passive dEarly dPcast solvedA1 product rule

Status: Proved in Lean locally; controller pen-and-paper reproduction written;
focused module build passed; xhigh review passed; `scripts/sorries`,
`git diff --check`, full `DLNFibre` build, and theorem axiom audit passed.

Claim: the solved-`A1` residual product that appears as `Pcast` in the
retained-passive `dEarly` recurrence obeys the ordinary noncommutative
product rule.  For `p : Fin (M+1)`, define

```text
Pcast(y) = residualFactorProduct solvedA1_y final p.castSucc,
Psucc(y) = residualFactorProduct solvedA1_y final p.succ.
```

Then at a determinant-chart point `z`,

```text
dPcast_z(v)
  = dPsucc_z(v) * solvedA1_z(p)
    + Psucc(z) * d(solvedA1 p)_z(v).
```

Lean proves this as
`fderiv_retainedPassive_solvedA1_residualFactorProduct_castSucc_apply` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-dearly-dpcast-solveda1-product-rule.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-dearly-dpcast-solveda1-product-rule.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-dearly-dpcast-solveda1-product-rule.md`.

Kill condition: if `(fderiv solvedA1 p)` is replaced by a passive source
tangent for all `p`, if a downstream Jacobian theorem is imported into the
derivative file, if the factor order is changed, or if this is advertised as
complete `dPcast` source staging, determinant equality, measure transport,
normal crossings, pole order, or RLCT, it is not the intended slice.

Nonclaims: no derivative formula for `solvedA1 0`, no complete source-staging
of `dPcast`, no substitution into the `dEarly` recurrence, no closed finite-
sum formula, no target staging, no determinant theorem, no measure theorem, no
normal crossings, pole order, or RLCT.

## A2 retained-passive dEarly terminal dCprod boundary

Status: Proved in Lean locally; controller pen-and-paper reproduction written;
focused module build passed; xhigh review passed; full verification passed:
`scripts/sorries`, `git diff --check`, full `DLNFibre` build, and theorem
axiom audit passed.

Claim: at the terminal boundary of the retained-passive `dEarly` recurrence,
after the `dCprod` and `dG` factors have been source-staged, the empty
successor stored-`C` suffix derivative and the successor zeroed-final tail
derivative vanish.  For `q = Fin.last M : Fin (M+1)`, set
`p = q.castSucc` and `r = q.succ`.  The current Lean theorem gives the terminal
recurrence in the explicit form

```text
dEarly_terminal,z(v)
  = -((0 * C_z r + Cnext(z) * v.2.2.2.1 r)
        * A3p(z) * Pcast(z)^-1)
    - Cprod(z) * dG * Pcast(z)^-1
    + Cprod(z) * A3p(z) * Pcast(z)^-1
        * dPcast_z(v) * Pcast(z)^-1.
```

Lean proves this through
`fderiv_retainedPassive_C_residualFactorProduct_self_apply` and
`fderiv_retainedPassiveLowerLeftProductTailSum_last_product_dCprod_dG_apply`
in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-dearly-terminal-dcprod-boundary.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-dearly-terminal-dcprod-boundary.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-dearly-terminal-dcprod-boundary.md`.

Kill condition: if the source tangent is taken at `q.castSucc` rather than
`r = q.succ`, if `Cnext(z)` is simplified in the theorem without a separate
value-cleanup proof, if the noncommutative order is changed, or if this is
advertised as `dPcast` staging, target staging, determinant equality, measure
transport, normal crossings, pole order, or RLCT, it is not the intended slice.

Nonclaims: no empty-product value simplification of `Cnext(z)`, no one-edge
terminal `Cprod(z)` cleanup, no `dPcast` staging, no closed finite-sum formula
for `dCprod`, no target staging, no full positive-tail `F3` target staging, no
determinant theorem, no measure theorem, no normal crossings, pole order, or
RLCT.

## A2 retained-passive dEarly dCprod source staging

Status: Proved in Lean locally; controller pen-and-paper reproduction written;
focused module build passed; xhigh review passed; full verification passed:
`scripts/sorries`, `git diff --check`, full `DLNFibre` build, and theorem
axiom audit passed.

Claim: in the retained-passive `dEarly` product-rule recurrence, after the
`dG` factor has been source-staged, the stored-`C` suffix product derivative
is source-staged one step.  For `q : Fin M`, set
`p = q.castSucc` and `r = q.succ`; then

```text
dCprod_z(v) = dCnext_z(v) * C_z r + Cnext(z) * v.2.2.2.1 r.
```

Substitution into the current summand gives

```text
-((dCnext_z(v) * C_z r + Cnext(z) * v.2.2.2.1 r)
    * A3p(z) * Pcast(z)^-1).
```

Lean proves this through
`fderiv_retainedPassive_C_apply`,
`fderiv_retainedPassive_C_residualFactorProduct_castSucc_apply`, and
`fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_castSucc_apply`
in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-dearly-dcprod-source-staging.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-dearly-dcprod-source-staging.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-dearly-dcprod-source-staging.md`.

Kill condition: if the source tangent is taken at `q.castSucc` instead of
`q.succ`, if the noncommutative order is changed, or if this is advertised as
`dPcast` staging, target staging, determinant equality, measure transport,
normal crossings, pole order, or RLCT, it is not the intended slice.

Nonclaims: no `dPcast` staging, no closed finite-sum formula for `dCprod`, no
target staging, no full positive-tail `F3` target staging, no determinant
theorem, no measure theorem, no normal crossings, pole order, or RLCT.

## A2 retained-passive dEarly terminal zero tail

Status: Proved in Lean locally; controller pen-and-paper reproduction written;
focused module build passed; xhigh review passed; full verification passed:
`scripts/sorries`, `git diff --check`, full `DLNFibre` build, and theorem
axiom audit passed.

Claim: at the terminal tail index, the retained-passive lower-left product
tail built from the zeroed-final `A3` family is pointwise constant zero:

```text
retainedPassiveLowerLeftProductTailSum
  A1 (retainedPassiveA3WithoutLast A3) C M (Nat.le_succ M) = 0.
```

Therefore the Frechet derivative of the corresponding topology-tuple function
is zero at every basepoint `z` and tangent `v`.

Lean proves this as
`fderiv_retainedPassiveLowerLeftProductTailSum_withoutLast_last_apply` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-dearly-terminal-zero-tail.md`,
`threads/03-block-product-reduction/statement-card-a2-retained-passive-dearly-terminal-zero-tail.md`,
and
`threads/03-block-product-reduction/review-a2-retained-passive-dearly-terminal-zero-tail.md`.

Kill condition: if this theorem is read as a statement about the solved
terminal lower-left `A3` or the terminal `F3` derivative, if it is given
determinant-chart/invertibility hypotheses, or if it is advertised as
`dCprod`/`dPcast` staging, target staging, determinant equality, measure
transport, normal crossings, pole order, or RLCT, it is not the intended
slice.

Nonclaims: no `dCprod` staging, no `dPcast` staging, no target staging, no
full positive-tail `F3` target staging, no determinant theorem, no measure
theorem, no normal crossings, pole order, or RLCT.

## A2 retained-passive dEarly dG source staging

Status: Proved in Lean locally; controller pen-and-paper reproduction written;
focused module build passed; xhigh math and Lean-terrain scout checks passed;
`scripts/sorries`, `git diff --check`, full `DLNFibre` build, and theorem
axiom audit passed.

Claim: the derivative of the zeroed retained-passive lower-left factor

```text
G_p(y) = retainedPassiveA3WithoutLast(data_y.A3seed)(p)
```

is source-staged in the two endpoint cases:

```text
dG_{q.castSucc,z}(v) = v.2.2.1 q,
dG_{Fin.last M,z}(v) = 0.
```

Lean proves this as
`fderiv_retainedPassiveA3WithoutLast_castSucc_apply` and
`fderiv_retainedPassiveA3WithoutLast_last_apply` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`.

Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-dearly-dg-source-staging.md`,
`threads/03-block-product-reduction/statement-card-a2-retained-passive-dearly-dg-source-staging.md`,
and
`threads/03-block-product-reduction/review-a2-retained-passive-dearly-dg-source-staging.md`.

Kill condition: if the terminal zero theorem is read as the solved terminal
`A3`/`F3` derivative, or if this is advertised as target staging, determinant
equality, measure transport, normal crossings, pole order, or RLCT, it is not
the intended slice.

Nonclaims: no target staging, no `dD` or `dP` staging, no full positive-tail
`F3` target staging, no determinant theorem, no measure theorem, no normal
crossings, pole order, or RLCT.

## A2 retained-passive target edge-pair recovery

Status: Proved in Lean; reproduced on paper; focused and full builds passed;
sorry/whitespace/axiom audits passed; xhigh review passed after documentation
status repair.

Claim: define `retainedPassiveTargetRecoveredF2At z w` by backward induction
over retained edges.  At `Fin.last M`, the successor correction is zero.  At
`p.castSucc`, the successor correction is the already recovered target-side
`F2` value at `p.succ`, transported along
`Fin.succ_castSucc p : p.castSucc.succ = p.succ.castSucc`.  On an actual
derivative target `w = (fderiv raw z) v`, this recovered family equals the
source `F2` tangent family `v.F2`.

The induced target-side successor family then replaces the source-staged
successor family in the all-edge normalized pair

```text
U_F(q) = Dzv.F2_q + rawEdgeTupleA1(Dzv)_q * coord.F2 q.castSucc
         - targetXsucc(q) * coord.C q,
U_C(q) = Dzv.C_q  + rawEdgeTupleA3(Dzv)_q * coord.F2 q.castSucc.
```

Lean proves that this target-side pair equals the point-specialized formal
`(F2,C)` output pair, and that the existing formal edge-pair inverse recovers
`(v.F2, v.C)` from it.

Lean proves this in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean` as
`retainedPassiveTargetRecoveredF2At`,
`retainedPassiveTargetRecoveredSuccessorF2At`,
`retainedPassiveTargetRecoveredF2At_fderiv_eq_sourceF2`,
`retainedPassiveTargetRecoveredSuccessorF2At_fderiv_eq_sourceStagedSuccessorF2`,
`retainedPassiveTargetEdgePairShearAt`,
`retainedPassiveTargetEdgePairShearAt_fderiv_eq_formalF2C`, and
`retainedPassiveTargetEdgePairShearAt_fderiv_recovers_sourcePair`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-target-edge-pair-recovery.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-target-edge-pair-recovery.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-target-edge-pair-recovery.md`.

Kill condition: terminal zero is used only at `Fin.last M`; nonterminal edges
must use the recovered successor `F2`, not zero and not a source tangent
directly.  If the dependent cast direction is changed, the successor
correction is not the existing retained-passive successor slot.  If this
theorem is read as a determinant-one target-side `LinearEquiv`, determinant
equality, or whole-tuple target normalization, it overclaims.

Nonclaims: no whole-tuple target-side normalization, no determinant-one
target-side `LinearEquiv`, no actual derivative determinant formula, no
measure theorem, no normal crossings, pole order, or RLCT is proved by this
target edge-pair recovery.

## A2 retained-passive passive A1 target-staged shear

Status: Proved in Lean; reproduced on paper; focused and full builds passed;
sorry/whitespace/axiom audits passed; xhigh review passed.

Claim: for `Dzv = d(topologyTupleEdgeRawOrder)_z(v)` and `q = p.succ`, the
passive top-left correction can be written with the target-recovered successor
`F2` family and the raw lower-left target readout:

```text
Dzv.A1passive_p
  - targetXsuccF2(q) * coord.solvedA3(q)
  - coord.F2(q.succ) * rawEdgeTupleA3(Dzv,q)
= formal.A1passive_p.
```

Applying the formal passive `A1` recovery gives the same expression equal to
`v.A1passive_p`.

Lean proves this in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean` as
`retainedPassive_F2_succ_mul_rawEdgeTupleA3_fderiv_eq_sourceStagedSuccessorA3`,
`A1passive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`,
and
`A1passive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_A1passive`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-a1passive-target-staged-shear.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-a1passive-target-staged-shear.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-a1passive-target-staged-shear.md`.

Kill condition: the terminal raw lower-left target derivative must not be
identified with zero before multiplication by `coord.F2(q.succ)`.  The
successor `F2` correction must be the target-recovered family
`retainedPassiveTargetRecoveredSuccessorF2At z Dzv`, not the source-staged
family.  If the theorem is read as staging `Ctop`, staging `F3`, whole-tuple
target-side normalization, determinant equality, or measure transport, it
overclaims.

Nonclaims: no `Ctop` target staging, no `F3` target staging, no whole-tuple
target-side normalization, no determinant-one target-side `LinearEquiv`, no
actual derivative determinant formula, no measure theorem, no normal
crossings, pole order, or RLCT is proved by this passive `A1` target-staged
bridge.

## A2 retained-passive Ctop target-staged endpoint shear

Status: Proved in Lean; reproduced on paper; focused and full builds passed;
sorry/whitespace/axiom audits passed; xhigh checker passed.

Claim: in the zero-tail and positive-tail Ctop endpoint formulas, the
successor correction at `0 : Fin (M+1)` can be written using the
target-recovered successor `F2` family and the raw lower-left target readout:

```text
Dzv.Ctop
  - targetXsuccF2(0) * coord.solvedA3(0)
  - coord.F2(0.succ) * rawEdgeTupleA3(Dzv,0)
  + explicit_tail_term
= formal.Ctop.
```

For `M = 0`, `explicit_tail_term` is absent.  For `0 < M`, it is the already-
proved first suffix-product derivative expression, kept in the landed
noncommutative order.  Multiplication by `Tail` recovers the source `Ctop`
tangent.

Lean proves this in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean` as
`Ctop_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`,
`Ctop_tail_pos_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`,
`Ctop_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop`,
and
`Ctop_tail_pos_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-ctop-target-staged-endpoint-shear.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-ctop-target-staged-endpoint-shear.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-ctop-target-staged-endpoint-shear.md`.

Kill condition: in the `M = 0` case, the terminal raw lower-left target
derivative must not be identified with zero before multiplication by the
terminal zero extended `F2` slot.  In the positive-tail case, the explicit
suffix derivative term must not be dropped, expanded, or reordered.  If the
theorem is read as `F3` target staging, whole-tuple target-side normalization,
determinant equality, or measure transport, it overclaims.

Nonclaims: no `F3` target staging, no whole-tuple target-side normalization,
no determinant-one target-side `LinearEquiv`, no actual derivative determinant
formula, no measure theorem, no normal crossings, pole order, or RLCT is
proved by this Ctop target-staged endpoint bridge.

## A2 retained-passive all-edge pair source-staged target shear

Status: Proved in Lean; reproduced on paper; focused and full builds passed;
xhigh review passed.

Claim: define the all-edge staged successor source tangent family by `Fin.snoc`.
For a nonterminal retained edge `q = p.castSucc`, the family value is the
source tangent `v.F2_(p.succ)` transported along
`Fin.succ_castSucc p : p.castSucc.succ = p.succ.castSucc`; for the terminal
edge `q = Fin.last M`, the family value is zero.  With this family `Xsucc`,
the normalized actual target edge-family pair

```text
U_F(q) = Dzv.F2_q + rawEdgeTupleA1(Dzv)_q * coord.F2 q.castSucc
         - Xsucc(q) * coord.C q,
U_C(q) = Dzv.C_q  + rawEdgeTupleA3(Dzv)_q * coord.F2 q.castSucc
```

equals the point-specialized formal `(F2,C)` output family.  Applying the
already-proved formal edge-pair inverse recovers the full source `(F2,C)`
family `(v.F2, v.C)`.

Lean proves this in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean` as
`retainedPassiveSourceStagedSuccessorF2`,
`retainedPassiveSourceStagedSuccessorF2_castSucc`,
`retainedPassiveSourceStagedSuccessorF2_last`,
`F2C_all_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`,
and
`F2C_all_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_sourcePair`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-all-edge-pair-source-staged-target-shear.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-all-edge-pair-source-staged-target-shear.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-all-edge-pair-source-staged-target-shear.md`.

Kill condition: terminal zero is used only at `Fin.last M`; the edge before the
terminal edge still uses the stored successor source tangent.  If this theorem
is read as a target-side determinant-one equivalence, a determinant formula,
or the full descending construction, it overclaims.

Nonclaims: no descending induction, no target-side `LinearEquiv`, no
determinant-one shear, no actual derivative determinant formula, no measure
theorem, no normal crossings, pole order, or RLCT is proved by this all-edge
package.

## A2 retained-passive edge-pair source-staged tuple assembly

Status: Proved in Lean; reproduced on paper; focused and full builds passed;
xhigh review passed.

Claim: the hybrid whole-tuple package keeps the derivative-staged
`A1passive`, passive `A3`, `Ctop`, and `F3` entries from
`shearedTopologyTupleEdgeRawOrderFDerivAt`, replaces only the `(F2,C)`
edge-family branch by the all-edge source-staged normalized pair, and agrees
with the point-specialized formal raw-order Jacobian.

Lean proves this in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean` as
`edgePairSourceStagedShearedTopologyTupleEdgeRawOrderFDerivAt` and
`edgePairSourceStaged_sheared_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-edge-pair-source-staged-tuple-assembly.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-edge-pair-source-staged-tuple-assembly.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-edge-pair-source-staged-tuple-assembly.md`.

Kill condition: only the `(F2,C)` branch is source-staged.  If the theorem is
read as a fully source-staged tuple, target-side linear equivalence,
determinant-one shear, determinant equality, or measure theorem, it overclaims.

Nonclaims: no target-side `LinearEquiv`, no determinant-one shear, no actual
derivative determinant formula, no measure theorem, no normal crossings, pole
order, or RLCT is proved by this hybrid tuple package.

## A2 retained-passive passive A1 source-staged shear

Status: Proved in Lean; reproduced on paper; focused and full builds passed;
sorry/whitespace/axiom audits passed; xhigh boundary review passed.

Claim: define the all-edge staged successor lower-left tangent family by
`Fin.snoc`.  For a nonterminal edge `q = p.castSucc`, the family value is the
stored passive source tangent `v.A3passive_p`; for the terminal edge
`q = Fin.last M`, the family value is zero.  Lean proves the nonterminal
projection derivative

```text
d(solvedA3_{p.castSucc})_z(v) = v.A3passive_p
```

and the all-edge multiplier identity

```text
coord.F2 q.succ * d(solvedA3_q)_z(v)
  = coord.F2 q.succ * XsuccA3(q).
```

The terminal case uses `coord.F2 (Fin.last (M+1)) = 0`; it does not identify
the terminal `solvedA3` derivative.  Substituting this identity and the
all-edge successor `F2` derivative readout into the old passive `A1` bridge
gives the passive `A1` source-staged formula.

Lean proves this in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean` as
`retainedPassiveSourceStagedSuccessorA3`,
`retainedPassiveSourceStagedSuccessorA3_castSucc`,
`retainedPassiveSourceStagedSuccessorA3_last`,
`fderiv_retainedPassive_toCoordinateData_solvedA3_castSucc_apply`,
`fderiv_retainedPassive_toCoordinateData_F2_succ_apply`,
`retainedPassive_F2_succ_mul_fderiv_solvedA3_eq_sourceStagedSuccessorA3`,
and
`A1passive_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-a1passive-source-staged-shear.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-a1passive-source-staged-shear.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-a1passive-source-staged-shear.md`.

Kill condition: if `d(solvedA3_q) = XsuccA3(q)` is asserted for all `q`, the
claim is false at the terminal edge.  If the terminal zero `F2` multiplier is
removed, the all-edge multiplier identity overclaims.  If the theorem is read
as staging `Ctop`, staging `F3`, or staging the whole tuple, it overclaims.

Nonclaims: no `Ctop` staging, no `F3` staging, no fully source-staged tuple,
no target-side `LinearEquiv`, no determinant-one shear, no actual derivative
determinant formula, no measure theorem, no normal crossings, pole order, or
RLCT is proved by this passive `A1` source-staged bridge.

## A2 retained-passive formal non-edge recovery

Status: Proved in Lean; reproduced on paper; focused and full builds passed;
sorry/whitespace/axiom audits passed; xhigh review passed.

Claim: for `u = retainedPassiveFormalRawOrderJacobianAt z v`, the formal
raw-order map recovers the non-edge source branches by

```text
u.A1passive_p = v.A1passive_p,
Tail * u.Ctop = v.Ctop,
u.F3 * (-(coord.solvedA1 (Fin.last M)))^{-1} = v.F3.
```

Lean proves this in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean` as
`retainedPassiveFormalRawOrderJacobianAt_recovers_A1passive`,
`retainedPassiveFormalRawOrderJacobianAt_recovers_Ctop`, and
`retainedPassiveFormalRawOrderJacobianAt_recovers_F3`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-formal-nonedge-recovery.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-formal-nonedge-recovery.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-formal-nonedge-recovery.md`.

Kill condition: these are recovery identities for the formal map only.  If
they are used to claim that the actual Frechet derivative has been converted to
the formal map by a determinant-one target-side equivalence, the argument
overclaims.  The `Ctop` and `F3` formulas must keep the determinant-chart
hypothesis; only `A1passive` is chart-free.

Nonclaims: no actual derivative identification, no `Ctop` source staging, no
`F3` source staging, no target-side `LinearEquiv`, no determinant-one shear,
no actual derivative determinant equality, no measure theorem, no normal
crossings, pole order, or RLCT is proved by this formal recovery package.

## A2 retained-passive nonterminal edge-pair staged target shear

Status: Proved in Lean; reproduced on paper; focused and full builds passed;
first xhigh review failed on a derivative/source-staging mismatch; Lean fixed;
xhigh re-review passed.

Claim: for a nonterminal retained-passive edge `q = p.castSucc` with
`p : Fin M`, if the staged successor input `Xsucc` is the source tangent
`v.F2_(p.succ)` transported along
`Fin.succ_castSucc p : p.castSucc.succ = p.succ.castSucc`, then the normalized
actual target pair

```text
U_F = Dzv.F2_q + rawEdgeTupleA1(Dzv)_q * coord.F2 q.castSucc
      - Xsucc * coord.C q,
U_C = Dzv.C_q  + rawEdgeTupleA3(Dzv)_q * coord.F2 q.castSucc
```

equals the corresponding point-specialized formal `(F2,C)` output pair, and
the formal edge inverse recovers the current source `F2` and `C` tangents.

Lean proves the source-staged public package as
`fderiv_retainedPassive_toCoordinateData_F2_nonterminal_succ_apply`,
`F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`,
`F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F2`,
and
`F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_C`.
The internal derivative-staged bridge is
`F2C_nonterminal_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`,
`F2C_nonterminal_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F2`,
and
`F2C_nonterminal_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_C`
in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-nonterminal-edge-pair-staged-target-shear.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-nonterminal-edge-pair-staged-target-shear.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-nonterminal-edge-pair-staged-target-shear.md`.

Kill condition: the theorem is one-step and staged.  If read as the full
descending target-side construction, or if `Xsucc` is silently set to zero at
a nonterminal edge, it overclaims.  If the dependent-index cast is omitted, the
statement is not the actual Lean source-tangent theorem.

Nonclaims: no full descending induction, no target-side determinant-one linear
equivalence, no actual derivative determinant formula, no measure theorem, no
normal crossings, pole order, or RLCT is proved by this one-step result.

## A2 retained-passive terminal edge-pair target shear

Status: Proved in Lean; reproduced on paper; xhigh review passed.

Claim: at the terminal retained-passive edge `p = Fin.last M`, the normalized
actual target-side pair

```text
U_F = Dzv.F2_p + rawEdgeTupleA1(Dzv)_p * coord.F2 p.castSucc,
U_C = Dzv.C_p  + rawEdgeTupleA3(Dzv)_p * coord.F2 p.castSucc
```

equals the corresponding point-specialized formal raw-order `(F2,C)` output
pair.  Therefore the formal inverse formulas recover `v.F2_p` and `v.C_p`
from `(U_F,U_C)`.

Lean proves this in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean` as
`F2C_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`,
`F2C_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F2`,
and
`F2C_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_recovers_C`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-terminal-edge-pair-target-shear.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-terminal-edge-pair-target-shear.md`.

Review:
`threads/03-block-product-reduction/review-a2-retained-passive-terminal-edge-pair-target-shear.md`,
accepted by xhigh `Mendel` and `Ramanujan`.

Kill condition: this theorem is terminal-edge only.  Nonterminal edges still
carry the successor-`F2` derivative term and need a descending/triangular
construction.  The target shear uses `coord.F2 p.castSucc`, while the formal
inverse uses `coord.F2 p.succ`; confusing these two slots breaks the endpoint
calculation.

Nonclaims: no nonterminal staged target-side shear, global determinant-one
linear equivalence, actual derivative determinant equality, measure theorem,
normal crossings, pole order, or RLCT is proved by this terminal package.

## A2 retained-passive edge-pair product equivalence

Status: Proved in Lean; reproduced on paper; xhigh implementation review
passed.

Claim: the edge-local formal `(F,C)` equivalence packages over all
retained-passive edges and transports to raw-order separated `(F2,C)` families.
At a determinant-chart point, the inverse recovers the source edge-pair
families from the formal raw-order output.

Lean names include `edgeLocalFCPairPiLinearEquiv`,
`retainedPassiveFormalRawF2CLinearEquiv`,
`retainedPassiveFormalRawF2CLinearEquivAt`, and
`retainedPassiveFormalRawF2CLinearEquivAt_symm_recovers_sourcePair`.

Review:
`threads/03-block-product-reduction/review-a2-retained-passive-edge-pair-product-equiv.md`,
accepted by xhigh `Huygens`.

Kill condition: this is not a statement about the actual Frechet derivative
and does not include endpoint `Ctop`/`F3` factors.

Nonclaims: no full determinant equality, measure theorem, normal crossings,
pole order, or RLCT is proved by this equivalence.

## A2 retained-passive terminal `F2` target shear

Status: Proved in Lean; reproduced on paper; xhigh implementation review
passed.

Claim: for the terminal retained-passive edge, the successor `F2` coordinate is
the constant zero coordinate, so the actual `F2` target-shear bridge simplifies
to `dY12_p + dA1_p * coord.F2 p.castSucc = formal.F2_p`.

Lean names:

```text
fderiv_retainedPassive_toCoordinateData_F2_last_apply
F2_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

Review:
`threads/03-block-product-reduction/review-a2-retained-passive-terminal-f2-target-shear.md`,
accepted by xhigh `Huygens`.

Kill condition: this claim is terminal-edge only.  Applying it to all edges
would be wrong because nonterminal edges still have the successor derivative.

Nonclaims: no nonterminal staged shear, determinant equality, measure theorem,
normal crossings, pole order, or RLCT is proved by this bridge.

## A2 retained-passive actual derivative tuple assembly

Status: Proved in Lean; reproduced on paper; xhigh review passed.

Claim: the tuple obtained from the actual raw-order Frechet derivative by the
six landed retained-passive component corrections agrees with
`retainedPassiveFormalRawOrderJacobianAt`.

Lean defines `shearedTopologyTupleEdgeRawOrderFDerivAt` and proves
`sheared_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-actual-derivative-tuple-shear-assembly.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-actual-derivative-tuple-shear-assembly.md`.

Review:
`threads/03-block-product-reduction/review-a2-retained-passive-actual-derivative-tuple-shear-assembly.md`.

Kill condition: this theorem must remain componentwise tuple packaging.  If it
is used for determinant equality before a determinant-one target-side linear
equivalence is constructed, the argument overclaims.

Nonclaims: no actual derivative determinant formula, no measure/Jacobian-
density theorem, no normal crossings, pole order, or RLCT is proved by this
assembly.

## A2 retained-passive formal F2 recovery

Status: Proved in Lean; reproduced on paper; xhigh review passed.

Claim: from the formal output
`u = retainedPassiveFormalRawOrderJacobianAt z v`, each source `F2` tangent is
recovered by

```text
(coord.solvedA1 p)^-1 *
  (coord.F2 p.succ * u.C_p - u.F2_p)
= v.F2_p.
```

Lean proves this as `retainedPassiveFormalRawOrderJacobianAt_recovers_F2` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-formal-f2-recovery.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-formal-f2-recovery.md`.

Review:
`threads/03-block-product-reduction/review-a2-retained-passive-formal-f2-recovery.md`.

Kill condition: the theorem depends on determinant-chart invertibility of
`coord.solvedA1 p`; it is not available off chart and must not be read as a
statement about the actual Frechet derivative.

Nonclaims: no staged target-side shear, determinant equality, measure theorem,
normal crossings, pole order, or RLCT is proved by this recovery identity.

## A2 edge-local `(F,C)` pair inverse equivalence

Status: Proved in Lean; reproduced on paper; xhigh review passed.

Claim: for `det A` a unit, the generic finite edge-local formal map

```text
(F,C) |-> (-(A + H*G)*F + H*C, -G*F + C)
```

is a linear equivalence.  The inverse sends `(U,V)` to

```text
(A^{-1} * (H*V - U),
 V + G * (A^{-1} * (H*V - U))).
```

Lean proves this in
`lean/DLNFibre/DLN/Aoyagi/MatrixLinearDeterminant.lean` as
`edgeLocalFCPairLinearMapInverse`, `edgeLocalFCPairLinearMapInverse_apply`,
`edgeLocalFCPairLinearEquiv`, `edgeLocalFCPairLinearEquiv_apply`, and
`edgeLocalFCPairLinearEquiv_symm_apply`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-edge-local-fc-pair-inverse-equiv.md`
and
`threads/03-block-product-reduction/statement-card-a2-edge-local-fc-pair-inverse-equiv.md`.

Review:
`threads/03-block-product-reduction/review-a2-edge-local-fc-pair-inverse-equiv.md`,
accepted by xhigh `Halley the 5th`.

Kill condition: this theorem is generic edge-local finite linear algebra.  It
must not be used as the retained-passive total target-side shear without
separately packaging the product/regrouping over all edges.

Nonclaims: no retained-passive total target-side shear, actual derivative
determinant comparison, measure theorem, normal crossings, pole order, or RLCT
is proved by this edge-local equivalence.

## A2 retained-passive formal C recovery

Status: Proved in Lean; reproduced on paper; xhigh review passed.

Claim: from the formal output
`u = retainedPassiveFormalRawOrderJacobianAt z v`, each source `C` tangent is
recovered by adding back the lower-left shear using the previously recovered
source `F2` tangent:

```text
u.C_p + coord.solvedA3 p *
  ((coord.solvedA1 p)^-1 * (coord.F2 p.succ * u.C_p - u.F2_p))
= v.C_p.
```

Lean proves this as `retainedPassiveFormalRawOrderJacobianAt_recovers_C` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-formal-c-recovery.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-formal-c-recovery.md`.

Review:
`threads/03-block-product-reduction/review-a2-retained-passive-formal-c-recovery.md`,
accepted by xhigh `Huygens the 5th`.

Kill condition: this theorem must continue to use the formal `F2` recovery and
the formal `C` formula only.  It is not a substitute for constructing the
target-side determinant-one shear.

Nonclaims: no staged target-side shear, determinant equality, measure theorem,
normal crossings, pole order, or RLCT is proved by this recovery identity.

## A2 retained-passive actual derivative passive A1 formal component bridge

Status: Proved in Lean; reproduced on paper; xhigh implementation review
passed.

Claim: after the successor-`F2`/lower-left product corrections, the actual
Frechet derivative's passive `A1` component agrees with the passive `A1`
component of `retainedPassiveFormalRawOrderJacobianAt`.

Lean proves the component identity as
`fderiv_topologyTupleEdgeRawOrder_A1passive_shear_apply` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`, and the
formal component bridge as
`A1passive_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`
in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-actual-derivative-a1passive-shear-bridge.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-actual-derivative-a1passive-shear-bridge.md`.

Review:
`threads/03-block-product-reduction/review-a2-retained-passive-actual-derivative-a1passive-shear-bridge.md`.

Kill condition: the theorem must stay restricted to passive top-left indices
`p : Fin M`.  The first top-left coordinate is `Ctop`, not a stored passive
coordinate, and requires the solved first-edge top-left block and tail-product
derivative corrections.

Nonclaims: no `Ctop` derivative bridge, terminal `F3` derivative bridge,
global determinant-one shear linear equivalence, full analytic derivative
factorization, determinant equality, measure/Jacobian-density theorem, normal
crossings, pole order, or RLCT is proved by this bridge.

## A2 retained-passive actual derivative Ctop formal component bridge

Status: Proved in Lean; reproduced on paper; independent xhigh pen-and-paper
check passed; xhigh implementation review passed.

Claim: after the successor-`F2`/lower-left product corrections and the
passive-tail inverse correction, the actual Frechet derivative's first
top-left `Ctop` component agrees with the `Ctop` component of
`retainedPassiveFormalRawOrderJacobianAt`.

Lean proves the component identity as
`fderiv_topologyTupleEdgeRawOrder_Ctop_shear_apply` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`, and the
formal component bridge as
`Ctop_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-actual-derivative-ctop-shear-bridge.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-actual-derivative-ctop-shear-bridge.md`.

Pen-and-paper review:
`Einstein the 5th`, xhigh read-only reviewer, PASS.

Implementation review:
`threads/03-block-product-reduction/review-a2-retained-passive-actual-derivative-ctop-shear-bridge.md`
accepted by xhigh `Bohr the 5th`.

Kill condition: the correction term
`- d(Tail^{-1})(v) * coord.Ctop` is essential.  Dropping it leaves the
variation of the passive top-left tail.  The theorem must keep the full
`F2full` successor slot `coord.F2 ((0 : Fin (M+1)).succ)`.

Nonclaims: no terminal `F3` derivative bridge, global determinant-one shear
linear equivalence, full analytic derivative factorization, determinant
equality, measure/Jacobian-density theorem, normal crossings, pole order, or
RLCT is proved by this bridge.

## A2 retained-passive actual derivative Ctop successor source-staging bridge

Status: Proved in Lean locally; reproduced on paper; xhigh implementation
review passed.

Claim: in the actual Frechet derivative's first top-left `Ctop` bridge, the
successor `F2` derivative and the multiplied successor lower-left derivative
can be replaced by the staged source tangent families, while the passive-tail
inverse derivative remains explicit.

Lean proves the bridge as
`Ctop_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`
in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-ctop-source-staged-successor-shear.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-ctop-source-staged-successor-shear.md`.

Review:
`threads/03-block-product-reduction/review-a2-retained-passive-ctop-source-staged-successor-shear.md`
passed by xhigh `Kant`.

Kill condition: the theorem must keep
`d_y(Tail(y)^{-1})_z(v) * coord.Ctop` as an explicit term.  Expanding this
term into `-Tail^{-1} * dTail * Tail^{-1}` requires a separate product and
inverse derivative calculation.

Nonclaims: no explicit tail-inverse derivative formula, no recursive product
formula for `dTail`, no `F3` source staging, no global determinant-one shear
linear equivalence, full analytic derivative factorization, determinant
equality, measure/Jacobian-density theorem, normal crossings, pole order, or
RLCT is proved by this bridge.

## A2 retained-passive tail-inverse derivative bridge

Status: Proved in Lean locally; pen-and-paper reproduction written and
checked; independent xhigh implementation review passed; focused and full
builds, sorry scan, whitespace check, and axiom audit passed.

Claim: for the passive top-left tail map

```text
Tfun(y) = retainedPassiveA1TailAfterFirst (ofTopologyTuple y).A1seed,
```

the Frechet derivative of the inverse tail at a determinant-chart point is

```text
d_y(Tfun(y)^{-1})_z(v) = -Tail^{-1} * dTail * Tail^{-1},
```

where `Tail = Tfun(z)` and `dTail = (fderiv Tfun z) v`.

Lean proves this as
`fderiv_retainedPassive_A1TailAfterFirst_inv_eq_tail_fderiv` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`, and also
proves the Ctop consumer
`Ctop_tail_fderiv_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-tail-inverse-fderiv.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-tail-inverse-fderiv.md`.

Review:
pen-and-paper PASS from xhigh `Boole`; Lean/API scout PASS from xhigh
`Mencius`; implementation review PASS from xhigh `Epicurus`, recorded at
`threads/03-block-product-reduction/review-a2-retained-passive-tail-inverse-fderiv.md`.

Kill condition: if `dTail` is expanded or named as a source-staged recursive
product in this theorem, the statement overclaims.  The theorem only identifies
the inverse derivative in terms of the actual Frechet derivative of the tail
map.

Nonclaims: no recursive product formula for `dTail`, no full `Ctop` source
staging, no `F3` source staging, no global determinant-one shear linear
equivalence, full analytic derivative factorization, determinant equality,
measure/Jacobian-density theorem, normal crossings, pole order, or RLCT.

## A2 retained-passive tail product derivative recursion

Status: Proved in Lean locally; pen-and-paper reproduction written and
checked; focused and full builds passed; independent xhigh implementation
review passed after a documentation wording fix; sorry scan, whitespace check,
and axiom audit passed.

Claim: for the passive top-left suffix product

```text
P_i(y) = residualFactorProduct
  (ofTopologyTuple y).A1seed (Fin.last (M+1)) i,
```

the endpoint derivative is zero, and for `q : Fin M`, `p=q.succ`, the
recursive derivative step is

```text
d(P_{p.castSucc})_z(v)
  = d(P_{p.succ})_z(v) * A1seed_z(p)
    + P_{p.succ}(z) * v.A1passive_q.
```

Lean proves this as
`differentiableAt_retainedPassiveA1seed_residualFactorProduct`,
`fderiv_retainedPassive_A1seed_residualFactorProduct_self_apply`, and
`fderiv_retainedPassive_A1seed_residualFactorProduct_succ_castSucc_apply` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-tail-product-fderiv-recursion.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-tail-product-fderiv-recursion.md`.

Review:
pen-and-paper PASS from xhigh `Bacon`; Lean/API scout PASS from xhigh `Kuhn`;
implementation review PASS after documentation wording fix from xhigh
`Schrodinger`, recorded at
`threads/03-block-product-reduction/review-a2-retained-passive-tail-product-fderiv-recursion.md`.

Kill condition: if the recurrence includes the dummy `A1seed 0`, reverses the
noncommutative product-rule terms, or leaves `d(A1seed(q.succ))` opaque
instead of `v.1 q`, it is not the intended passive-tail recurrence.

Nonclaims: no closed finite-sum formula for `dTail`, no inverse-tail
derivative theorem, no full `Ctop` source staging, no `F3` source staging, no
global determinant-one shear linear equivalence, full analytic derivative
factorization, determinant equality, measure/Jacobian-density theorem, normal
crossings, pole order, or RLCT.

## A2 retained-passive tail endpoint derivative

Status: Proved in Lean locally; pen-and-paper reproduction written; focused
and full builds passed; pen-and-paper and Lean/API scouts passed; independent
implementation review passed; sorry scan, whitespace check, and axiom audit
passed.

Claim: the actual retained-passive top-left tail after the first edge has zero
derivative in the `M=0` empty-tail case, and in positive length its derivative
is the first passive suffix-product recurrence step:

```text
d(Tail)_z(v)
  = d(Psucc)_z(v) * A1seed_z(p) + Psucc(z) * v.A1passive_0.
```

Lean proves this as
`fderiv_retainedPassive_A1TailAfterFirst_zero_apply`,
`fderiv_retainedPassive_A1TailAfterFirst_succ_apply`, and
`fderiv_retainedPassive_A1TailAfterFirst_pos_apply` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-tail-endpoint-fderiv.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-tail-endpoint-fderiv.md`.

Review:
pen-and-paper scout PASS from xhigh `Goodall`; Lean/API scout PASS from xhigh
`Bohr`; implementation review PASS from xhigh `Russell`, recorded at
`threads/03-block-product-reduction/review-a2-retained-passive-tail-endpoint-fderiv.md`.

Kill condition: if the theorem includes the dummy `A1seed 0`, requires
determinant-chart membership, reverses either product-rule order, or claims a
closed finite-sum expansion of `dTail`, it is not the intended endpoint
specialization.

Nonclaims: no closed finite-sum formula for `dTail`, no full `Ctop` source
staging, no `F3` source staging, no target-side determinant-one shear,
determinant equality, measure/Jacobian-density theorem, normal crossings, pole
order, or RLCT.

## A2 retained-passive Ctop tail endpoint substitution

Status: Proved in Lean locally; pen-and-paper reproduction written; focused
and full builds passed; pen-and-paper and Lean/API scouts passed; independent
implementation review passed; sorry scan, whitespace check, and axiom audit
passed.

Claim: substituting the endpoint tail derivative into the existing Ctop
tail-inverse bridge gives two cases.  For `M=0`, the tail correction vanishes.
For `0 < M`, the tail correction becomes

```text
Tail^{-1}
  * ((fderiv Psucc z) v * data.A1seed p + Psucc z * v.A1passive_0)
  * Tail^{-1}
  * coord.Ctop.
```

Lean proves this as
`Ctop_tail_zero_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`
and
`Ctop_tail_pos_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`
in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-ctop-tail-endpoint-substitution.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-ctop-tail-endpoint-substitution.md`.

Review:
pen-and-paper scout PASS from xhigh `Godel`; Lean/API scout PASS from xhigh
`Hooke`; implementation review PASS from xhigh `Galileo`, recorded at
`threads/03-block-product-reduction/review-a2-retained-passive-ctop-tail-endpoint-substitution.md`.

Kill condition: if the theorem changes the sign of the tail correction,
commutes/reverses product-rule factors, moves `coord.Ctop` leftward, includes
dummy `A1seed 0`, or expands the remaining suffix derivative, it is not the
intended substitution theorem.

Nonclaims: no closed finite-sum formula for `dTail`, no full `Ctop` source
staging, no `F3` source staging, no target-side determinant-one shear,
determinant equality, measure/Jacobian-density theorem, normal crossings, pole
order, or RLCT.

## A2 retained-passive Ctop/F3 recovery consumers

Status: Proved in Lean locally; controller pen-and-paper reproduction written;
focused and full builds passed; sorry scan, whitespace check, and axiom audit
passed; independent xhigh implementation review passed after a documentation
repair exposing the determinant-chart hypothesis.

Claim: under `z in topologyTupleDetChartSet`, the already-landed staged Ctop
component equalities and F3 component equality recover the source tangent
components after the corresponding formal inverse normalizations:

```text
Tail * U_Ctop = v.Ctop
U_F3 * (-(coord.solvedA1 (Fin.last M)))^{-1} = v.F3.
```

Lean proves this as
`Ctop_tail_zero_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop`,
`Ctop_tail_pos_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop`,
and
`F3_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-ctop-f3-recovery-consumers.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-ctop-f3-recovery-consumers.md`.

Review:
xhigh `Turing` found no Lean fidelity issue and required only the explicit
determinant-chart assumption in the docs, recorded at
`threads/03-block-product-reduction/review-a2-retained-passive-ctop-f3-recovery-consumers.md`.

Kill condition: if the positive Ctop correction changes sign, moves outside
the two `Tail^{-1}` factors, expands the remaining suffix derivative as if a
finite-sum formula were proved, or if the F3 normalization uses passive
`Tail` instead of `coord.solvedA1 (Fin.last M)`, this is not the intended
consumer theorem.

Nonclaims: no closed finite-sum formula for `dTail`, no F3 early-tail
derivative recurrence, no full source-staged tuple theorem, no target-side
determinant-one shear, determinant equality, measure/Jacobian-density theorem,
normal crossings, pole order, or RLCT.

## A2 retained-passive actual derivative F3 formal component bridge

Status: Proved in Lean; reproduced on paper; independent xhigh checks passed.

Claim: after the earlier lower-left tail derivative correction and terminal
top-factor derivative correction, the actual Frechet derivative's terminal
`F3` component agrees with the `F3` component of
`retainedPassiveFormalRawOrderJacobianAt`.

Lean proves the component identity as
`fderiv_topologyTupleEdgeRawOrder_F3_shear_apply` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`, and the
formal component bridge as
`F3_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`.

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-actual-derivative-f3-shear-bridge.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-actual-derivative-f3-shear-bridge.md`.

Reviews:
`Epicurus the 5th` pen-and-paper PASS,
`Godel the 5th` Lean reconnaissance PASS, and
`threads/03-block-product-reduction/review-a2-retained-passive-actual-derivative-f3-shear-bridge.md`
accepted by xhigh `Jason the 5th`.

Kill condition: the theorem must keep right multiplication by the terminal
factor.  `LastTop` is `coord.solvedA1 (Fin.last M)` by the one-edge terminal
residual-factor lemma; for `M = 0` this is `coord.Ctop`, not an empty identity
and not the passive first-edge `Tail`.

Nonclaims: no global determinant-one shear linear equivalence, full analytic
derivative factorization, determinant equality, measure/Jacobian-density
theorem, normal crossings, pole order, or RLCT is proved by this bridge.

## A4 selected-entry analytic atlas/source-production frontier recheck

Status: Boundary recorded; no Lean theorem proposed.

Claim: Aoyagi pp. 19-22 justify the displayed Case 2 finite selected-entry
matrix algebra, but not a constructor from the finite selected-entry
certificate to `SelectedEntryAnalyticAtlasBoundary`.

Artifacts:
`threads/04-blow-up-certificate/reproduction-selected-entry-analytic-atlas-source-production-frontier-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-analytic-atlas-source-production-frontier.md`.

Positive content: the source supports the selected pivot chart, `D_J = u D'_J`,
`b'_i = u b_i`, regular `Q/P`, `C'_J^(S+1) = Q^-1 C_J^(S+1)`, the cleared
`D'''_J` block, displayed product identities, and the continue/stop
instructions.

Negative content: the source does not define analytic chart domains,
source-neighborhood coverage, analytic overlap maps, analytic
Jacobian/volume-form compatibility, source-produced successor/suffix data, or
branch termination as an atlas theorem.

Kill condition: reject any theorem named like
`SelectedEntryAnalyticAtlasBoundary.of_case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate_finiteSuppliedBranch`
if it fills `coverage`, `transition_regular`, `source_production`, or other
analytic fields from finite selected-entry coverage,
`SelectedEntryFiniteAffineTransitionRegularFamily`, or
`SourceProductionObligation` constructors.  Also reject a future producer that
collapses the continuing, actual-width stopped, and row-exhausted stopped
payloads.

Nonclaims: no analytic atlas existence, source production, transition
regularity, analytic Jacobian theorem, normal crossings, pole order, or RLCT.

## A4 selected-entry analytic atlas producer interface

Status: Lean interface checked locally; xhigh reviews passed.

Claim: `SelectedEntrySuppliedAnalyticAtlasProducer` is a supplied,
data-bearing interface above the finite selected-entry certificate layer.  Its
projection
`SelectedEntrySuppliedAnalyticAtlasProducer.toBoundary` fills the existing
`SelectedEntryAnalyticAtlasBoundary` socket with predicate wrappers around the
supplied data.

Artifacts:
`threads/04-blow-up-certificate/reproduction-selected-entry-analytic-atlas-producer-interface-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-analytic-atlas-producer-interface.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-analytic-atlas-producer-interface-a4.md`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/SelectedEntryAnalyticAtlasProducer.lean`.

The interface records one shared atlas context, open/source coverage, chart and
transition regularity, unit regularity, nonzero chart-domain weighted
pushforward measure compatibility, separate continuing / actual-width stopped /
row-exhausted stopped branch payloads with produced chart/source-domain
witnesses, and well-founded branch termination.  There is no constructor from
finite selected-entry coverage, finite affine transition regularity, or
`SourceProductionObligation`.

Focused build passed for
`DLNFibre.DLN.Aoyagi.SelectedEntryAnalyticAtlasProducer`.

The projection to `SelectedEntryAnalyticAtlasBoundary` is forgetful; shared
context coherence is a property of the producer, not of arbitrary boundaries
assembled from the exported predicate wrappers.

Nonclaims: no analytic atlas construction, extraction hypothesis, proved
Jacobian-density formula from `C.jacobianPrior`, normal crossings, pole order,
RLCT, source-rank coverage, or final Theorem 2 statement is proved.

## A4 Case 2 finite raw-pivot continuing successor boundary

Status: Proved in Lean; focused module build passed; xhigh review passed.

Claim: under `hS : 1 <= S` and
`hnext : J+2 <= prefixMinNat n (S+1)`, the successor Case 2 residual-block
chart-family boundary at `(S,J+1)` is inhabited by the nontrivial finite
selected-entry predicates, not by `True` predicates.

Lean theorem:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
  .finiteRawPivotContinuingSuccessorBoundary
```

Artifact:
`threads/04-blow-up-certificate/reproduction-case2-finite-raw-pivot-continuing-successor-boundary-a4.md`.

Kill condition: the theorem must remain a finite wrapper around
`finiteRawPivotChartFamilyBoundary`.  It must not be cited as analytic
next-chart construction, analytic transition regularity, source production,
branch termination, normal crossings, pole order, or RLCT extraction.

## A2 retained-passive F3 target-staged shear

Status: Proved in Lean; focused module build passed; xhigh review passed.

Claim: in positive retained-passive tail length, the terminal `F3` shear can
be stated with the earlier-tail derivative replaced by the recursive
target-staged lower-left tail derivative.

Lean theorem:

```text
fderiv_topologyTupleEdgeRawOrder_F3_targetStaged_shear_apply
```

Artifact:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-f3-target-staged-shear.md`.

Review:
`threads/03-block-product-reduction/review-a2-retained-passive-f3-target-staged-shear.md`
passed by xhigh `Bernoulli`.

Kill condition: this theorem is only a positive-tail substitution wrapper.  It
must not be cited as the full derivative/formal-Jacobian equality, determinant
equality, target-side linear equivalence, measure transport, normal crossings,
pole order, or RLCT.

## A2 Case 2 selected-entry Schur cleanup

Status: Proved in Lean; focused and full local builds passed; xhigh reviews
passed.

Claim: Aoyagi pp. 19-22's displayed Case 2 selected-entry cleanup is finite
matrix algebra:

```text
D = u E,
E Q = [[1,0],[c,Z-ca]],
P B E Q = B [[1,0],[0,Z-ca]]
```

with quotient witnesses `b_i = q_i b0` for the weighted row operation.  If the
old source block is `D = u E`, the selected variable is absorbed into the row
weights `B' = u B_old`; there is no second global `u`.

Lean theorems added:

```text
pivotFirstMatrix_mul_pivotQ_eq_pivotPostQBlock
case2SourceSelectedSubstitutionBlockOfMem_eq_mul_normalized
case2SourceSelectedNormalizedBlockOfMem_mul_pivotQ
case2DisplayedPaperDchart_mul_Q_eq_pivotPostQBlock
```

Artifacts:
`threads/03-block-product-reduction/reproduction-a2-case2-selected-entry-schur-cleanup.md`
and
`threads/03-block-product-reduction/statement-card-a2-case2-selected-entry-schur-cleanup.md`.

Review:
`threads/03-block-product-reduction/review-a2-case2-selected-entry-schur-cleanup.md`
passed by xhigh source/scope reviewer `Ampere the 4th` and xhigh Lean/API
reviewer `Franklin the 4th`.

Kill condition: this claim must not be cited as analytic atlas coverage,
chart-domain regularity, transition regularity, Jacobian or volume
compatibility, source production, branch termination, source-prior transport,
normal crossings, pole order, RLCT, or as identification of `Z-ca` with the
next residual block without the separate continuing-branch reindexing and size
hypotheses.
