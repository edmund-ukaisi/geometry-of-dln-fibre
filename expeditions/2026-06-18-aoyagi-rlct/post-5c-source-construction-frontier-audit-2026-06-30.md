# Post-5c Source-Construction Frontier Audit

Date: 2026-06-30.

Branch/head:

```text
expedition/aoyagi-rlct @ 5c113254
```

Status: controller audit after the relative passive-theta raw-order endpoint
sector theorem.  This audit deliberately does not propose a Lean wrapper.

## Trigger

The last banked theorem,

```text
exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
```

puts endpoint-sector measurability, determinant-chart membership, raw-order
chart membership, source-chart readback, and one-stage/two-stage raw-order
pushforward presentations on one local shrink.  The question was whether that
new uniform local package now unlocks a non-thin A2/A4/A5 theorem.

## Direct Source Check

The controller re-read the relevant Aoyagi preprint pages from

```text
paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/aoyagi-2023-neural-networks-preprint.pdf
```

Pages 10-13 prove the block Schur elimination and the product reduction:
regular block matrices transform a product of nearby matrices into a
top-left regular block plus a lower-right product, and the loss splits into a
finite regular contribution plus the reduced product loss.  This supports the
retained-passive coordinate algebra and the Jacobian/local-coordinate work
already formalised.  It does not state an original-prior transport theorem,
raw-order Haar transport, a source-image theorem, or a density comparison for
the original DLN parameter measure.

Pages 19-22 give the Case 2 blow-up algebra: the displayed pivot blow-up,
the `Q` and `P` row/column operations, the transformed block, the continuing
or row-exhausted alternatives, and the candidate order expression.  This
supports finite selected-entry transition/source-frontier packages.  It does
not define analytic chart domains, chart-token coverage, analytic overlap
regularity, analytic Jacobian compatibility, or a produced global successor
object.

Pages 24-27 give the Lemma 5 interval-count argument.  The source supplies
the interval-count codomain and displayed branch families for the lower-bound
side.  It does not give a Lean-level classifier on the present
`terminalMinimumLabels`, a selector-injectivity theorem, a counted-datum
back-to-label map, or a no-extra terminal-minimum coverage theorem.

## Xhigh Scout Results

Hume checked the A2 retained-passive/passive-theta frontier.  Verdict: no
new non-thin theorem follows from the relative raw-order endpoint-sector
package.  It would only provide another presentation of the same
chart-produced pushforward.  The remaining field is a genuine passive-variable
construction: explicit coordinate domain, source map, local inverse/readback,
image or coverage theorem, measure theorem, and Jacobian/source-density
accounting.

Peirce checked A4.  Verdict: the narrow Case 2 displayed source-production
field fill already exists in

```text
SelectedEntryAnalyticAtlasCase2FinalBridge.lean
```

via

```text
SelectedEntryCase2DisplayedA0SourceProduction.of_case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
```

No current finite selected-entry theorem honestly fills the full
`SelectedEntryAnalyticAtlasBoundary`: coverage, chart regularity, transition
regularity, unit regularity, analytic Jacobian compatibility, and branch
termination remain analytic/source fields.

James checked A5.  Verdict: no current A5 theorem satisfies the non-wrapper
bar.  Existing Eq5 endpoint-chain and own-block classifier adapters already
remove the abstract classifier object conditionally, but still assume the
real source-missing fields: deterministic-selector injectivity, terminal
`(p, alpha)` injectivity, an upper-bound/no-extra classifier, or a
counted-datum back-to-label theorem.

## Controller Decision

Do not add another theorem whose only effect is to restate an already supplied
field with different names.

The controller rechecked the current Lean inventory after this audit was
opened.  The broad phrase "build the retained-passive passive-variable
construction package" is now too coarse: substantial pieces of that package
already exist.  In particular, the current A2 files already provide:

```text
Case2PassiveTheta
case2PassiveThetaEndpointSourceChart
exists_open_case2PassiveThetaEndpointSourceChart_readback_leftInverse
exists_open_case2PassiveThetaEndpointTopologyTuple_sourceChart_injOn
exists_open_subset_measurableSet_case2PassiveThetaEndpointSectorSet
retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive
case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_mem_sourceRankStratum_and_localSource_and_residualBlockCoordinateMap_eq_chartMap
continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport_withPassive
measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_restrict_retainedPassiveP13LocalSource_eq_self
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass_sourceStratum_bounds
```

Thus the next A2 construction target is not another local inverse, support,
or chart-produced finite-integral theorem.  The remaining non-wrapper frontier
is the source-prior or full-image bridge:

```text
external/original local source measure
  -> retained-passive/passive-theta chart-produced measure
```

The next theorem should either construct this bridge or keep its missing
fields explicit.  The meaningful options are:

1. A local image/coverage theorem: nearby original source-rank points in a
   fixed-base source chart are in the image of the retained-passive passive
   coordinate chart, with a named local inverse.
2. A local source-prior domination theorem: a restricted external/original
   source measure is absolutely continuous with respect to the existing
   chart-produced passive product-domain pushforward, with locally bounded
   density.
3. A determinant/raw-order Haar transport theorem strong enough to identify
   the retained-passive source chart pushforward with the existing Haar-based
   raw-order measure interface.

Each option must name its domain, source map, inverse or support theorem, and
density/Jacobian comparison.  A theorem that merely defines the source measure
to be `Measure.map sourceChart (...)`, or one that still assumes the external
source-prior comparison, is not progress at this frontier.

## Nonclaims

This audit proves no Lean theorem.  It does not construct determinant-chart
Haar transport, raw-order Haar transport, original DLN source-prior transport,
exact passive-sector pushforward, source-image equality, source-rank coverage,
analytic atlas coverage, branch termination, normal crossings, pole order, or
RLCT extraction.

## Next Work Packet

Start an A2 construction card for the source-prior/full-image frontier.  The
card should name the exact current Lean inputs, state the smallest theorem
that would remove an external source-prior, Haar-transport, or local-image
coverage field, and include a pen-and-paper check separating the existing
chart-produced passive measure from any original DLN parameter prior.
