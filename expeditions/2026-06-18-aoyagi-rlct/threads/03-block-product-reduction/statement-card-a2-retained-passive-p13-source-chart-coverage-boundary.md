# Statement Card - A2 retained-passive p.13 source-chart coverage boundary

## Lean Files

Existing retained-passive chart objects:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
```

Relevant downstream coverage socket:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

Relevant fixed-base neighborhood infrastructure:

```text
lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
```

## Existing Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChartSet
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.detChart_sourceRecursiveDetChart_openPartialHomeomorph
DLNFibre.DLN.Aoyagi.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_subset_localSource
```

## Proposed Lean Target

No theorem is formalised by this card yet.  The first non-wrapper target should
remove or sharpen the coverage hypothesis in the local-measure consumer:

```text
exists_retainedPassiveP13LocalSource_coverage :
  exists Ulocal localSource, IsOpen Ulocal /\ x0 in Ulocal /\
    Ulocal inter paperEndpointFixedBaseSourceRankStratum ... subset
      Ulocal inter localSource
```

The intended `localSource` is not an arbitrary copy of the source stratum.  It
should be tied to the retained-passive chart, for example as the preimage of
`sourceRecursiveDetChartSet` under the fixed-base source edge-matrix map, with
the already formalised retained-passive `edgeMatrix` / `sourceReadback`
chart available on that local source.

## Reproduction

```text
reproduction-a2-retained-passive-p13-source-chart-boundary.md
```

## Claim Boundary

Aoyagi pp. 10-13 support the finite retained-passive block algebra and the
p.13 active readout

```text
[ Ctop - I      -F2
  -F3        D - F3 F2 ].
```

The passive variables reconstruct source edges and supply unit factors, but
they are not additional singular variables in the p.13 readout.

## Proved

Already proved in Lean before this card:

- the retained-passive coordinate data and source map `edgeMatrix`;
- the source-side readback `sourceReadback`;
- the two finite inverse laws on determinant/source-recursive domains;
- openness of `detChartSet` and `sourceRecursiveDetChartSet`;
- the retained-passive open partial homeomorphism.

Subsequent Lean bridge:

- `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean` defines the
  retained-passive p.13 local source as the fixed-base preimage of
  `sourceRecursiveDetChartSet` and proves the self-base open-neighborhood
  coverage wrapper.  See
  `statement-card-a2-retained-passive-local-source-coverage.md`.

## Assumed

For the proposed coverage theorem:

- a source parameter map into fixed-base edge families;
- continuity of that map at the basepoint;
- basepoint membership in the retained-passive recursive determinant chart;
- the exact local relation between the paper source-rank stratum and the
  retained-passive local source.

## Cited

None for the finite block algebra.  The later normal-crossing-to-RLCT
extraction remains the expedition's separate cited analytic boundary.

## Deferred

Coverage, exact-rank/source-rank finite cover, measure pushforward, Jacobian
density transport, bounded transported prior, normal crossings, pole order,
and RLCT extraction are deferred from this card.

## Structure & Ideas Observed

The load-bearing mechanism is that the passive variables reconstruct the
source edge family while leaving the p.13 active square-sum on the same
coordinates `Ctop - I`, `F2`, `F3`, and residual product `D`.  The passive
determinant conditions should therefore be treated as unit data for local
coverage and measure transport, not as new singular coordinates.

The generative next step is to pull the already proved open
`sourceRecursiveDetChartSet` back along the fixed-base edge-family map and
then prove the source-rank stratum is locally contained in that charted
source.  Only after that should the measure/Jacobian target be opened.

## Route

Controller route synthesis from Franklin the 3rd and Socrates the 3rd:

1. Define a retained-passive p.13 local source as a fixed-base source
   preimage of `sourceRecursiveDetChartSet`.
2. Use fixed-base continuous-edge neighborhood lemmas to obtain an open
   neighborhood on which the recursive determinant chart holds.
3. Prove the coverage inclusion against
   `paperEndpointFixedBaseSourceRankStratum` without choosing
   `localSource` to be merely the source stratum.
4. Keep measure/Jacobian transport as a separate theorem family.

## Status

Reviewed boundary card.  Boyle the 3rd passed the reproduction/card/ledger
package with no blocking issue; see
`review-a2-retained-passive-p13-source-chart-coverage-boundary.md`.

The first Lean bridge following this boundary is now recorded in
`statement-card-a2-retained-passive-local-source-coverage.md`.  It resolves
the paper/Lean index convention at the local-source level.  Any later Jacobian
theorem must still define the `A2/F2` column width internally before using the
symbolic determinant exponent.
