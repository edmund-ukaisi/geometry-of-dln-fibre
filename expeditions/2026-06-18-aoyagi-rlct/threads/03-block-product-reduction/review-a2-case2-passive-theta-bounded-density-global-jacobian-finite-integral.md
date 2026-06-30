# Review - A2 Case 2 passive theta bounded-density global-Jacobian finite integral

Date: 2026-06-30.

## Source and Scope Review

Reviewer: `Faraday`, xhigh effort.  Result: PASS.

The slice is local and conditional.  It defines

```text
baseJ := passiveSource.withDensity jacobianDensity
sourceMeasure := baseJ.withDensity sourceDensity
```

and concludes residual-source hypotheses or a p.13 finite integral only after
the caller supplies a finite a.e. bound for `sourceDensity` on
`baseJ.restrict W`.

The reviewer found that the pen-and-paper reproduction matches the Lean proof:
the `restrict_withDensity`, `withDensity_const`, and `withDensity_mono`
calculation in the reproduction is exactly the domination calculation used in
Lean.

The reviewer found no source-prior, determinant-Haar, raw-Haar, exact
passive-sector transport, source-image equality, normal-crossing, pole-order,
or RLCT overclaim.  The phrase "no source-rank coverage" is read as no global
source-image/source-rank coverage; the proof still uses the existing local
self-base containment lemma from the retained-passive local-source layer.

## Lean and API Review

Reviewer: `Planck`, xhigh effort.  Result: PASS.

The reviewer checked that the `withDensity` domination is the right local
statement:

```text
sourceDensity <= Csrc  baseJ.restrict W-a.e.
```

gives

```text
sourceMeasure.restrict W <= Csrc • baseJ.restrict W.
```

The finite-integral theorem composes the intended residual-source socket and
then the source-stratum consumer

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_bounds_locally_subset_localSource.
```

The reviewer found no unnecessary or conflicting measurable-space assumptions:
the `EdgeFamily` measurable-space assumptions remain locally quantified in the
existing socket style, and the theorem avoids adding stronger global
Borel/Polish assumptions on theta space.

## Controller Check

The landed public declarations are:

```text
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_withDensity_ae_le_const_globalWithDensity_jacobian_passiveProductMeasure_finiteMass

exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_withDensity_ae_le_const_globalWithDensity_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

The implementation removes the arbitrary-candidate local domination field for
the prior-shaped bounded-density case, but it does not construct an original
source prior or exact passive-sector Haar comparison.

## Nonclaims

This review accepts only bounded-density bookkeeping over the globally
Jacobian-weighted passive-product theta measure.  It does not assert
determinant-chart Haar transport, raw-order Haar transport, original DLN
source-prior identification, exact passive-sector pushforward, source-image
equality, global source-rank coverage, normal crossings, pole order, or RLCT
extraction.
