# Reproduction - A2 with-following rank-cut original-prior residual source hypotheses

Date: 2026-07-06.

Status: Lean target implemented as a conditional wrapper over the rank-cut
residual integrability theorem.

## Claim

On the rank-cut p.13/readback source patch returned by the with-following
original-prior residual-integrability theorem, residual zero-locus nullity for
the restricted original edge-family prior implies the residual-source
hypotheses needed by the local finite-integral sockets: a.e. positivity of the
fixed-base residual square-sum and finite residual negative-power
integrability.

This proves no zero-locus-nullity theorem.  The nullity of the residual zero
locus is an explicit hypothesis on exactly the rank-cut source set.

## Setup

The previous rank-cut theorem returns an open theta neighborhood `V` and the
rank-cut source set

```text
rankCutSource =
  (p13SourceSet cap readback^{-1}(V)) cap sourceStratum.
```

For the original edge-family prior

```text
muPrior =
  originalEdgeFamilyPrior
    (paperEndpointFixedBaseFinBasis W2 B2 U0 hU0)
    density,
```

it proves

```text
residualNegPowerIntegrableOn
  (fun E => E) rankCutSource muPrior t.
```

The additional hypothesis for this reproduction is

```text
(muPrior.restrict rankCutSource)
  { E |
    aoyagiCoordinateSquareSum
      (paperEndpointFixedBaseResidualBlockCoordinateMap
        W2 B2 U0 hU0 (fun E => E) E) = 0 } = 0.
```

## Calculation

For every edge family `E`, the coordinate square-sum is nonnegative:

```text
0 <= aoyagiCoordinateSquareSum
  (paperEndpointFixedBaseResidualBlockCoordinateMap
    W2 B2 U0 hU0 (fun E => E) E).
```

Therefore the complement of the positive set is contained in the zero set:

```text
not (0 < residualSq E)  implies  residualSq E = 0.
```

If the zero set has `muPrior.restrict rankCutSource` measure zero, the
nonpositive set also has zero measure, hence

```text
forall ae E with respect to muPrior.restrict rankCutSource,
  0 < residualSq E.
```

The finite negative-power integral over `rankCutSource` is already the output
of the previous rank-cut theorem.  Combining these two facts gives exactly

```text
(forall ae E with respect to muPrior.restrict rankCutSource,
    0 < residualSq E)
and
residualNegPowerIntegrableOn
  (fun E => E) rankCutSource muPrior t.
```

In Lean this is the existing generic helper

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_mono_of_zero_set_null
```

with `source = source' = rankCutSource` and `Subset.rfl`.

## Lean Target

Implemented in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalPriorResidualRankCutBridge.lean
```

Theorem:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_inter_sourceRankStratum_case2PassiveThetaWithFollowingFactor_of_zero_set_null_of_continuousAt_priorDensity_of_subset_detSector
```

The theorem should return the same `V` data as the existing rank-cut theorem:

- open `V`, `z0 in V`, and `V subset G`;
- readback left inverse, source-chart injectivity, continuity, and source
  image data;
- measurability and openness of `p13SourceSet cap readback^{-1}(V)`;
- measurability of the rank-cut source patch;
- the theta-side rank-equation equivalence and rank-cut image equality;
- for every supplied raw Haar measure, the explicit zero-locus-nullity
  hypothesis implies residual a.e. positivity and
  `residualNegPowerIntegrableOn` on the rank-cut source patch.

## Kill Conditions

- The theorem is read as proving the residual zero-locus is null.
- The zero-locus-nullity hypothesis is moved to the uncut p.13 source, to the
  ambient source-rank stratum, or to a theta-volume measure instead of
  `muPrior.restrict rankCutSource`.
- The theorem is read as proving original `lossDLN` finite integrability,
  adapted-product lower bounds, density comparison, source-rank coverage,
  analytic atlas coverage, normal crossings, pole order, or RLCT.

## Nonclaims

- No residual zero-locus-nullity proof.
- No original `lossDLN` finite-integral theorem.
- No adapted-product lower bound or density comparison for original loss.
- No source-rank coverage or analytic atlas coverage.
- No statistical-prior identification beyond the supplied
  `originalEdgeFamilyPrior`.
- No determinant/raw Haar transport or Jacobian normalization.
- No normal crossings, pole order, or RLCT extraction.

## Checks

Verification passed: focused `lake env lean`, focused module build,
`lake env lean DLNFibre.lean`, full local `lake build DLNFibre`,
`scripts/sorries`, `git diff --check`, marker scan for
`sorry`/`#exit`/`native_decide`/`axiom` in the touched Lean file, and direct
axiom probe.  The new theorem reports only
`[propext, Classical.choice, Quot.sound]`.  Xhigh read-only reviewer `Ampere`
passed the statement/proof-fidelity audit.
