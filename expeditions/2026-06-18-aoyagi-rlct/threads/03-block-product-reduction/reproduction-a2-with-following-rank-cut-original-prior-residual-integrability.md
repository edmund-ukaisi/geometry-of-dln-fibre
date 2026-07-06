# Reproduction - A2 with-following rank-cut original-prior residual integrability

Date: 2026-07-06.

Status: Lean target implemented as a local rank-cut residual-integrability
wrapper.

## Claim

The existing with-following original-prior residual-integrability patch can be
shrunk inside the local source-rank adapter.  On the resulting patch, the
source-rank stratum cuts the p.13/readback image exactly by the two theta-side
rank equations, and the fixed-base residual negative-power integrability
restricts to that rank-cut source piece.

This is only a local rank-cut adapter.  It does not prove rank-stratum
coverage, analytic atlas coverage, residual positivity, original `lossDLN`
comparison, normal crossings, pole order, or RLCT extraction.

## Calculation

The source-rank image theorem gives a theta neighborhood `Vrank` with

```text
sourceChart '' (Vrank cap rankEq)
  = (p13SourceSet cap readback^{-1}(Vrank)) cap sourceStratum
```

and, for `z in Vrank`,

```text
sourceChart z in sourceStratum <-> z in rankEq.
```

Here the theta-side rank locus is

```text
rankEq =
  { z |
      r + rank(z.followingFactor) = rEdge 0
      and
      r + rank(successorSelectedEntryMatrix(z.yNext)) = rEdge 1 }.
```

Now apply the original-prior residual-integrability theorem with the open set

```text
G cap Vrank.
```

The returned residual patch `V` satisfies `V subset Vrank` and

```text
sourceChart '' V = p13SourceSet cap readback^{-1}(V).
```

Restrict the rank equivalence from `Vrank` to `V`.  Then the rank-cut image
equality for the smaller residual patch follows by elementary set
bookkeeping:

```text
sourceChart '' (V cap rankEq)
  = (p13SourceSet cap readback^{-1}(V)) cap sourceStratum.
```

For the integral, let

```text
source  = p13SourceSet cap readback^{-1}(V),
source' = source cap sourceStratum.
```

Since `source' subset source`, monotonicity of measure restriction gives

```text
mu.restrict source' <= mu.restrict source.
```

The integrand in `residualNegPowerIntegrableOn` is nonnegative as an
`ENNReal`-valued function, so finite lower integral over `source` implies
finite lower integral over `source'`.

## Lean Target

Implemented in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalPriorResidualRankCutBridge.lean
```

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalPriorResidualRankCutBridge.lean
```

Theorem:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_residualNegPowerIntegrableOn_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_inter_sourceRankStratum_case2PassiveThetaWithFollowingFactor_of_continuousAt_priorDensity_of_subset_detSector
```

The theorem should return:

- open `V` with `z0 in V` and `V subset G`;
- the usual readback left inverse and source-chart regularity data;
- `sourceChart '' (V cap rankEq) =
  (p13SourceSet cap readback^{-1}(V)) cap sourceStratum`;
- `residualNegPowerIntegrableOn` for
  `(p13SourceSet cap readback^{-1}(V)) cap sourceStratum` and
  `originalEdgeFamilyPrior`.

The same file also adds the generic restriction lemma:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.residualNegPowerIntegrableOn_mono
```

## Checks

Verification passed: focused `lake env lean` for the new file, focused module
build, `lake env lean DLNFibre.lean`, full local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, marker scan for
`sorry`/`#exit`/`native_decide`/`axiom` in the new Lean file, and direct axiom
probes.  Both new declarations report only
`[propext, Classical.choice, Quot.sound]`.

## Nonclaims

- No residual positivity theorem.
- No original `lossDLN` finite-integral theorem.
- No adapted-product lower bound or density comparison for original loss.
- No source-rank coverage or analytic atlas coverage.
- No statistical-prior identification beyond the supplied
  `originalEdgeFamilyPrior`.
- No determinant/raw Haar transport or Jacobian normalization.
- No normal crossings, pole order, or RLCT extraction.
