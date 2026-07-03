# A2 With-Following Readback Product Residual, Original Prior, Direct Endpoint Domination

Date: 2026-07-03.

## Lean artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean
```

Theorem:

```text
exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_endpointPatch_restrict_le_smul_endpointReferenceImage_priorDensity_upper
```

This is the direct-domination sibling of the unit source-image-density
readback product-residual wrapper.  It consumes the endpoint hypothesis

```text
rawHaar.restrict (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P)
  <= Cdet * endpointReferenceImage
```

instead of the stronger endpoint `withDensity formalProductAbsDet` identity
plus a determinant-density lower bound.

## Pen-and-paper calculation

The source finite-integral theorem gives an open `Vsource` around the base
point such that

```text
∫ productResidual(z)^(-t) d(coordinateSourceMeasure.restrict Vsource) < ∞.
```

On `Vsource`, the source chart has a left inverse:

```text
readback (sourceChart z) = z.
```

Therefore the square-sum identity converts the integrand:

```text
readbackProductResidual(sourceChart z) = productResidual(z).
```

The direct prior-domination package is called with `G := Vsource`.  It returns
a smaller open `V` for chart pieces and says that direct endpoint scalar
domination, the unit source-density lower bound, and a local prior-density
upper bound give

```text
Measure.map readback (originalPrior.restrict chartPiece)
  <= Cprior * baseJ.restrict Vsource,
Cprior < ∞.
```

Here `baseJ` appears because the source image density is identically `1`, so
`coordinateSourceMeasure = baseJ.withDensity (fun _ => 1)` simplifies to
`baseJ` in the direct prior package.

Finally, on `chartPiece ⊆ sourceChart '' V`, the right-inverse identity gives

```text
sourceChart (readback E) = E
```

for the prior-a.e. points of the chart piece.  The generic readback transfer
lemma with `β := PUnit` and `η := dirac PUnit.unit` transfers the finite source
integral to

```text
∫ readbackProductResidual(E)^(-t) d(originalPrior.restrict chartPiece) < ∞.
```

The product integral collapses by `lintegral_prod_dirac_right`.

## Why this route

Xhigh read-only audits found that the exact endpoint weighted-Haar identity is
not currently the smallest honest socket.  Existing infrastructure already has
active endpoint scalar domination:

```text
rawHaar.restrict endpointPatch
  <= C * endpointReferenceImage
```

provided the endpoint patch is contained in the active writeback image.  The
new theorem is shaped to consume exactly this weaker scalar domination.

The remaining honest frontier is therefore:

```text
rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P
  ⊆ activeWriteback '' activePatchImage
```

possibly after shrinking the local `V`.

## Audit conclusions

- Determinant-density lower bounds are local.  They come from positivity and
  continuity of `retainedPassiveFormalRawOrderJacobianProductAbsDetAt` around
  a determinant-chart point, not from a global arbitrary p.13 patch theorem.
- The readback residual measurability socket remains explicit.  The source
  chart package gives local continuity/a.e.-measurability after shrinking, but
  the current wrapper asks for global measurability of the pullback integrand.
- The active endpoint/Haar route is the best next target, but it still needs
  the p.13 endpoint patch to be related to the active writeback image.

## Verification

Passed:

```text
lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination
lake build DLNFibre
lean/scripts/sorries
git diff --check
rg -n "sorry|admit|axiom|#exit|native_decide|TODO|FIXME" lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean
```

Direct axiom probe for the theorem reports:

```text
[propext, Classical.choice, Quot.sound]
```

## Nonclaims

This theorem does not prove endpoint Haar transport, active-image containment,
determinant-density lower-bound shrinking, source-image coverage, source-rank
coverage, original-prior transport, normal crossings, pole order, or RLCT
extraction.
