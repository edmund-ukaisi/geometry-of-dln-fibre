# A2 With-Following Readback Product Residual, Original Prior, Active Endpoint Domination

Date: 2026-07-03.

## Target

Compose the existing active endpoint scalar-domination theorem with the direct
endpoint-domination original-prior finite-integral wrapper.

The active endpoint theorem gives, for an open source patch `Omega` in the
nonzero-pivot locus and an endpoint patch contained in the active writeback
image,

```text
rawHaar.restrict endpointPatch
  <= Cdet * endpointReferenceImage(Omega),
Cdet < infinity.
```

The direct finite-integral wrapper consumes exactly this scalar domination for

```text
endpointPatch =
  rawDetChart ∩ rawOrderOnEndpoint ⁻¹' (rawSourceSet ∩ rawChart ⁻¹' chartPiece).
```

## Pen-and-paper calculation

Let

```text
pivotSet = {z | case2PassiveThetaPivotNonzero z.1}.
```

The direct wrapper by itself returns an open set `V ⊆ G`.  The active endpoint
theorem needs the same `V` to lie in `pivotSet`.  Therefore call the direct
wrapper with

```text
G' = G ∩ pivotSet.
```

The base point lies in `G'` because it lies in `G` and satisfies the supplied
`hpivot0`.  The pivot set is open: it is the nonzero locus of the selected
coordinate `z.1.yNext pivotNext`, a continuous real-valued coordinate.

The direct wrapper then returns

```text
V open, z0 ∈ V, V ⊆ G ∩ pivotSet.
```

For a measurable chart piece with `chartPiece ⊆ sourceChart '' V`, define

```text
P = rawSourceSet ∩ rawChart ⁻¹' chartPiece,
endpointPatch = rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P.
```

Assume the remaining geometric containment

```text
endpointPatch ⊆ activeWriteback '' activePatchImage(V),
```

where

```text
activePatchImage(V) =
  activeChart '' (V ∩ {z | z.1.yNext ∈ signedBox Rres}).
```

Since `V ⊆ pivotSet`, the active endpoint theorem applies with `Omega := V`
and returns a finite scalar `Cdet` and the endpoint domination needed by the
direct wrapper.  The direct wrapper then gives

```text
∫ readbackProductResidual(E)^(-t)
    d(originalEdgeFamilyPrior(density).restrict chartPiece) < infinity
```

under the same explicit prior-density upper bound and readback residual
measurability hypotheses.

## Boundary

This composition removes the caller's need to supply an arbitrary scalar
`Cdet`, but it does not prove the geometric containment of the p.13 endpoint
patch in the active writeback image.  That containment is the next source-image
frontier.  The theorem also keeps the original prior-density upper bound and
readback residual pullback measurability hypotheses explicit.

## Verification

Passed:

```text
lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination
lake build DLNFibre
scripts/sorries
git diff --check
rg -n "sorry|admit|axiom|#exit|native_decide|TODO|FIXME" lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean
```

Direct axiom probe for the theorem reports:

```text
[propext, Classical.choice, Quot.sound]
```
