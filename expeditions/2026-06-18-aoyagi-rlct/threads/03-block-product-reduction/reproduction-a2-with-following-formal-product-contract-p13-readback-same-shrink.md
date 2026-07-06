# A2 With-following Formal-product Contract Same-shrink p.13/readback Support

## Source Calculation

For the with-following Case 2 endpoint source chart, the local source-image
equality has the form

```text
sourceChart '' W = p13SourceSet ∩ readback ⁻¹' W.
```

If we later shrink to `V ⊆ W`, the same equality remains true on `V`, provided
the readback is still a left inverse on `W`:

```text
sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V.
```

The forward direction is immediate: for `E = sourceChart theta` with
`theta ∈ V`, the point lies in the p.13 source set by the equality on `W`,
and `readback E = theta ∈ V` by the left inverse on `W`.

The reverse direction uses the equality on `W`: if `E ∈ p13SourceSet` and
`readback E ∈ V`, then `readback E ∈ W`, so `E ∈ sourceChart '' W`.  Write
`E = sourceChart theta` with `theta ∈ W`; the left inverse on `W` gives
`readback E = theta`, hence `theta = readback E ∈ V`, and therefore
`E ∈ sourceChart '' V`.

This is the set-theoretic guardrail needed when one local package first
chooses a with-following p.13 image-equality shrink and another package then
shrinks further for the raw-map formal-product/source-reference contract.

## Lean Targets

The generic shrink-stability lemma is:

```text
sourceChart_image_eq_p13_readback_preimage_of_subset
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

The concrete same-shrink contract wrapper is:

```text
exists_open_subset_a2FormalProductSourceImagePieceContract_case2PassiveThetaWithFollowingFactorEndpointSourceChart_of_rawMap_eq_restrict_rawSource_chartPiece_subset_p13_readback
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaFormalProductSourceImageContract.lean
```

It returns a single `V` carrying both:

```text
sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V
```

and the raw-pushforward-to-contract continuation.  Thus callers may provide:

```text
chartPiece subset p13SourceSet
chartPiece subset readback ⁻¹' V
```

instead of separately proving:

```text
chartPiece subset sourceChart '' V.
```

## Boundary

This is same-shrink support bookkeeping and contract packaging.  The raw
pushforward identity remains an explicit hypothesis.  The theorem does not
prove raw Haar transport, a raw-map Jacobian formula, determinant/raw Haar
transport, source/product-coordinate prior transport, local product-coordinate
readback domination, normal crossings, pole order, or RLCT extraction.

The xhigh measure audit for this checkpoint also ruled out targeting a full
raw-Haar pushforward from the p.13 raw section: that section fixes variables
such as `C1 = I` and `A3 = 0`, while the raw determinant chart contains open
sets with those variables free.  The real next measure target is local
readback domination for the actual product-coordinate chart carrying the
prior density `phi(CedgeProd(x,u))`.

## Kill Conditions

- Kill any use that treats the theorem as proving the raw pushforward identity.
- Kill any use that combines the image equality from one shrink with the
  contract from an unrelated shrink.
- Kill any use that reads the constant-density contract as original-prior
  transport or a product-coordinate change-of-variables theorem.
