# A2 endpoint-patch null-measurability

Status: reproduced, ready for Lean.

## Claim

Let `S` be the retained-passive tuple determinant chart, let
`T` be the raw-order source-recursive determinant chart, and let

```text
Phi y = topologyTupleEdgeRawOrder y
rawChart y = paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart y.
```

For any measurable p.13 chart piece `C`, put

```text
P = T ∩ rawChart ⁻¹' C.
```

Then

```text
P ⊆ T
S ∩ Phi ⁻¹' P
```

is null-measurable for any measure on the endpoint tuple space, hence in
particular for any tuple Haar measure.

## Calculation

The inclusion `P ⊆ T` is immediate from the definition.

The map `Phi` is continuous on the determinant-chart subtype `S`; hence it is
a.e.-measurable for the restricted measure `m|S`.  Moreover the raw-order
coordinate theorem gives

```text
Phi(S) ⊆ T.
```

Therefore `Measure.map Phi (m|S)` is supported on `T`, and restricting this
image measure to `T` changes nothing.

The public p.13 raw-order source chart is already proved a.e.-measurable on
`T`, for any ambient measure.  Apply that theorem to

```text
Measure.map Phi (m|S).
```

Since the image measure is supported on `T`, this gives a.e.-measurability of
`rawChart` for `Measure.map Phi (m|S)`.  Composing with the a.e.-measurable
`Phi` gives a.e.-measurability of

```text
y ↦ rawChart (Phi y)
```

for `m|S`.  Hence the preimage of any measurable chart piece `C` is
null-measurable for `m|S`.

Finally, on `S` we have `Phi y ∈ T`, so

```text
S ∩ Phi ⁻¹' (T ∩ rawChart ⁻¹' C)
  = S ∩ (rawChart ∘ Phi) ⁻¹' C.
```

The `nullMeasurableSet_restrict` bridge turns null-measurability for `m|S`
into null-measurability of the intersection with `S` for `m`.

## Boundary

This proves only the set-measurability part of the localized endpoint-patch
socket.  It does not prove the scalar domination

```text
m|(S ∩ Phi ⁻¹' P) ≤ C • Measure.map Y(referenceSource|V),
```

nor any endpoint Haar transport, raw-Haar normalization, source coverage,
normal-crossing extraction, pole order, or RLCT statement.
