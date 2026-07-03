# A2 with-following source-cylinder C-one support bridge

## Claim

For the source-cylinder-supported scalar-domination route, the hypothesis

```text
chartPiece ⊆ sourceChart '' (V ∩ sourceCylinder)
```

can be produced from two more natural chart-piece hypotheses:

```text
chartPiece ⊆ sourceChart '' V
∀ E ∈ chartPiece, cOneReadout(E) ∈ signedBox.
```

Here `cOneReadout` is the enlarged with-following endpoint readout that reads
the selected successor residual block `C 1` back into the center coordinates,
and `sourceCylinder = {z | z.1.yNext ∈ signedBox}`.

## Pen-and-paper check

The local source chart already supplies a left inverse:

```text
readback(sourceChart z) = z,    z ∈ V.
```

In the definition of the enlarged with-following readback, the `yNext` field
is exactly `cOneReadout(E)`.  Projecting the displayed equality to the
`yNext` field therefore gives

```text
cOneReadout(sourceChart z) = z.1.yNext,    z ∈ V.
```

Now take `E ∈ chartPiece`.  The image-support hypothesis gives

```text
E = sourceChart z,    z ∈ V.
```

The chart-piece readout support gives

```text
cOneReadout(E) ∈ signedBox.
```

Substituting `E = sourceChart z` and using the projected readback equality
gives

```text
z.1.yNext ∈ signedBox.
```

Hence `z ∈ sourceCylinder`, so `E = sourceChart z` with
`z ∈ V ∩ sourceCylinder`.  This proves the source-cylinder image support
needed by the existing active endpoint containment and finite-integral
wrapper.

## Boundary

This bridge does not prove that arbitrary p.13 source chart pieces satisfy the
C-one signed-box support.  It only converts that support into the exact
source-cylinder support already consumed downstream.
