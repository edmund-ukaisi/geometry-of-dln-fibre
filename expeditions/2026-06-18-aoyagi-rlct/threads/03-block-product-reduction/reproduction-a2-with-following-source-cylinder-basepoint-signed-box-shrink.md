# A2 with-following source-cylinder basepoint signed-box shrink

## Claim

For the source-cylinder-supported scalar-domination route, if the basepoint
itself satisfies

```text
z0.1.yNext ∈ signedBoxSet Rres,
```

then the local source chart can be shrunk inside the source cylinder

```text
sourceCylinder = {z | z.1.yNext ∈ signedBoxSet Rres}.
```

After that shrink, an ordinary chart-piece support hypothesis

```text
chartPiece ⊆ sourceChart '' V
```

already implies the downstream source-cylinder support

```text
chartPiece ⊆ sourceChart '' (V ∩ sourceCylinder).
```

Thus the finite-integral wrapper no longer needs a separate pointwise
`cOneReadout` signed-box hypothesis in this local basepoint-in-box case.

## Pen-and-paper check

The selected-entry signed box is the finite product of open intervals:

```text
signedBoxSet Rres = ∏ i (-Rres i, Rres i).
```

Hence it is open in the finite product topology.  The coordinate projection

```text
z ↦ z.1.yNext
```

is continuous, so

```text
sourceCylinder = (z ↦ z.1.yNext)^{-1}(signedBoxSet Rres)
```

is open.  If `z0.1.yNext ∈ signedBoxSet Rres`, then `z0 ∈ sourceCylinder`.
Run the existing source-cylinder finite-integral theorem with the open
neighborhood

```text
G ∩ sourceCylinder.
```

The returned source chart neighborhood `V` satisfies

```text
V ⊆ G ∩ sourceCylinder,
```

so in particular `V ⊆ sourceCylinder`.  Therefore any chart piece with
`chartPiece ⊆ sourceChart '' V` is automatically supported in
`sourceChart '' (V ∩ sourceCylinder)`: if `E = sourceChart z` with `z ∈ V`,
then `z ∈ sourceCylinder`, so the same witness belongs to the intersection.

The proof then delegates to the already verified source-cylinder
continuous-at prior-density wrapper.

## Boundary

This does not prove that arbitrary p.13 source pieces are globally supported
in one signed box.  It is a local shrink theorem around a chosen basepoint
whose selected-entry `yNext` coordinate already lies in the signed box.
