# Review - A2 With-Following Endpoint-Patch Reference Domination

Date: 2026-07-07.

Reviewer: xhigh read-only reviewer `Darwin the 2nd`.

## Verdict

No issues found.

## Boundary Check

The theorem boundary is honest.  It proves only localized endpoint-patch
domination under the explicit hypothesis

```text
chartPiece ⊆ sourceChart '' (V ∩ sourceCylinder)
```

and does not claim determinant-chart Haar transport or exact raw-Haar
pushforward.

## Proof Shape

The proof matches the reproduction note.  Source-cylinder support gives
endpoint-patch containment, and the existing active selected-entry endpoint
Haar lemma supplies finite scalar domination.

## Source Fidelity

Aoyagi pp. 10-13 support the block-coordinate and p.13 chart algebra, not the
Haar measure transport.  The Lean docstring and reproduction note keep that
distinction visible.

## Usefulness

The theorem closes the direct endpoint-patch domination socket for
cylinder-supported chart pieces.  It does not by itself turn arbitrary

```text
chartPiece ⊆ sourceChart '' V
```

into source-cylinder support.

## Residual Risk

The remaining mathematical risk is upstream/downstream: proving the actual
endpoint patch satisfies the source-cylinder support condition, or shrinking
into it, without smuggling in a stronger coverage or Haar-transport claim.
