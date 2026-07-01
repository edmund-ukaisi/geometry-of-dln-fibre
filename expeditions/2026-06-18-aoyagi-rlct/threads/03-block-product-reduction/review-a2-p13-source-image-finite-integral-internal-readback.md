# Review - A2 p.13 Source-image Finite-integral Internal Readback

Date: 2026-07-01.

Status: PASS.

## Scope

Review target: the concrete source-image reference and bounded-density
finite-integral wrappers in
`OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean`.

The intended change is only to remove the final handler assumption that
`readback` is a right inverse on `chartPiece`, deriving it from containment in
the returned local image.

## Check

The required calculation is:

```text
chartPiece subset sourceChart '' V
forall E in sourceChart '' V,
  readback E in V and sourceChart (readback E) = E
V subset W
------------------------------------------------
forall E in chartPiece,
  readback E in W and sourceChart (readback E) = E.
```

This is a subset composition.  It does not change any volume domination,
density identity, source-reference, or finite-integral argument.

## Verification

Passed after Lean implementation:

- focused file elaboration:
  `lake env lean DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean`;
- focused module build:
  `lake build DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13ReadbackFiniteIntegral`;
- aggregate elaboration: `lake env lean DLNFibre.lean`;
- full local build: `lake build DLNFibre`;
- `lean/scripts/sorries`;
- `git diff --check`;
- direct axiom probe for both strengthened wrapper names.

The direct axiom probe reports only:

```text
[propext, Classical.choice, Quot.sound]
```

## Nonclaims

This is not source coverage, source-image equality, original-volume transport,
density identity or density bound, Haar or Jacobian transport, normal
crossings, pole order, or RLCT extraction.
