# Review - A2 p.13 Source-image Finite-integral Internal p.13 Support

Date: 2026-07-01.

Status: PASS; local controller checks passed.

## Scope

Review target: the concrete source-image reference and bounded-density
finite-integral wrappers in
`OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean`.

The change removes the final handler assumption
`chartPiece subset p13SourceSet` and derives it from the returned image support.

## Check

The required calculation is:

```text
chartPiece subset sourceChart '' V
forall E in sourceChart '' V, E in p13SourceSet
------------------------------------------------
chartPiece subset p13SourceSet.
```

In Lean the source-image reference wrapper now constructs `V` via
`exists_open_subset_measurableSet_case2PassiveThetaEndpointSourceChart_image_subset_p13SourceEdgeFamilySet`.
The final handler derives the old p.13 containment by unpacking the
`sourceChart '' V` witness and applying the returned pointwise support theorem.
The bounded-density wrapper consumes the strengthened source-image reference
wrapper, so it also drops the separate p.13 source-set assumption.

No volume domination, density identity, readback, or finite-integral argument
is changed.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean` passed.
- `lake build DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13ReadbackFiniteIntegral` passed.
- `lake env lean DLNFibre.lean` passed.
- Full local `lake build DLNFibre` passed.
- `lean/scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- `git diff --check` passed.
- Direct axiom probes for both strengthened wrappers reported only `[propext, Classical.choice, Quot.sound]`.

## Nonclaims

This is not source coverage, source-image equality, original-volume transport,
density identity or density bound, Haar or Jacobian transport, normal
crossings, pole order, or RLCT extraction.
