# Review - A2 Case 2 Passive-theta Source-image p.13 Source-set Support

Date: 2026-07-01.

Status: PASS; local controller checks passed.

## Scope

Review target:

```text
exists_open_subset_measurableSet_case2PassiveThetaEndpointSourceChart_image_subset_p13SourceEdgeFamilySet
```

The theorem is a support theorem for the actual local image `sourceChart '' V`.
It uses only the determinant-chart membership already returned by the local
inverse theorem and the existing p.13 source-chart membership lemma.

## Check

The mathematical direction is one-way:

```text
theta in V
detChart (retainedData theta)
--------------------------------
sourceChart theta in p13SourceSet
```

Then:

```text
E in sourceChart '' V
--------------------------------
E in p13SourceSet
```

by choosing `theta` with `E = sourceChart theta`.  This is weaker than coverage
or equality, and that weaker shape is the desired claim.

The Lean proof constructs the determinant-chart subtype from `hdetV`, applies
`paperEndpointFixedBaseRetainedPassiveP13SourceChart_mem_sourceEdgeFamilySet`,
and unfolds the endpoint source-chart definition only to identify it with the
subtyped p.13 source chart.  The image statement is obtained by unpacking image
membership.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean` passed.
- `lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage` passed.
- `lake env lean DLNFibre.lean` passed.
- Full local `lake build DLNFibre` passed.
- `lean/scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- `git diff --check` passed.
- Direct axiom probe reported only `[propext, Classical.choice, Quot.sound]`.

## Nonclaims

The theorem is not source coverage, source-image equality, source-rank
coverage, original-prior transport, Haar or Jacobian transport, normal
crossings, pole order, or RLCT extraction.
