# Review - A2 local source regular-coordinate ideal split

Date: 2026-06-24.

Reviewers: controller self-check and xhigh `Feynman the 3rd`.

## Verdict

Passed.

The theorem only repackages the existing local source-neighborhood certificate
through already-proved algebraic ideal equalities.  The conclusion remains
guarded by membership in `paperEndpointFixedBaseSourceRankStratum`.

The canonical signs are preserved:

```text
F2 = -S.B,
F3 = lowerLeftBlock S.L.
```

The residual block `S.D` remains outside the scalar regular-coordinate ideal.

Feynman's xhigh review found no issues.  The review confirmed that the theorem
is a thin projection from `cert.exists_source_neighborhood`, preserves the
source-stratum guard, keeps the canonical signs `(S.Ctop - 1)`, `-S.B`,
`lowerLeftBlock S.L`, and leaves `S.D` residual.  It also checked Aoyagi PDF
p. 13 for the displayed sign convention.

## Build Check

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
LEAN_NUM_THREADS=1 lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
lake build DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
```

Focused controller checks passed; Feynman also reported the single-threaded
focused Lean check passed.
