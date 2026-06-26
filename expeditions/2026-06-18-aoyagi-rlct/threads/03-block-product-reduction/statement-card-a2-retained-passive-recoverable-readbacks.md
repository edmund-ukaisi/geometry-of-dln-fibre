# Statement Card - A2 retained-passive recoverable readbacks

## Lean File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveCoordinateData.edgeMatrix_recoverableReadbacks_eq_targets
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveCoordinateData.edgeMatrix_recoverable_ext
```

## Reproduction

```text
reproduction-a2-retained-passive-recoverable-readbacks.md
```

## Claim

For bundled retained-passive coordinate data, Lean now proves the finite
readback theorem for exactly the recoverable coordinate fields.  Under

```text
F2_last = 0,
det(A1seed_p) is a unit for p != 0,
det(Ctop) is a unit,
```

the edge family `data.edgeMatrix` recovers:

```text
F2_0, Ctop, F3
```

from the source-left suffix state, and for every edge recovers:

```text
A1seed_p for p != 0,
F2_{p.castSucc},
A3seed_p for p != last edge,
C_p.
```

The terminal value `F2_last` is determined in the extensionality theorem from
the side condition `F2_last=0`, not from a transformed-edge readback.

Lean also proves a sharp finite extensionality theorem: if two data objects
satisfy the side conditions and have the same `edgeMatrix`, then their
recoverable fields agree:

```text
A1seed_p = A1seed'_p for p != 0,
F2 = F2',
A3seed_p = A3seed'_p for p != last edge,
C = C',
Ctop = Ctop',
F3 = F3'.
```

## Method

The readback theorem calls
`RetainedPassiveCoordinateData.edgeMatrix_readbacks_eq_targets`, then rewrites
the solved endpoint families back to seed fields away from the dummy endpoints
using:

```text
retainedPassiveSolvedA1_eq_of_ne_zero
retainedPassiveSolvedA3_eq_of_ne_last
```

The extensionality theorem applies the same readback theorem to both data
objects after rewriting the second edge family by the equality hypothesis.  It
splits `F2` into non-final `castSucc` coordinates plus the final coordinate
with `Fin.forall_iff_castSucc`.

## Role

This is the finite local-inverse layer for the retained-passive source map, at
the level where such an inverse is true.  It is intentionally weaker than full
record injectivity because two seed entries are placeholders.

## Nonclaims

No full equality `data = data'` is claimed.  The fields `A1seed 0` and
`A3seed (Fin.last M)` are dummy seed fields and are not recoverable from
`edgeMatrix`.

No open coordinate domain, topology, measure, Jacobian, source-rank coverage,
source/image equality, normal crossings, pole order, or RLCT extraction is
proved.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
```

This focused check passed on 2026-06-26.

Full check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
```

also passed on 2026-06-26, with pre-existing warnings outside the touched
module.  `scripts/sorries` and `git diff --check` also passed.

Review:

```text
threads/03-block-product-reduction/review-a2-retained-passive-recoverable-readbacks.md
```

passed.
