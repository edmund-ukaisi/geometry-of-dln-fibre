# Review: A2 retained-passive target edge-pair raw-tuple linear inverse

Reviewer: xhigh `Mendel the 2nd`.

## Verdict

PASS for the pen-and-paper inverse algebra and no-overclaim boundary.

The inverse algebra is correct for arbitrary raw tuples when the formal
edge-pair inverse is used only to extract the first component

```text
X := ((retainedPassiveFormalRawF2CLinearEquivAt hz).symm (U_F,U_C)).1.
```

The formal inverse's second component must not be treated as the recovered raw
`C` component for arbitrary target tuples.  The full raw-tuple inverse works
because it fixes side fields and explicitly cancels the side contributions:

```text
C(q)  := U_C(q) - rawA3(y,q) * H(q),
F2(q) := U_F(q) - rawA1(y,q) * H(q) + Xsucc(q) * coord.C(q).
```

The statement card correctly avoids a determinant-one claim.  The determinant
of the formal edge-pair equivalence is nontrivial, so determinant-one for the
target raw-tuple shear requires a separate unitriangular factorization or
direct determinant proof.

## Corrections Applied

- Renamed the schematic raw field `F` to `F2`.
- Clarified that only the formal inverse's first component is used as `X`.
- Added `A3passive` to the nonclaims list.

## Nonclaim

Do not state

```text
(retainedPassiveFormalRawF2CLinearEquivAt hz).symm
  (retainedPassiveTargetEdgePairShearAt z w) = (w.F2, w.C)
```

for arbitrary `w`.  The Lean checkpoint proves only the first-component
recovery needed by the raw-tuple inverse direction.
