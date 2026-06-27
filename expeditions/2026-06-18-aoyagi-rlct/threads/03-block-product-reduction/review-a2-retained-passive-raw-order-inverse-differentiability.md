# Review - A2 Retained-Passive Raw-Order Inverse Differentiability

Date: 2026-06-26.

Reviewer: Nash the 4th, xhigh read-only explorer.

## Verdict

Pass, with one low dependency-hygiene caveat.

## Finding

Low dependency hygiene: `RetainedPassiveCoordinatesDerivative.lean` imports
`ProductReductionStepDerivative`, which also contains one-step derivative and
formal-Jacobian material.  The reviewed proof uses the generic matrix inverse
differentiability and matrix-multiplication helpers from that import, not any
Jacobian determinant result.  This is not a mathematical overclaim in the
final theorem.  If this dependency boundary becomes important, split those
generic helpers into a smaller calculus utility module.

## Checks

Nash checked that

```text
differentiableAt_topologyTupleEdgeRawOrderInverse_of_mem_rawOrderSourceRecursiveDetChartSet
```

states only differentiability of `topologyTupleEdgeRawOrderInverse` at a point
of `topologyTupleRawOrderSourceRecursiveDetChartSet`.

The recursive proof was checked against the source readback formulas.  The
`L` update uses the source-faithful inverse

```text
(S.Ctop * topLeftCorner M)^-1
```

and its determinant-unit provenance is the induction-carried unit for
`S.Ctop` multiplied by the source-recursive chart unit for `topLeftCorner M`,
using `Matrix.det_mul`.

The index choices were checked:

```text
A1passive p = topLeftCorner T_(p.succ)
A3passive p = lowerLeftBlock T_(p.castSucc)
Ctop = S_0.Ctop
F3 = lowerLeftBlock S_0.L.
```

The raw-order reconstruction endpoints were also checked: raw `A1` sends `0`
to `Ctop` and successors to `A1passive`; raw `A3` sends `castSucc` to
`A3passive` and the last index to `F3`.

## Nonclaims

The review found no derivative formula, tangent equivalence, determinant
unit/formula, Jacobian density, measure transport, normal-crossing,
pole-order, RLCT, or quiver-paper/result dependency introduced by the new
theorem.  The dependency caveat above is only about module granularity.
