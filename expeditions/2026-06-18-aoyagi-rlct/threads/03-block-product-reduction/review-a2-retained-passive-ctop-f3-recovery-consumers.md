# Review - A2 Retained-Passive Ctop and F3 Recovery Consumers

Date: 2026-06-27.

Reviewer: xhigh read-only implementation reviewer `Turing`.

Hardener: xhigh read-only hardener `Hubble`.

## Verdict

PASS after documentation repair.  Focused
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` build, full
`DLNFibre` build, `scripts/sorries`, `git diff --check`, and theorem axiom
audit all passed.

## Finding Addressed

The initial statement card did not state the main Lean hypothesis:

```text
hz : z in topologyTupleDetChartSet.
```

The Lean theorems expose this hypothesis directly.  It is needed by the formal
recovery theorems, because those recoveries use determinant-unitness of the
passive top-left tail for `Ctop` and determinant-unitness of the terminal
solved top-left factor for `F3`.

The reproduction and statement card now state the determinant-chart assumption
on the claim surface.

## Implementation Fidelity

No Lean fidelity issue was found.

For `Ctop`, the theorem multiplies the staged expression on the left by
`Tail`.  In the positive-tail case, the first passive recurrence substitution
keeps the correction

```text
+ Tail^{-1}
    * ((fderiv Psucc z) v * data.A1seed p + Psucc z * v.1 q)
    * Tail^{-1}
    * coord.Ctop
```

with the positive sign and the noncommutative order unchanged.

For `F3`, the theorem uses

```text
Dzv.F3 - (d Early)_z(v) * Last + (coord.F3 - Early z) * (d Last)_z(v)
```

and right-multiplies by

```text
(-(coord.solvedA1 (Fin.last M)))^{-1}.
```

This is the terminal solved top-left block.  For `M=0`, it is `coord.Ctop`;
it is not the passive first-edge tail.

## Nonclaim Boundary

This slice is a recovery consumer.  It does not prove a closed finite-sum
formula for `dTail`, a derivative formula for the lower-left early tail, a
fully source-staged tuple theorem, a target-side determinant-one linear
equivalence, actual determinant equality, measure transport, normal crossings,
pole order, or RLCT.

The hardener pass independently checked that the theorem names and statements
are scoped as recovery consumers, that the determinant-chart hypothesis is
surfaced in the Lean statements and docs, that the nonclaim boundary is clear,
and that this slice does not use quiver references.
