# Review - A2 target-only lower-left step core

Date: 2026-06-27.

Reviewer: xhigh `Halley the 2nd`.

Verdict: PASS.

## Findings

No mathematical or formalisation inaccuracies were found in the reviewed diff.

The Lean statements match the narrow reproduced claim.  The target-only step
core keeps `dCnext`, `dAcur`, `dPsucc`, and `dNext` explicit, and only replaces
the current source `C` tangent by `retainedPassiveTargetRecoveredSourceCAt hz w r`
and the passive lower-left tangent by `rawEdgeTupleA3 w q.castSucc`.

The noncommutative matrix order agrees with the existing source step core:

```text
-(((dCnext * C_r + Cnext * dC_r) * A3p * Pcast^-1)
- (Cprod * dG * Pcast^-1)
+ Cprod * A3p * Pcast^-1
    * (dPsucc * solvedA1(p) + Psucc * dAcur)
    * Pcast^-1
+ dNext.
```

The target replacements are sound on actual raw-order derivative targets:

- `retainedPassiveTargetRecoveredSourceCtopAt` is the recursive staged `Ctop`
  branch multiplied by the passive tail and recovers `v.Ctop`.
- `retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt` has the
  correct zero branch and successor branch; the successor branch uses
  `s.castSucc`.
- `retainedPassiveLowerLeftTailTargetOnlyStepCoreAt_fderiv_eq_sourceStepCore`
  rewrites recovered source `C`, and uses the existing raw-edge/formal-map fact
  plus the formal raw-order application formula to recover `v.A3free(q)`.

## Boundary

This checkpoint does not prove a full target-only lower-left recurrence, does
not target-stage `dCnext`, does not construct a determinant-one target
normalizer, and proves no determinant equality, source-prior transport, normal
crossings, pole order, or RLCT.
