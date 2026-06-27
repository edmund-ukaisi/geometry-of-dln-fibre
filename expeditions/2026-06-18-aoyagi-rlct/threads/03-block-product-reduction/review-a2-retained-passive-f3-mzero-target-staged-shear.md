# Review - A2 retained-passive F3 zero-tail target-staged shear

Date: 2026-06-27.

Reviewer: xhigh `Bernoulli`.

Verdict: PASS.

## Scope

Reviewed the new Lean theorems in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

with the reproduction and statement card:

```text
reproduction-a2-retained-passive-f3-mzero-target-staged-shear.md
statement-card-a2-retained-passive-f3-mzero-target-staged-shear.md
```

## Findings

No blocking issue.

The Lean statements are restricted to `M = 0`.  The advertised staged
expression uses `retainedPassiveTargetRecoveredSuccessorF2At z Dzv` and has no
source-staged tangents on the left-hand side.  The terminal raw lower-left
target readout appears only in

```text
coord.F2 (0 : Fin 1).succ * rawEdgeTupleA3(Dzv,0),
```

so the proof does not assert that the terminal raw lower-left target
derivative is zero.

The `F3` product-rule order is preserved as

```text
Dzv.F3 + coord.F3 * targetCtop.
```

The recovery theorem right-multiplies by `(-(coord.Ctop))^{-1}`, not by the
passive Ctop tail.  The proof zeroes only the one-edge `Early` source tail and
does not claim determinant equality, measure transport, normal crossings,
pole order, or RLCT.

## Cleanup applied

The card status was updated after the focused build and checker pass, and the
reproduction now clarifies that the zeroed lower-left family is the source
family entering `Early`, not `rawEdgeTupleA3`.
