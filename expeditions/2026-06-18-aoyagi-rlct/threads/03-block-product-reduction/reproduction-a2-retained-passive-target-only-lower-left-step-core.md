# Reproduction - A2 retained-passive target-only lower-left step core

Date: 2026-06-27.

Status: controller pen-and-paper reproduction for the next narrow Lean rung.

This note is independent of the quiver-based paper.  It records the target-side
one-step lower-left recurrence support needed before constructing the full
determinant-one target normalizer.

## Setup

Work in the positive-tail retained-passive shape

```text
z, w : RetainedPassiveRawTopologyTuple (M := M+1) rho kappa' R,
kappa' : Fin ((M+1)+2) -> Type.
```

The existing source-direction one-step recurrence is indexed by
`q : Fin (M+1)`.  Set

```text
p = q.castSucc : Fin ((M+1)+1),
r = q.succ     : Fin ((M+1)+1).
```

The already-proved one-step core has the order

```text
-(((d Cnext) * C_r + Cnext * dC_r) * A3p * Pcast^-1)
- (Cprod * dG * Pcast^-1)
+ Cprod * A3p * Pcast^-1
    * (dPsucc * solvedA1(p) + Psucc * dAcur)
    * Pcast^-1
+ dNext.
```

No factors commute.  The target-only one-step core keeps `dCnext`, `dAcur`,
`dPsucc`, and `dNext` explicit, and replaces only the source tangent reads
whose target-side versions are already available.

## Target replacements

The current source `C` tangent is recovered from the target tuple by the landed
edge-pair inverse:

```text
dC_r(w) = retainedPassiveTargetRecoveredSourceCAt hz w r.
```

On an actual derivative target `w = D_z raw(v)` this is `v.C(r)`.

The current lower-left free tangent is read directly from the raw lower-left
edge tuple:

```text
dG(w) = rawEdgeTupleA3(w, q.castSucc).
```

Since `q.castSucc` is never the terminal endpoint in this positive-tail step,
the actual derivative target gives

```text
rawEdgeTupleA3(D_z raw(v), q.castSucc) = v.A3free(q).
```

The current solved-`A1` tangent has two cases.  At `m=0`, first recover the
source `Ctop` tangent from the target-side recursive `Ctop` shear:

```text
R_Ctop(z,w) =
  Tail *
    (w.Ctop
      - XsuccF2(0) * coord.solvedA3(0)
      - coord.F2(1) * rawEdgeTupleA3(w,0)
      + Tail^-1 * dTail * Tail^-1 * coord.Ctop),
```

where

```text
dTail = retainedPassiveA1TailTargetStagedFDerivAt z w 0.
```

Then the zero current solved-`A1` target tangent is

```text
Tail^-1 * R_Ctop(z,w) - Tail^-1 * dTail * Tail^-1 * coord.Ctop.
```

On an actual derivative target, `R_Ctop(z,D_z raw(v)) = v.Ctop` and the landed
`A1`-tail derivative bridge gives `dTail = d(Tail)_z(v)`, hence this recovers
the source zero branch.

At a successor current index `m=s+1`, use the landed passive `A1` target
tangent:

```text
retainedPassiveTargetStagedA1passiveTangentAt z w s.castSucc.
```

On an actual derivative target this is `v.A1passive(s.castSucc)`, which is the
successor branch of the source recurrence.

## Narrow Lean target

The intended first Lean layer is:

```text
retainedPassiveTargetRecoveredSourceCtopAt
retainedPassiveTargetRecoveredSourceCtopAt_fderiv_eq_sourceCtop
retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt
retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt_zero
retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt_succ
retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt_fderiv_eq_source
retainedPassiveLowerLeftTailTargetOnlyStepCoreAt
retainedPassiveLowerLeftTailTargetOnlyStepCoreAt_fderiv_eq_sourceStepCore
```

The step-core theorem should pass in the actual `dCnext`, `dAcur`, `dPsucc`,
and `dNext` arguments and prove equality with the existing source step core
after substituting only `dC_r` and `dG`.

## Kill conditions

- Do not replace `dCnext` by a guessed target expression in this rung.
- Do not identify `dG` with the source `C` tangent.
- Do not use `v.1 q` in the successor solved-`A1` branch; the source tangent is
  at `s.castSucc`.
- Do not commute matrix factors or change the order of the positive term.
- Do not choose a base at `m = M+2`; the later recursive lower-left object
  should still end at the zeroed-final tail `m = M+1`.
- Do not claim determinant-one normalization, determinant equality, measure
  transport, normal crossings, pole order, or RLCT from this one-step helper.
