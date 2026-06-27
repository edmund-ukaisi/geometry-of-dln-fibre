# Reproduction - A2 retained-passive target-staged `C` suffix derivative

Date: 2026-06-27.

Status: controller pen-and-paper reproduction for the next narrow Lean rung.

This note is independent of the quiver-based paper.  It records the elementary
product-rule calculation needed to remove the remaining explicit `dCnext` input
from the target-only one-step lower-left core.

## Setup

For a retained-passive raw tuple

```text
z, w : RetainedPassiveRawTopologyTuple (M := M) rho kappa' R,
kappa' : Fin (M+2) -> Type,
```

write

```text
j = Fin.last (M+1).
```

For `m <= M+1`, the stored `C` suffix product is

```text
S_m(y) =
  residualFactorProduct C_y j <m> .
```

The endpoint `m = M+1` is the empty product:

```text
S_{M+1}(y) = 1,
dS_{M+1} = 0.
```

For a nonterminal index `m < M+1`, set

```text
a : Fin (M+1) := <m, m < M+1>.
```

Then the residual product unfolds as

```text
S_m(y) = S_{m+1}(y) * C_y(a).
```

The noncommutative product rule gives

```text
dS_m =
  dS_{m+1} * C_z(a)
  + S_{m+1}(z) * dC_a.
```

No factors commute.

## Target-side replacement

The current `C` tangent is already target-recovered:

```text
dC_a(w) = retainedPassiveTargetRecoveredSourceCAt hz w a.
```

On an actual raw-order derivative target `w = D_z raw(v)`, this is the source
tangent `v.C(a)`.

Therefore define the target-staged derivative recursively by

```text
D#_{M+1}(w) = 0,
D#_m(w) =
  D#_{m+1}(w) * C_z(a)
  + S_{m+1}(z) * retainedPassiveTargetRecoveredSourceCAt hz w a.
```

The intended derivative bridge is

```text
d(S_m)_z(v) = D#_m(D_z raw(v)).
```

## `dCnext` specialization

The positive-tail lower-left one-step core has

```text
q : Fin (M+1),
p := q.castSucc : Fin ((M+1)+1),
r := q.succ     : Fin ((M+1)+1),
j := Fin.last ((M+1)+1),
Cnext(y) := residualFactorProduct C_y j r.succ r.succ.le_last.
```

Thus `dCnext` is the `C` suffix derivative at the vertex `r.succ`.
At the terminal active index `q = Fin.last M`, this is the empty suffix and
`dCnext = 0`; the term `Cnext * dC_r` remains present.

The target-only step-core wrapper should use

```text
retainedPassiveCnextTargetStagedFDerivAt hz w q
```

as the supplied `dCnext` input to the already-landed
`retainedPassiveLowerLeftTailTargetOnlyStepCoreAt`.

## Lean target

The intended Lean layer is:

```text
retainedPassiveCTailTargetOnlyStepAt
retainedPassiveCTailTargetOnlyStepAt_fderiv_eq_sourceStep
retainedPassiveCSuffixTargetStagedFDerivAt
retainedPassiveCSuffixTargetStagedFDerivAt_self
retainedPassiveCSuffixTargetStagedFDerivAt_step
retainedPassiveCSuffixProductAt
fderiv_retainedPassive_C_residualFactorProduct_targetStaged_apply
retainedPassiveCnextTargetStagedFDerivAt
retainedPassiveCnextTargetStagedFDerivAt_fderiv_eq_source
retainedPassiveLowerLeftTailTargetOnlyStepCoreWithCnextAt
retainedPassiveLowerLeftTailTargetOnlyStepCoreWithCnextAt_fderiv_eq_sourceStepCore
```

The recursive unfold theorem is stated through the one-step helper.  This keeps
the product-rule API localized while the recursive object still removes the
entire `dCnext` suffix derivative as a target-side expression.

## Kill conditions

- Do not start `Cnext` at `r`; it starts at `r.succ`.
- Do not drop `Cnext * dC_r` in the terminal active step; only `dCnext`
  vanishes there.
- Do not commute the product-rule terms.
- Do not identify lower-left `A3` tangents with `C` tangents.
- Do not claim determinant-one normalization, determinant equality, measure
  transport, normal crossings, pole order, or RLCT from this rung.
