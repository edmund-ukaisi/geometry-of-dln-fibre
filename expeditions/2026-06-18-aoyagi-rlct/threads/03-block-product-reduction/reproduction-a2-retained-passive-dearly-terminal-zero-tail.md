# Reproduction - A2 retained-passive dEarly terminal zero tail

Date: 2026-06-27.

Status: controller pen-and-paper reproduction; Lean proved; focused build
passed; xhigh review passed; full verification passed.

This note is independent of the quiver-based paper.  It records only the
terminal boundary case for the zeroed retained-passive lower-left product
tail.

## Setup

Let

```text
A1fun(y)(r) = solvedA1_r(y),
A3seed(y)  = data_y.A3seed,
A3fun(y)   = retainedPassiveA3WithoutLast(A3seed(y)),
Cfun(y)(r) = C_r(y).
```

The retained-passive lower-left tail is

```text
Tail_m(y) =
  retainedPassiveLowerLeftProductTailSum(A1fun y, A3fun y, Cfun y)(m).
```

At the final retained edge `m = M`, the algebraic tail formula has only the
final `A3` contribution.  But `A3fun(y)(Fin.last M) = 0` by construction.

## Calculation

The existing algebraic lemma says

```text
retainedPassiveLowerLeftProductTailSum
  A1 (retainedPassiveA3WithoutLast A3) C M (Nat.le_succ M) = 0.
```

Applying this pointwise to `A1fun(y)`, `A3seed(y)`, and `Cfun(y)` gives

```text
Tail_M(y) = 0
```

for every ambient tuple `y`.  Hence `Tail_M` is the constant zero map, so at
any basepoint `z` and tangent `v`,

```text
d(Tail_M)_z(v) = 0.
```

No determinant-chart hypothesis is needed: the proof never differentiates
matrix inversion or solved products.  It only differentiates a pointwise
constant zero map after the algebraic zero-tail rewrite.

## Lean Scope

Lean proves:

```text
fderiv_retainedPassiveLowerLeftProductTailSum_withoutLast_last_apply
```

in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

The theorem depends on the algebraic `[simp]` lemma
`retainedPassiveLowerLeftProductTailSum_withoutLast_last` and
`fderiv_const_apply`.

## Independent Review

Xhigh reviewer `Aquinas` passed the slice.  The review confirmed the terminal
zeroed-tail scope, the pointwise constant-zero proof route, the absence of a
determinant-chart hypothesis, and the fact that this is not a solved terminal
`A3` or `F3` derivative theorem.

## Verification

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative`, full `DLNFibre`
build, `scripts/sorries`, and `git diff --check` passed.  The theorem axiom
audit reports only `[propext, Classical.choice, Quot.sound]`.

## Kill Conditions

- If the theorem is read as a statement about solved terminal `A3` or `F3`, it
  is wrong.
- If a determinant-chart or invertibility hypothesis is introduced, the proof
  is no longer the intended elementary boundary case.
- If this is advertised as source staging for `dCprod` or `dPcast`, target
  staging, determinant equality, measure transport, normal crossings, pole
  order, or RLCT, it overclaims.

## Nonclaims

No `dCprod` staging, no `dPcast` staging, no target staging, no full
positive-tail `F3` target staging, no determinant theorem, no measure theorem,
no normal crossings, no pole order, and no RLCT follows from this terminal
zero-tail boundary slice.
