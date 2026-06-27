# Reproduction - A2 retained-passive dEarly dG source staging

Date: 2026-06-27.

Status: controller pen-and-paper reproduction; Lean proved; focused build
passed; xhigh math and Lean-terrain scout checks passed; `scripts/sorries`,
`git diff --check`, full `DLNFibre` build, and theorem axiom audit passed.

This note is independent of the quiver-based paper.  It isolates only the
`dG_p` factor in the retained-passive `dEarly` product-rule recurrence.

## Setup

In the product-rule recurrence, the lower-left factor is

```text
G_p(y) =
  retainedPassiveA3WithoutLast(data_y.A3seed)(p),
```

where `data_y = ofTopologyTuple(y)`.  The retained-passive nonredundant tuple
stores passive lower-left coordinates as

```text
y.2.2.1 : ∀ q : Fin M, Matrix (κ' q.castSucc.succ) ρ ℝ.
```

The redundant seed family is

```text
data_y.A3seed = Fin.snoc data_y.A3passive 0.
```

Thus

```text
data_y.A3seed(q.castSucc) = data_y.A3passive(q) = y.2.2.1(q),
data_y.A3seed(Fin.last M) = 0.
```

The early-tail family additionally applies `retainedPassiveA3WithoutLast`,
which is the identity away from `Fin.last M` and is zero at `Fin.last M`.

## Calculation

For `q : Fin M`, the edge `q.castSucc : Fin (M + 1)` is nonterminal.  Hence

```text
G_{q.castSucc}(y)
  = retainedPassiveA3WithoutLast(data_y.A3seed)(q.castSucc)
  = data_y.A3seed(q.castSucc)
  = y.2.2.1(q).
```

The map `y ↦ y.2.2.1(q)` is a linear coordinate projection, so at any `z` and
tangent `v`,

```text
dG_{q.castSucc,z}(v) = v.2.2.1(q).
```

For the terminal edge,

```text
G_{Fin.last M}(y)
  = retainedPassiveA3WithoutLast(data_y.A3seed)(Fin.last M)
  = 0,
```

so

```text
dG_{Fin.last M,z}(v) = 0.
```

This is source staging for the zeroed retained-passive `G_p` only.  It is not
the derivative of the solved terminal lower-left block.

## Lean Scope

Lean proves:

```text
fderiv_retainedPassiveA3WithoutLast_castSucc_apply
fderiv_retainedPassiveA3WithoutLast_last_apply
```

in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

The first theorem identifies the nonterminal derivative with the passive source
tangent `v.2.2.1 q`.  The second identifies the terminal derivative with zero.

## Independent Checks

Xhigh math scout `Halley` passed the two cases and confirmed that the terminal
case is the zeroed retained-passive branch, not solved terminal `A3`/`F3`.

Xhigh Lean-terrain scout `Nietzsche` confirmed the proof route using
`retainedPassiveA3WithoutLast`, `ofTopologyTuple`, the projection-linear-map
pattern, and `fderiv_const_apply`.

Full verification passed after review: `scripts/sorries` reported zero
`sorry`, `#exit`, `native_decide`, and `axiom`; `git diff --check` was clean;
the full `DLNFibre` build succeeded; and the theorem axiom audit reported only
the standard `[propext, Classical.choice, Quot.sound]` footprint for both new
theorems.

## Kill Conditions

- If the terminal theorem is read as the derivative of solved terminal `A3` or
  `F3`, it is wrong.
- If the nonterminal derivative is assigned to a different source coordinate
  than `v.2.2.1 q`, it is wrong.
- If this is advertised as target staging for `dG`, `dD`, or `dP`, it
  overclaims.
- If this is advertised as determinant equality, measure transport, normal
  crossings, pole order, or RLCT, it overclaims.

## Nonclaims

No target staging, no `dD` or `dP` staging, no full positive-tail `F3` target
staging, no determinant theorem, no measure transport, no normal crossings, no
pole order, and no RLCT follows from this source-staging slice.
