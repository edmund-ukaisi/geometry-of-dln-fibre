# Statement Card - A2 retained-passive dEarly dG source staging

Status: reproduced by controller; Lean proved; focused build passed; xhigh
math and Lean-terrain scout checks passed; `scripts/sorries`,
`git diff --check`, full `DLNFibre` build, and theorem axiom audit passed.

## Claim

For the lower-left factor

```text
G_p(y) =
  retainedPassiveA3WithoutLast(data_y.A3seed)(p)
```

in the retained-passive `dEarly` product-rule recurrence, the derivative is
source-staged in the two endpoint cases:

```text
dG_{q.castSucc,z}(v) = v.2.2.1 q       for q : Fin M,
dG_{Fin.last M,z}(v) = 0.
```

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

Lean names:

```text
fderiv_retainedPassiveA3WithoutLast_castSucc_apply
fderiv_retainedPassiveA3WithoutLast_last_apply
```

## Dependencies

- `retainedPassiveA3WithoutLast`;
- `ofTopologyTuple`;
- `A3seed_castSucc` and `A3seed_last` via simplification;
- linear coordinate projection `fderiv`;
- `fderiv_const_apply`.

## Review

Xhigh scouts `Halley` and `Nietzsche` passed the math and Lean-terrain checks.
Full verification passed: zero forbidden Lean placeholders by `scripts/sorries`,
clean `git diff --check`, successful full `DLNFibre` build, and only the
standard `[propext, Classical.choice, Quot.sound]` axiom footprint for both
new theorem names.

## Cited

None.

## Deferred

Substituting the staged `dG` into the product-rule recurrence; target staging
for `dD` and `dP`; iteration of the recurrence into a closed `dEarly`
expression; positive-tail `F3` target staging; determinant theorem; measure
theorem; normal crossings; pole order; RLCT.

## Kill Conditions

- The terminal zero theorem is for `retainedPassiveA3WithoutLast`, not solved
  terminal `A3`.
- The nonterminal theorem must return the passive source tangent `v.2.2.1 q`.
- The theorem must not claim target staging, determinant equality, measure
  transport, normal crossings, pole order, or RLCT.
