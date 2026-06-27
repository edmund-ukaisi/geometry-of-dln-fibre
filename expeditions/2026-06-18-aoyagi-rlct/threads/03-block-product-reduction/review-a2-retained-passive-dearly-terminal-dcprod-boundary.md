# Review - A2 retained-passive dEarly terminal dCprod boundary

Date: 2026-06-27.

Reviewer: xhigh `Copernicus`.

Verdict: PASS.

## Scope

Reviewed the terminal retained-passive `dEarly`/`dCprod` boundary slice in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

against the reproduction and statement card:

```text
reproduction-a2-retained-passive-dearly-terminal-dcprod-boundary.md
statement-card-a2-retained-passive-dearly-terminal-dcprod-boundary.md
```

Reviewed Lean names:

```text
fderiv_retainedPassive_C_residualFactorProduct_self_apply
fderiv_retainedPassiveLowerLeftProductTailSum_last_product_dCprod_dG_apply
```

## Findings

No blocking issue.

The empty stored-`C` suffix helper is narrow: it states only that the Frechet
derivative of `residualFactorProduct ... j j le_rfl` is zero, and proves this
by rewriting the function to a constant identity matrix before applying
`fderiv_const_apply`.

The terminal theorem correctly specializes the prior staged recurrence at
`q = Fin.last M`, with `p = q.castSucc` and `r = q.succ`.  The stored-`C`
source tangent is correctly `v.2.2.2.1 r`, not a tangent at `q.castSucc`; the
already staged `dG` term is `v.2.2.1 q`.

The noncommutative order is preserved:

```text
((0 * C_z r + Cnext(z) * v.C_r) * A3p(z) * Pcast(z)^-1),
Cprod(z) * dG * Pcast(z)^-1,
Cprod(z) * A3p(z) * Pcast(z)^-1 * dPcast_z(v) * Pcast(z)^-1.
```

The theorem collapses only `(fderiv Cnext z) v` and the successor-tail
derivative.  It leaves `Cnext(z)`, `Cprod(z)`, and `(fderiv Pcast z) v`
explicit.

The notes are aligned with this boundary: they defer the empty-product value
cleanup `Cnext(z) = 1`, the one-edge terminal `Cprod(z)` simplification, and
`dPcast` staging.  They do not claim determinant equality, measure transport,
normal crossings, pole order, RLCT, target staging, or a closed finite-sum
recurrence.

## Verification Notes

The reviewer did not run a build.  Controller verification ran the focused
`scripts/lb` module build, `scripts/sorries`, `git diff --check`, full
`DLNFibre` build, and theorem axiom audit successfully after the latest Lean
and documentation patches.  Both new theorem names have only the standard
`[propext, Classical.choice, Quot.sound]` footprint.
