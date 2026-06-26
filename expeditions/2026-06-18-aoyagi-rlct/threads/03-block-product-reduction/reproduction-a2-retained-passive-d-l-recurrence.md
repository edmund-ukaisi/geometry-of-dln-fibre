# Reproduction - A2 retained-passive D and L recurrences

Date: 2026-06-26.

Status: pen-and-paper prerequisite for the next finite Lean rung.

## Setup

Use the retained-passive transformed edge block

```text
M_p =
  [ A1_p       -A1_p * F2_p
    A3_p        C_p - A3_p * F2_p ].
```

The fixed-base edge is

```text
E_p = [I, F2_{p+1}; 0, I] * M_p,
```

and the deterministic suffix state before edge `p` is `S_{p+1}`.  The prior
retained-passive Lean rung proves that, if `B_{p+1} = -F2_{p+1}`, then the
transformed edge seen by the suffix recursion is exactly `M_p`.

The suffix-state step uses

```text
Ctop_p = Ctop_{p+1} * topLeft(M_p),
D_p    = D_{p+1} * schurResidual(M_p),
L_p    = [I,0; -D_{p+1} * lowerLeft(M_p)
                  * (Ctop_{p+1} * topLeft(M_p))^-1, I] * L_{p+1}.
```

For `M_p`, `topLeft(M_p)=A1_p` and `lowerLeft(M_p)=A3_p`.

## Schur Residual

Assume `det(A1_p)` is a unit.  The Schur residual of `M_p` is

```text
(C_p - A3_p * F2_p)
  - A3_p * A1_p^-1 * (-(A1_p * F2_p)).
```

Use associativity and `A1_p^-1 * A1_p = I`:

```text
A3_p * A1_p^-1 * (-(A1_p * F2_p))
  = -(A3_p * (A1_p^-1 * A1_p) * F2_p)
  = -(A3_p * F2_p).
```

Hence

```text
schurResidual(M_p)
  = C_p - A3_p * F2_p - (-(A3_p * F2_p))
  = C_p.
```

Therefore the retained-passive deterministic residual field satisfies the
one-step recurrence

```text
D_p = D_{p+1} * C_p.
```

By reverse induction from `D_N=I`, this should give

```text
D_i = C_{N-1} * ... * C_i
```

in the existing Lean notation:

```text
D_i = residualFactorProduct C last i.
```

## Lower-Unitriangular Contribution

The suffix-state left multiplier updates by

```text
L_p =
  [I,0; -D_{p+1} * A3_p * (Ctop_{p+1} * A1_p)^-1, I] * L_{p+1}.
```

The previous Ctop recurrence identifies

```text
Ctop_p = Ctop_{p+1} * A1_p.
```

So the update is equivalently

```text
L_p =
  [I,0; -D_{p+1} * A3_p * Ctop_p^-1, I] * L_{p+1}.
```

If

```text
L_{p+1} = [I,0; F3_{p+1}, I],
```

then lower-unitriangular multiplication gives

```text
L_p = [I,0; -D_{p+1} * A3_p * Ctop_p^-1 + F3_{p+1}, I].
```

Thus the lower-left field of `L` satisfies

```text
F3_p = F3_{p+1} - D_{p+1} * A3_p * Ctop_p^-1.
```

Iterating from `F3_N=0` gives the source-note formula

```text
F3_0 = - sum_p D_{p+1} * A3_p * Ctop_p^-1.
```

This is the finite recurrence needed before solving for the omitted
right-endpoint lower-left variable:

```text
A3_last =
  -(F3_0 + sum_{p<last} D_{p+1} * A3_p * Ctop_p^-1) * Ctop_last.
```

## Intended Lean Scope

The next Lean step should first prove the Schur residual and `D` recurrences
for the retained-passive fixed-base reconstruction:

```text
schurResidualBlock_retainedPassiveTransformedEdge
step_retainedPassiveFixedBaseEdgeMatrix_D
suffixState_D_retainedPassiveFixedBaseEdgeMatrix
```

The lower-unitriangular recurrence can then be stated as a separate theorem,
using the existing `step` definition and the already-proved `Ctop` recurrence.

## Nonclaims

This is finite suffix-state algebra only.  It does not construct the
retained-passive coordinate domain, does not solve `A3_last` yet, does not
prove source-rank coverage, source/image equality, source-measure pushforward,
Jacobian/prior density transport, normal crossings, pole order, or RLCT.
