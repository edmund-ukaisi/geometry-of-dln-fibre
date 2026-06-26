# Reproduction - A2 retained-passive lower-left L recursion

Date: 2026-06-26.

Status: pen-and-paper follow-up to
`reproduction-a2-retained-passive-d-l-recurrence.md`.

## Setup

Continue with retained-passive fixed-base edges

```text
E_p = [I,F2_{p+1};0,I] *
      [A1_p, -A1_p F2_p; A3_p, C_p - A3_p F2_p],
```

and deterministic suffix states `S_p = suffixState E last p`.

The previous D/L reproduction checked the one-step formula

```text
L_p =
  [I,0; -(D_{p+1} * A3_p * (Ctop_{p+1} * A1_p)^-1), I] * L_{p+1}.
```

The generic product-reduction API proves that every suffix-state `L_p` is
lower unitriangular, so write

```text
L_{p+1} = [I,0; F3_{p+1}, I].
```

## Recurrence

Lower-unitriangular multiplication gives

```text
L_p =
  [I,0;
     -(D_{p+1} * A3_p * (Ctop_{p+1} * A1_p)^-1) + F3_{p+1},
   I].
```

Taking lower-left blocks:

```text
lowerLeft(L_p)
  = -(D_{p+1} * A3_p * (Ctop_{p+1} * A1_p)^-1)
      + lowerLeft(L_{p+1}).
```

The retained-passive Ctop recurrence is

```text
Ctop_p = Ctop_{p+1} * A1_p.
```

Therefore the source-facing recurrence is

```text
lowerLeft(L_p)
  = -(D_{p+1} * A3_p * Ctop_p^-1) + lowerLeft(L_{p+1}).
```

This is the recursive lower-left formula behind

```text
F3_p = F3_{p+1} - D_{p+1} * A3_p * Ctop_p^-1.
```

## Lean Scope

The Lean theorem should state the one-edge suffix-state recurrence, not yet the
iterated finite sum:

```text
suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_castSucc
suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_castSucc_currentCtop
```

The second theorem is the preferred source-facing form because it uses the
current suffix-state `Ctop_p`.

## Nonclaims

This does not prove the iterated sum for `F3_0`, does not solve for
`A3_last`, and does not construct the retained-passive coordinate domain,
source-rank coverage, source/image equality, source-measure pushforward,
Jacobian/prior density theorem, normal crossings, pole order, or RLCT.
