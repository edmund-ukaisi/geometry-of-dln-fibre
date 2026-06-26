# Reproduction - A2 retained-passive lower-left L tail sum

Date: 2026-06-26.

Status: pen-and-paper follow-up to
`reproduction-a2-retained-passive-l-lowerleft-recursion.md`.

## Setup

Continue with retained-passive fixed-base edges

```text
E_p = [I,F2_{p+1};0,I] *
      [A1_p, -A1_p F2_p; A3_p, C_p - A3_p F2_p],
```

and deterministic suffix states `S_p = suffixState E last p`.

The previous rung proved the one-edge lower-left recurrence

```text
lowerLeft(S_p.L)
  = -(S_{p+1}.D * A3_p * S_p.Ctop^-1)
      + lowerLeft(S_{p+1}.L).
```

The terminal suffix state has `S_last.L=I`, hence
`lowerLeft(S_last.L)=0`.

## Iteration

Define the tail contribution recursively by

```text
Tail_last = 0,
Tail_p = -(S_{p+1}.D * A3_p * S_p.Ctop^-1) + Tail_{p+1}.
```

Reverse induction on the vertex index gives

```text
lowerLeft(S_i.L) = Tail_i.
```

At the source endpoint this is the finite iterated formula

```text
lowerLeft(S_0.L)
  = sum over p from 0 to last edge of
      -(S_{p+1}.D * A3_p * S_p.Ctop^-1).
```

The retained-passive residual and top-block product readbacks are

```text
S_i.D    = residualFactorProduct C last i,
S_i.Ctop = residualFactorProduct A1 last i,
```

where the second product uses the constant vertex family `rho`.  Therefore the
same tail can be written explicitly as

```text
ProductTail_last = 0,
ProductTail_p =
  -(residualFactorProduct C last p.succ
      * A3_p
      * (residualFactorProduct A1 last p.castSucc)^-1)
    + ProductTail_{p+1}.
```

## Endpoint Algebra Deferred

For a nonempty edge family, the last summand has
`D_{last+1}=I`, so the paper-facing endpoint solve should later isolate

```text
A3_last =
  -(F3_0 + sum over p < last of
      residualFactorProduct C last p.succ
        * A3_p
        * (residualFactorProduct A1 last p.castSucc)^-1)
    * Ctop_last.
```

That solve needs an explicit nonempty-edge formulation and a determinant-unit
side condition for `Ctop_last` so right-multiplication by `Ctop_last` cancels
the displayed inverse.  It is not part of this rung.

## Lean Scope

The Lean theorem should state the recursive tail sum first, because it matches
the repository's `Nat.decreasingInduction` definitions of `suffixState` and
`residualFactorProduct`.

Main Lean names:

```text
retainedPassiveLowerLeftTailSum
retainedPassiveLowerLeftTailSum_castSucc
suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_eq_tailSum
suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_zero_eq_tailSum
suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix
retainedPassiveLowerLeftProductTailSum
retainedPassiveLowerLeftTailSum_eq_productTailSum
suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_eq_productTailSum
suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_zero_eq_productTailSum
```

## Nonclaims

This proves finite suffix-state algebra only.  It does not solve `A3_last`,
does not construct the retained-passive coordinate domain, does not prove
source-rank coverage, source/image equality, source-measure pushforward,
Jacobian/prior density transport, normal crossings, pole order, or RLCT.

Lean's matrix inverse is total.  Analytic or chart-regularity uses of the
displayed inverses must still pair these formulas with determinant-unit facts
for the relevant `Ctop` product.
