# Reproduction - Case 2 transition constructed old-top `Cprime` source-current stack

Date: 2026-06-24.

Status: controller reproduction before Lean formalisation.

## Source Anchor

Aoyagi PDF pp. 21-22 gives the displayed Case 2 chart calculation with the
transported following block

```text
C'_J^(S+1) = Q^-1 C_J^(S+1).
```

The previously formalised selected-entry transition wrapper compares an
arbitrary source-selected chart to Aoyagi's displayed chart on the overlap
where the displayed normalized coordinate is nonzero.  It rewrites the
displayed lower-left substitution block for the transition-generated target
data back to the source-selected substitution block.

This slice combines that transition wrapper with the constructed
old-top/free-`Cprime` `SourceProductionObligation` package.  It is a finite
consumer wrapper only.

## Data

Work over an ordered field `K`, with the Case 2 stage data

```text
1 <= S,
J+1 <= prefixMinNat n (S+1).
```

Fix a source-selected chart index `sourceChart`, source chart coordinates
`u,residual`, and explicit displayed target data

```text
targetU : K,
targetResidual : N x N -> K.
```

Assume the target data are the transition-generated displayed data:

```text
targetU =
  u * normalized(sourceChart,residual,(J+1,J+1)),

targetResidual(q) =
  normalized(sourceChart,residual,q)
    / normalized(sourceChart,residual,(J+1,J+1)).
```

Assume the displayed normalized denominator is nonzero.  The existing
transition lemma then proves:

1. the displayed chart map at the transition point agrees with the source
   chart map at the source point;
2. the displayed target substitution block equals the source-selected
   substitution block;
3. any supplied `SourceProductionObligation` for the target displayed data can
   be consumed to produce the continuing source-current stack package with the
   lower-left block rewritten to the source-selected substitution block.

Now fix source-suffix types

```text
kappa : Fin (L+1) -> Type,
[forall i, Fintype (kappa i)],
[forall i, DecidableEq (kappa i)],
hSuffix : S+1 <= L,
Ctail : forall p : Fin L, Matrix (kappa p.castSucc) (kappa p.succ) K.
```

Let

```text
tau =
  kappa (sourceLayerIndex L (S+2)
    (Nat.succ_le_succ (Nat.zero_le (S+1)))
    (Nat.succ_le_succ hSuffix)).
```

Fix arbitrary old-top rows and arbitrary free displayed chart-coordinate
following data for the target displayed chart:

```text
Cold   : Matrix (case2SourceOldTopRowIndex J) tau K,
Cprime : Matrix (Unit + pivotComplement(displayed pivot column)) tau K.
```

Define the target following factor

```text
C =
  case2DisplayedConstructedSourceFollowingFactorWithOldTopFromCprime
    n data.stage_pos data.continuation targetResidual Cold Cprime.
```

The constructed-obligation slice supplies

```text
SourceProductionObligation data targetResidual kappa hSuffix C Ctail
  (case2DisplayedSourceSuccessorFollowingFactor
    n data.stage_pos data.continuation targetResidual C)
  ((verticalBlock Cold (case2DisplayedFreeCprimeTop ... Cprime))
    .submatrix (case2SourceTerminalRowEquiv J).symm id).
```

## Reproduction

Start from the existing transition consumer.  It requires a supplied
obligation

```text
ob :
  SourceProductionObligation data targetResidual kappa hSuffix
    C Ctail Csucc Cterm.
```

Instantiate that obligation with the constructed package above.  Then:

- the source chart-map equality is exactly the existing transition equality;
- the substitution-block equality is exactly the existing transition
  substitution equality;
- the continuing source-current stack package is exactly the existing
  supplied-`Csucc` stack consumer applied to the constructed obligation.

The successor following object in the output is not newly produced.  It is the
formula-level

```text
Csucc =
  case2DisplayedSourceSuccessorFollowingFactor
    n data.stage_pos data.continuation targetResidual C.
```

The source-current left block still uses the constructed target following
factor `C`, so its current rows are the old-top rows `Cold` over the
reconstructed residual block `Q*Cprime`.  The right block uses the formula
successor of that same `C`.

The source suffix in the stack is the supplied raw

```text
sourceSuffixProduct kappa Ctail S hSuffix.
```

No branch exclusivity, stopped terminal row, actual-width collapse, or
row-exhausted terminal collapse is used in this continuing wrapper.

## Intended Lean Target

Add a wrapper in the Case 2 residual-block chart-family-certificate namespace:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.
  sourceChartTransitionPoint_displayed_continuingSourceCurrentStack_constructedWithOldTopFromCprime_sourceSubstitution_of_displayed_normalized_ne_zero
```

It has the same transition inputs as

```text
sourceChartTransitionPoint_displayed_continuingSourceCurrentStack_suppliedCsucc_sourceSubstitution_of_displayed_normalized_ne_zero
```

but replaces the generic obligation argument by `Cold`, `Cprime`, and `Ctail`,
constructs `C`, and uses

```text
SourceProductionObligation.of_constructedWithOldTopFromCprime_terminalStack.
```

## Boundary Cases

- The theorem assumes the continuing guard `J+2 <= prefixMinNat n (S+1)`
  because the consumed source-current stack theorem is the continuing branch.
- It does not assume stopped next-continuation, actual-width exhaustion, or
  row-exhaustion.
- The terminal matrix inside the constructed obligation is still
  `[Cold; top(Cprime)]` reindexed to source terminal rows; it is not
  `[Cold; Cprime]` and not original source rows.
- The theorem does not source-produce `Csucc`; it only chooses the
  formula-level successor for the constructed `C`.

## Nonclaims

This is finite transition/source-substitution/stack packaging only.  It does
not construct source-produced successor data, suffixes, successor charts,
transition regularity, chart coverage, analytic Jacobian data, normal
crossings, pole order, termination, or RLCT.  It does not repair or use the
printed Case 2 vector mismatch.
