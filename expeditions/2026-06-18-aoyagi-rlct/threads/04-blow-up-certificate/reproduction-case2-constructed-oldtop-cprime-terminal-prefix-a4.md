# Reproduction - Case 2 constructed old-top `Cprime` terminal prefix

Date: 2026-06-24.

Status: controller reproduction, xhigh check accepted after corrections.

## Source Anchor

Aoyagi PDF pp. 21-22 stops Case 2 when the displayed next same-stage pivot is
not available and then rewrites the product at the advanced stage.  Aoyagi
gives the terminal-prefix display; the source-row and arbitrary free-`Cprime`
packaging is repo finite algebra motivated by that display and by the
transported factor `C'_J^(S+1)=Q^-1 C_J^(S+1)`.  The previous slice proved
that, for the constructed old-top/free-`Cprime` source following factor, those
source terminal rows are

```text
[Cold; top(Cprime)].
```

This slice only reindexes that source-row terminal matrix onto the terminal
prefix row type `1,...,M(S+1)` under the stopped-prefix equality.  It does not
add a new source theorem.

## Data

Assume the displayed Case 2 formation hypotheses

```text
1 <= S,
J+1 <= prefixMinNat n (S+1),
```

and the stopped-prefix hypothesis

```text
not (J+2 <= prefixMinNat n (S+1)).
```

Together, these imply

```text
prefixMinNat n (S+1) = J+1.
```

Lean packages the resulting row equivalence as

```text
case2SourceTerminalRowEquivPrefixOfNotNext n hcont hstop :
  case2SourceTerminalRowIndex J ≃ case2SourceTerminalPrefixRowIndex n S.
```

Let

```text
Cold :
  Matrix (case2SourceOldTopRowIndex J) tau R

Cprime :
  Matrix (Unit + pivotComplement (case2DisplayedPivotCol n hS hcont)) tau R

C =
  case2DisplayedConstructedSourceFollowingFactorWithOldTopFromCprime
    n hS hcont residual Cold Cprime.
```

For the product statement also fix

```text
[Fintype tau],
Wold :
  Matrix (case2SourceOldTopRowIndex J) (case2SourceOldTopRowIndex J) R,
b0 : R,
F : Matrix tau upsilon R.
```

The previous terminal-row slice gives the reindexed block statement

```text
(case2DisplayedSourceTerminalCprimeCandidate n hS hcont residual C).submatrix
    (case2SourceTerminalRowEquiv J) id
  =
verticalBlock Cold (case2DisplayedFreeCprimeTop n hS hcont Cprime).
```

The direct source-row equality used below is obtained by the bridge constructor

```text
SuppliedTerminalCprimeBridge.of_constructedWithOldTopFromCprime
```

and the existing theorem

```text
SuppliedTerminalCprimeBridge.cprimeCandidate_eq.
```

## Prefix Reindexing

The terminal-prefix candidate is definitionally

```text
case2DisplayedSourceTerminalCprimePrefixCandidate n hS hcont hstop residual C
  =
(case2DisplayedSourceTerminalCprimeCandidate n hS hcont residual C).submatrix
  (case2SourceTerminalRowEquivPrefixOfNotNext n hcont hstop).symm id.
```

Substituting the constructed terminal-row equality gives

```text
case2DisplayedSourceTerminalCprimePrefixCandidate n hS hcont hstop residual C
  =
((verticalBlock Cold (case2DisplayedFreeCprimeTop n hS hcont Cprime)).submatrix
  (case2SourceTerminalRowEquiv J).symm id).submatrix
  (case2SourceTerminalRowEquivPrefixOfNotNext n hcont hstop).symm id.
```

This is the explicit terminal-prefix matrix.  The outer reindexing changes the
row type from source terminal rows `1,...,J+1` to terminal prefix rows
`1,...,M(S+1)`.

## Product Form

The existing prefix product candidate satisfies

```text
case2DisplayedSourceTerminalProductPrefixCandidate Wold n hS hcont hstop
    b0 residual C F
  =
(case2DisplayedSourceTerminalWeightPrefixCandidate Wold n hcont hstop b0 *
  case2DisplayedSourceTerminalCprimePrefixCandidate n hS hcont hstop residual C) * F.
```

After substituting the explicit constructed prefix terminal matrix, the
constructed stopped product becomes

```text
(case2DisplayedSourceTerminalWeightPrefixCandidate Wold n hcont hstop b0 *
  explicitPrefixRows) * F.
```

where

```text
explicitPrefixRows =
  ((verticalBlock Cold (case2DisplayedFreeCprimeTop n hS hcont Cprime)).submatrix
    (case2SourceTerminalRowEquiv J).symm id).submatrix
    (case2SourceTerminalRowEquivPrefixOfNotNext n hcont hstop).symm id.
```

## Boundary Cases

- The stopped-prefix hypothesis identifies the terminal source-row interval
  with the terminal prefix interval.  Without it, the row types are different.
- This does not assume actual-width exhaustion `n(S+1)=J+1`.  In a
  row-exhausted wide-next case, the surviving pivot row remains the transported
  top row of `Q^-1 C`, here the free top row of `Cprime`; it is not replaced by
  the original source row.
- If `J=0`, the old-top block is empty and the prefix rows consist of the
  single transported pivot row.

## Formalisation Target

Useful Lean names:

```text
case2DisplayedSourceTerminalCprimePrefixCandidate_constructedWithOldTopFromCprime_eq_terminalStackPrefix
case2DisplayedSourceTerminalProductPrefixCandidate_constructedWithOldTopFromCprime_eq_weight_mul_terminalStackPrefix_mul
```

Both should be finite reindexing/product consumers of the terminal-row theorem
and existing prefix product theorem.

## Kill Conditions

- Replacing the transported top row by the original source row without
  `n(S+1)=J+1` is wrong.
- Stating `[Cold; Cprime]` as the terminal prefix matrix is wrong; terminal
  rows contain only `top(Cprime)`.
- Dropping `hstop` is wrong because the terminal source-row type need not equal
  the terminal prefix row type.
- Naming the result as source production of terminal data, chart construction,
  transition regularity, normal crossings, pole order, or RLCT overclaims.

## Nonclaims

This is finite reindexing and product-form bookkeeping only.  It does not
construct source data, terminal chart data, suffixes, successor chart families,
transition regularity, chart coverage, coordinate-derived post-data,
Jacobians, normal crossings, pole order, termination, RLCT extraction, or a
repair of the printed Case 2 vector mismatch.
