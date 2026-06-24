# Reproduction - Case 2 constructed old-top `Cprime` terminal-prefix source suffix

Date: 2026-06-24.

Status: controller reproduction, xhigh check accepted after correction.

## Source Anchor

Aoyagi PDF pp. 21-22 displays the stopped Case 2 terminal product after the
`Q`/`Q^-1` transport, in terminal-prefix row order.  This slice does not add a
new source formula.  It specializes existing finite consumer theorems to the
constructed source following factor from the previous old-top/free-`Cprime`
slices.

The relevant already-reproduced facts are:

- the constructed source following factor has old rows `Cold`;
- its displayed source following block is `Q*Cprime`, written in Lean as
  `case2DisplayedPaperConstructedFollowingFactor ... Cprime`;
- its transported terminal source-row matrix is the source-row reindexing of
  `[Cold; top(Cprime)]`;
- under the stopped-prefix hypothesis, this terminal source-row matrix
  reindexes to terminal-prefix rows.

## Data

Assume the displayed Case 2 supplied chart-family boundary

```text
data :
  Case2DisplayedSuppliedChartFamilyBoundary R L n S J
    t t' numerator numerator' leastValue leastValue'
    pre post u ChartRegular TransitionRegular.
```

In particular,

```text
data.stage_pos    : 1 <= S,
data.continuation : J+1 <= prefixMinNat n (S+1).
```

Assume stopped next-continuation:

```text
hstop : not (J+2 <= prefixMinNat n (S+1)).
```

Fix a source suffix setup:

```text
kappa : Fin (L+1) -> Type,
hSuffix : S+1 <= L,
Ctail : forall p : Fin L, Matrix (kappa p.castSucc) (kappa p.succ) R.
```

Let the following-factor target type be

```text
tau =
  kappa (sourceLayerIndex L (S+2)
    (Nat.succ_le_succ (Nat.zero_le (S+1)))
    (Nat.succ_le_succ hSuffix)).
```

Fix arbitrary old-top and free chart-coordinate following data

```text
Cold :
  Matrix (case2SourceOldTopRowIndex J) tau R,

Cprime :
  Matrix
    (Unit + pivotComplement
      (case2DisplayedPivotCol n data.stage_pos data.continuation))
    tau R.
```

Define

```text
C =
  case2DisplayedConstructedSourceFollowingFactorWithOldTopFromCprime
    n data.stage_pos data.continuation residual Cold Cprime.
```

Then:

```text
case2DisplayedSourceOldTopBlock C = Cold,
```

and

```text
case2DisplayedSourceFollowingFactor n data.stage_pos data.continuation C
  =
case2DisplayedPaperConstructedFollowingFactor
  n data.stage_pos data.continuation residual Cprime.
```

## Existing Consumer

The already-proved stopped terminal-prefix source-suffix consumer says that,
for any following factor `C` and any supplied terminal bridge,

```text
exists q,
  matrixEntryIdeal(source old-top/source-suffix product using C)
  =
  matrixEntryIdeal(
    (terminal-prefix weight *
      bridge.Cterm reindexed to terminal-prefix rows) *
    sourceSuffixProduct kappa Ctail S hSuffix).
```

The bridge for constructed old-top/free-`Cprime` data is

```text
SuppliedTerminalCprimeBridge.of_constructedWithOldTopFromCprime
  n data.stage_pos data.continuation residual Cold Cprime.
```

Its terminal matrix is

```text
(verticalBlock Cold
  (case2DisplayedFreeCprimeTop n data.stage_pos data.continuation Cprime))
  .submatrix (case2SourceTerminalRowEquiv J).symm id.
```

Therefore the bridge's terminal-prefix row presentation is

```text
((verticalBlock Cold
    (case2DisplayedFreeCprimeTop n data.stage_pos data.continuation Cprime))
  .submatrix (case2SourceTerminalRowEquiv J).symm id)
  .submatrix
    (case2SourceTerminalRowEquivPrefixOfNotNext
      n data.continuation hstop).symm id.
```

## Result To Formalise

Specializing the existing consumer to the constructed `C` gives an existential
row-operation witness `q` such that the source side is

```text
((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
    (weightedPivotBlockRowOp q (...) *
      (diagonal (fun i => pre.case2ResidualRowWeight i) *
        case2DisplayedSourceSubstitutionBlock
          n data.stage_pos data.continuation u residual)
      .submatrix (...) (...)) *
    verticalBlock Cold
      (case2DisplayedPaperConstructedFollowingFactor
        n data.stage_pos data.continuation residual Cprime)) *
  sourceSuffixProduct kappa Ctail S hSuffix)
```

and the terminal side is

```text
((case2DisplayedSourceTerminalWeightPrefixCandidate
    (case2DisplayedSourceOldTopWeight pre)
    n data.continuation hstop (post.weight (J+1)) *
  explicitPrefixRows) *
  sourceSuffixProduct kappa Ctail S hSuffix),
```

where `explicitPrefixRows` is the double reindexing of
`[Cold; top(Cprime)]` displayed above.

The intended Lean theorem name is

```text
Case2DisplayedSuppliedChartFamilyBoundary.
  exists_sourceOldTopSourceSuffix_entryIdeal_eq_constructedOldTopFromCprimeTerminalPrefixProduct_of_not_next_cont
```

## Boundary Cases

- `hstop` is required.  Without it the terminal-prefix row type is not
  equivalent to the source terminal row type.
- This result does not assume actual-width exhaustion `n(S+1)=J+1`.
- In row-exhausted but wide-next cases, the terminal pivot row is still the
  transported top row `top(Cprime)`, not the original source row.
- The suffix remains the supplied raw source suffix
  `sourceSuffixProduct kappa Ctail S hSuffix`.
- The theorem gives an entry-ideal equality, not literal equality of source
  products.

## Kill Conditions

- Replacing `top(Cprime)` by a full `Cprime` block in the terminal-prefix
  matrix is wrong.
- Replacing `top(Cprime)` by the original source row is wrong without the
  separate actual-width hypothesis.
- Dropping `hstop` is wrong.
- Claiming source production of `Csucc`, `C'^(S+1)`, suffixes, successor
  charts, transition regularity, chart coverage, normal crossings, pole order,
  or RLCT would overstate the result.

## Nonclaims

This is finite source-suffix and terminal-prefix consumer bookkeeping only.
It does not construct the source suffix, terminal matrix, successor following
factor, successor chart family, transition regularity, chart coverage,
analytic Jacobian data, normal crossings, pole order, termination, or RLCT.
