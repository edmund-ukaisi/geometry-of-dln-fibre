# Pen-and-paper reproduction - A4 Case 2 source successor following factor

Status: reproduced, reviewed, and formalised.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  The displayed calculation forms
`C' = Q^-1 C`.  Existing artifacts already prove the top-row formula and the
unchanged lower-tail formula for this transported following factor.

This checkpoint packages the same formula as a source-order following factor.
It does not construct the chart or a transition theorem.

## Reproduction

Define a source-coordinate matrix

```text
Csucc(j,a) =
  if j = J+1 then top row of (Q^-1 C) at a
  else C(j,a).
```

This is the source-order object suggested by the displayed Case 2 terminal
notation: only the surviving pivot row is changed.

The elementary restrictions are:

1. Pivot row:

   ```text
   Csucc(J+1,a) = case2DisplayedPaperCprimeTop(...,C)((),a).
   ```

2. Off-pivot rows:

   ```text
   j != J+1 -> Csucc(j,a) = C(j,a).
   ```

3. Old top rows:

   For `i in {1,...,J}`, we have `i != J+1`, so

   ```text
   Csucc(i,a) = C(i,a).
   ```

4. Continuing post-pivot tail:

   The next same-stage following factor uses columns

   ```text
   J+2 <= j <= n(S+1).
   ```

   Every such `j` is off the replaced row `J+1`.  Therefore

   ```text
   case2SourceFollowingFactor(S,J+1,Csucc)
     =
   case2SourceFollowingFactor(S,J+1,C).
   ```

5. Actual-width terminal branch:

   If `n(S+1)=J+1`, the top row of `Q^-1 C` has no post-pivot correction
   sum.  Hence `Csucc(J+1,-)=C(J+1,-)`, and all other rows are already
   unchanged:

   ```text
   Csucc = C.
   ```

6. Terminal transported rows:

   The existing transported terminal row matrix is exactly the terminal
   original-row matrix of `Csucc`:

   ```text
   case2DisplayedSourceTerminalOriginalRows(Csucc)
     =
   case2DisplayedSourceTerminalTransportedRows(C).
   ```

   Consequently the existing terminal `C'` candidate is also the original-row
   terminal matrix of `Csucc`.

## Lean Names

The Lean slice adds:

```text
case2DisplayedSourceSuccessorFollowingFactor
case2DisplayedSourceSuccessorFollowingFactor_pivotRow
case2DisplayedSourceSuccessorFollowingFactor_of_ne
case2DisplayedSourceSuccessorFollowingFactor_oldRow
case2SourceFollowingFactor_successorFollowingFactor_succ
case2DisplayedSourceSuccessorFollowingFactor_eq_original_of_width_next_eq
case2DisplayedSourceTerminalOriginalRows_successorFollowingFactor
case2DisplayedSourceTerminalCprimeCandidate_eq_originalRows_successorFollowingFactor
```

## Boundary Checks

- This is formula-level source-coordinate data, not chart production.
- It changes only row `J+1`.
- The continuing tail equality is only a restriction to post-pivot columns; it
  is not the full successor product.
- Actual-width equality with the original source following factor requires
  `n(S+1)=J+1`.
- Row-exhausted branches keep the transported pivot row; they do not replace
  it by the original source row.

## Kill Conditions

- Do not call `Csucc` a chart-produced successor matrix.
- Do not infer recurrence/exponent post-data from this object.
- Do not use row-exhaustion as actual-width exhaustion.
- Do not include old top multipliers, suffix products, chart coverage,
  successor chart-family data, transition invariance, Jacobian arithmetic,
  normal crossings, pole order, or RLCT.
- Do not use the Lehalleur-Rimanyi/quiver paper or quiver Lean as evidence.
