# Reproduction - A4 Case 2 supplied-successor reindexed product

Date: 2026-06-24.

Status: pen-and-paper reproduced; Lean formalised; xhigh reviewed.

## Source Anchor

Aoyagi PDF pp. 20-22, Case 2.  The displayed chart calculation applies the
finite `Q/P` operations, clears the selected pivot, and reindexes the result
into the next same-stage source product shape.  Earlier Lean already proves
that reindexed product with the formula-level successor following factor

```text
C_formula = case2DisplayedSourceSuccessorFollowingFactor n hS hcont residual C.
```

This note records only the finite consumer step where a later source-production
obligation supplies a concrete object `Csucc` together with

```text
hCsucc : Csucc = C_formula.
```

## Reproduction

Let the displayed reindexed product theorem have a witness `q` for the row
operation `P`.  Its matrix equality has the form

```text
Left(B) = Right(C_formula),
```

where `B` is the lower-left substitution block supplied to the congruence
version of the theorem.  More explicitly, the right side is

```text
fromBlocks W_post 0 0
  (D_post * Residual_post)
  *
  verticalBlock
    (oldTopBlock at J+1 of C_formula)
    (followingFactor at (S,J+1) of C_formula).
```

Now suppose an external source-production package has named the successor
following object `Csucc` and proves

```text
Csucc = C_formula.
```

Substituting this equality into the right side gives

```text
Right(Csucc) = Right(C_formula).
```

Therefore the same witness `q` proves the supplied-successor version

```text
Left(B) = Right(Csucc).
```

All post-data fields are unchanged:

- the post recurrence state is still `pre.case2Succ upivot`;
- the corrected exponent post-data are unchanged;
- the level invariant, least-value-gap invariant, and recurrence gap are the
  same fields returned by the displayed reindexed product theorem;
- the lower-left block rewrite, if any, is still supplied separately as
  `case2DisplayedSourceSubstitutionBlock ... = B`.

This is a congruence step in the displayed finite matrix identity.  It does not
construct `Csucc`; it only lets downstream theorems state the already-proved
identity in terms of a supplied `Csucc` once the formula equality is carried as
an explicit hypothesis.

## Lean Target

Add a supplied-successor proposition sibling:

```text
Case2DisplayedReindexedNextSourceProductEqWithSubstitutionBlockAndCsucc
```

and a consumer theorem:

```text
sourceChartMap_reindexedNextSourceProduct_fromCase2SuccCorrectedPostData_of_substitutionBlock_eq_of_Csucc_eq
```

The theorem consumes:

```text
hB :
  case2DisplayedSourceSubstitutionBlock n hS hcont u residual = B
hCsucc :
  Csucc = case2DisplayedSourceSuccessorFollowingFactor n hS hcont residual C
```

and returns the same existential package as the existing substitution-block
congruence theorem, but with the right-hand side written using `Csucc`.

Then add a thin `SourceProductionObligation` wrapper:

```text
SourceProductionObligation.reindexedNextSourceProduct_of_substitutionBlock_eq
```

This wrapper supplies `hCsucc` from `ob.Csucc_eq_formula`; it has no additional
mathematical content.

The targeted module build has passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
```

## Boundary

- This is not source production of `Csucc`.
- It does not produce suffix/following-product data.
- It does not construct successor chart families, coverage, transition
  regularity, analytic Jacobian/volume data, normal crossings, pole order, or
  RLCT extraction.
- It does not derive the corrected recurrence/exponent post-data from the
  printed source display; it reuses the already formalised corrected post-data
  theorem.
- The only new mathematical move is substitution of the supplied equality
  `Csucc = C_formula` into the finite product identity.

## Kill Conditions

- If the theorem can be read as constructing `Csucc`, rename or weaken it.
- If the theorem hides the equality `Csucc = C_formula`, expose it as an input.
- If the theorem changes any post-data field while rewriting `Csucc`, stop:
  the reproduction only justifies a right-hand-side congruence.
