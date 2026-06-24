# Reproduction - A4 Case 2 source-current stack substitution block

Date: 2026-06-24.

Status: pen-and-paper reproduced; Lean formalised; xhigh reviewed.

## Source Anchor

Aoyagi PDF pp. 20-22, Case 2.  The continuing branch rewrites the displayed
`Q/P` calculation into a source-current row stack and then multiplies by the
source suffix.  Earlier Lean already has a supplied-obligation consumer that
states this source-current stack with a supplied successor following object
`Csucc`.

This note records only the finite congruence that lets the lower-left
substitution block in that stack be supplied explicitly.

## Reproduction

The existing supplied-obligation continuing stack theorem has a row-operation
witness `P` and a matrix equality of the form

```text
Stack(DisplayedSub(u,residual), C, suffix)
  =
StackPost(Csucc, suffix).
```

The right side has already been rewritten through the obligation's supplied
successor equality

```text
Csucc =
  case2DisplayedSourceSuccessorFollowingFactor n hS hcont residual C.
```

Now suppose we separately know

```text
hB : DisplayedSub(u,residual) = B.
```

Substituting `hB` into the left side gives the same witness `P` for

```text
Stack(B, C, suffix)
  =
StackPost(Csucc, suffix).
```

All other output fields are unchanged:

- the next-center nonempty witness;
- corrected post exponent data;
- post level invariants;
- least-value-gap data;
- post Case 2 gap;
- finite center membership, divisibility, and principalization statements.

This is only a congruence step inside a finite matrix product.  It does not
construct the source-production obligation, construct or source-produce
`Csucc`, produce source suffixes, construct successor charts, prove transition
regularity, prove chart coverage, prove normal crossings, or extract pole
order/RLCT.

## Lean Target

Add a sibling of

```text
Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.
  continuing_sourceCurrentStack_suppliedCsucc
```

with landed name:

```text
Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.
  continuing_sourceCurrentStack_suppliedCsucc_of_substitutionBlock_eq
```

Inputs:

```text
B : Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R
hB :
  case2DisplayedSourceSubstitutionBlock
    n data.stage_pos data.continuation u residual = B
```

Conclusion: the same package as
`continuing_sourceCurrentStack_suppliedCsucc`, except the lower-left
substitution block is `B`.

Expected proof:

1. Call `continuing_sourceCurrentStack_suppliedCsucc ob hnext`.
2. Destructure the returned stack witness.
3. Reuse the same `q` and all post-data fields.
4. Close the matrix equality by `simpa [hB]`.

The focused module build has passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
```

Review:
`review-case2-source-current-stack-substitution-block-a4.md`.

## Boundary

- `B` is supplied; this theorem does not derive a source-side block.
- `Csucc` is still supplied by `SourceProductionObligation`.
- The suffix product is still supplied through the existing suffix family.
- No chart production, transition regularity, analytic Jacobian/volume data,
  normal crossings, pole order, or RLCT extraction is proved.

## Kill Conditions

- If the theorem constructs `SourceProductionObligation` or `Csucc`, stop.
- If post-data fields are changed while rewriting `B`, stop.
- If the statement claims source production of the substituted block rather
  than consuming `hB`, rename or weaken it.
