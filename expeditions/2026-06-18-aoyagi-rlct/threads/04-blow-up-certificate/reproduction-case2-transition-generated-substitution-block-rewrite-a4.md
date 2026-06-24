# Reproduction - A4 Case 2 transition-generated substitution-block rewrite

Date: 2026-06-24.

Status: pen-and-paper reproduced; Lean formalised; review pending.

## Source Anchor

Aoyagi PDF pp. 20-22, Case 2.  The displayed source chart uses the selected
residual-block coordinate `(J+1,J+1)` and substitutes the selected variable
times normalized residual-block coordinates into the finite residual block.

This note records the finite all-pivot selected-entry version of that
substitution-block equality.  The arbitrary target pivot is Lean's finite
all-pivot abstraction; the displayed pivot is the Aoyagi-facing special case.

## Reproduction

Let `E = case2ResidualBlockPivotEntries n S J`.  Let

```text
p in E,   q in E
```

be source and target selected pivots.  For source selected-entry coordinates
`(u, residual)`, write the source-normalized coordinate function as

```text
x_r = case2SourceSelectedNormalizedMapOfMem hp residual r.
```

Assume the target normalized coordinate is nonzero:

```text
d = x_q != 0.
```

The selected-entry transition-generated target data are

```text
targetU = u*d,
targetResidual_r = x_r/d.
```

The source substitution block is the residual-row/residual-column matrix of
finite center values

```text
Sub_p(u,x)_(i,j) = case2SourceSelectedChartMapOfMem hp u residual (i,j).
```

The target substitution block is

```text
Sub_q(u*d,x/d)_(i,j)
  = case2SourceSelectedChartMapOfMem hq (u*d) targetResidual (i,j).
```

There are two cases.

At the target pivot `(i,j)=q`,

```text
Sub_q(u*d,x/d)_q = u*d = u*x_q = Sub_p(u,x)_q.
```

Away from the target pivot,

```text
Sub_q(u*d,x/d)_(i,j)
  = (u*d)*(x_(i,j)/d)
  = u*x_(i,j)
  = Sub_p(u,x)_(i,j),
```

using `d != 0`.  Therefore the residual-block substitution matrices agree:

```text
Sub_q(u*d, x/d) = Sub_p(u, x).
```

## Lean Targets

```text
case2SourceSelectedSubstitutionBlockOfMem_transition_eq_of_target_normalized_ne_zero
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_sourceSelectedSubstitutionBlock_eq_of_target_normalized_ne_zero
```

## Boundary

- The denominator is the normalized target coordinate `d = x_q`, not the
  finite center value `u*d`.
- No `u != 0` or `u*d != 0` hypothesis is used.
- This proves equality of substitution blocks, not equality of normalized
  blocks.
- This is not the target Schur-complement or `Q/P` reduced-block rewrite.
- The arbitrary target-pivot statement is a finite all-pivot selected-entry
  abstraction; only the displayed pivot is directly Aoyagi-facing.
- This proves no analytic transition regularity, no open-neighbourhood
  gluing, no chart coverage, no source-displayed all-pivot atlas, no
  source-produced global successor object, no suffix production, no analytic
  Jacobian/volume theorem, no global normal crossings, no pole order, and no
  RLCT extraction.

## Kill Conditions

- Do not replace `d != 0` by `(u*d) != 0`.
- Do not claim the complementary overlap where `d = 0` is handled.
- Do not read this substitution-block equality as source production of
  arbitrary `Csucc` or `C'^(S+1)`.
- Do not infer chart regularity or transition regularity from this finite
  equality.
- Do not use all-pivot chart indices as evidence that Aoyagi prints every
  pivot chart.
