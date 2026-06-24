# Reproduction - A4 Case 2 residual-subtype Schur transition

Date: 2026-06-24.

Status: Lean formalised and gated.  Focused build, full build, sorry audit,
whitespace check, and controller/scout review passed.

## Source Anchor

Aoyagi PDF pp. 20-21, Case 2, where the selected pivot is normalised and the
finite `Q/P` calculation exposes the lower-right Schur expression.  This note
adds no new source claim beyond the previous Schur-complement reproduction: it
only adapts the denominator-cleared source-coordinate identity to the
residual-row and residual-column subtype indices used by the `Q/P` lower-right
block.

## Reproduction

Let `sourcePivot` and `targetPivot = (a,b)` be supplied members of the Case 2
residual-block pivot set.  In the source selected chart write

```text
x_rs = case2SourceSelectedNormalizedMapOfMem sourceMem residual (r,s).
```

Assume the normalised target coordinate is nonzero:

```text
x_ab != 0.
```

The target residual function is

```text
w_rs = x_rs / x_ab.
```

For an off-target residual row subtype index

```lean
i : pivotComplement (case2ResidualBlockPivotRowOfMem targetMem)
```

and off-target residual column subtype index

```lean
j : pivotComplement (case2ResidualBlockPivotColOfMem targetMem)
```

the source labels are `i.1.1` and `j.1.1`.  Since the pivot row and column
subtypes have values `a` and `b`, these labels also define ambient off-target
indices.  The target residual-block Schur coordinate is

```text
z_ij = w_(i,j) - w_(i,b) * w_(a,j),
```

where the notation reads `i` and `j` by their source labels.  Clearing
denominators gives

```text
x_ab^2 * z_ij
  = x_ab*x_(i,j) - x_(i,b)*x_(a,j).
```

This is exactly the ambient denominator-cleared formula, with the row and
column indices obtained from residual-block subtype complements.

## Lean Target

```text
case2SourceSelectedNormalizedBlockOfMem_schurComplement_transition_mul_sq
```

The theorem is a type adapter over
`case2SourceSelectedNormalizedMapOfMem_schurComplement_transition_mul_sq`.

## Boundary

- This is finite source-coordinate bookkeeping only.
- It proves no chart coverage, no analytic transition regularity, no
  open-neighbourhood gluing, no source-displayed all-pivot atlas, no successor
  residual/following-factor production, no analytic Jacobian/volume theorem,
  no global normal crossings, no pole order, and no RLCT extraction.
- The denominator is the normalised coordinate `x_ab`, not the finite center
  value `u*x_ab`.

## Kill Conditions

- Do not use the theorem without the explicit nonzero denominator.
- Do not replace `x_ab != 0` by `u*x_ab != 0`.
- Do not treat this residual-subtype adapter as successor production; it only
  rewrites an already-defined target residual block.
