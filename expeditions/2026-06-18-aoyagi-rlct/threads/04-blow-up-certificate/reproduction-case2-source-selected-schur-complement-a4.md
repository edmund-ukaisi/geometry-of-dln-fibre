# Reproduction - A4 Case 2 source-selected Schur complement

Date: 2026-06-24.

Status: Lean formalised; focused/full build, sorry audit, whitespace check,
and independent xhigh review passed.

## Source Anchor

Aoyagi PDF pp. 20-21, Case 2, after the selected residual-block coordinate is
normalised to pivot value `1`.  The paper displays the top-left Case 2 pivot;
the source-selected all-pivot Lean wrappers are finite selected-entry algebra
around supplied residual-block pivots, not a claim that the PDF writes every
non-top-left chart.

## Reproduction

Put a chosen pivot first in the normalised residual block.  The finite block has
the form

```text
A = [ 1  y ]
    [ x  D ],
```

where `x_i` is the lower pivot-column entry, `y_j` is the pivot-row entry, and
`D_ij` is a lower-right entry.  Aoyagi's displayed right operation is the
elementary column operation

```text
Q = [ 1  -y ]
    [ 0   I ].
```

Multiplying gives

```text
A Q
  = [ 1  y ] [ 1  -y ]
    [ x  D ] [ 0   I ]

  = [ 1       0   ]
    [ x  D - x*y ].
```

Thus every lower-right entry is

```text
z_ij = D_ij - x_i*y_j.
```

The subsequent `P` operation clears the lower-left pivot column.  In the
weighted version used in the Lean API, it requires quotient witnesses for the
row weights, but it still applies to the block whose lower-right part is the
same Schur expression `D - x*y`.  This reproduction records the entrywise
coordinate identity only.

For a second target pivot `q = (a,b)` on a selected-entry overlap, let the
source selected chart have normalised product-indexed coordinates `x_rs`.
The overlap condition is

```text
x_ab != 0,
```

the target selected variable and normalised coordinates are

```text
u_q = u*x_ab,
w_rs = x_rs/x_ab,
```

and the target Schur entry for off-pivot row `i != a` and column `j != b` is

```text
z_ij^(q)
  = w_ij - w_ib*w_aj
  = x_ij/x_ab - (x_ib/x_ab)*(x_aj/x_ab).
```

Clearing denominators gives the finite field identity

```text
x_ab^2 * z_ij^(q) = x_ab*x_ij - x_ib*x_aj.
```

The denominator is the normalised coordinate `x_ab`, not the finite center
value `u*x_ab`; this is the same overlap discipline as the previous finite
transition slice.

## Lean Targets

```text
pivotFirstSchurComplement_apply
selectedEntryNormalizedMap_schurComplement_transition_mul_sq
case2SourceSelectedNormalizedBlockOfMem_schurComplement_apply
```

The first theorem is the ring-level scalar projection of the lower-right block
`D - x*y`.  The second is the product-indexed field-level denominator-cleared
overlap identity.  The third is the Case 2 source-coordinate wrapper for a
supplied residual-block pivot.

## Boundary

- This is finite matrix and field algebra only.
- It proves no chart coverage, no analytic transition regularity, no open
  neighbourhood statement, no source-displayed all-pivot atlas, no successor
  matrix or suffix production, no analytic Jacobian/volume theorem, no global
  normal crossings, no pole order, and no RLCT extraction.
- It does not resolve the separate printed-vector mismatch or the p. 21
  displayed extra-`u` caution.

## Kill Conditions

- Do not use the denominator-cleared identity without `x_ab != 0`.
- Do not replace `x_ab != 0` by `u*x_ab != 0`.
- Do not treat this entrywise Schur coordinate formula as a full Case 2
  transition invariant; successor production and analytic regularity remain
  separate obligations.
