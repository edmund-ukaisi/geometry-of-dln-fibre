# A4 Case 2 Source-Selected Pair Wrapper

Status: reproduced source-coordinate wrapper for a supplied Case 2 residual
pivot pair.

## Source Data

In Case 2, the residual-block center has entries

```text
d_ij = 0,    J+1 <= i <= mu_S,    J+1 <= j <= n_(S+1).
```

The row range is prefix-minimum bounded, while the column range uses the
actual next-layer width. A source pivot pair

```text
p = (i0,j0)
```

is usable in this finite wrapper only with supplied membership

```text
p in {J+1..mu_S} x {J+1..n_(S+1)}.
```

This membership extracts a residual-row subtype pivot and a residual-column
subtype pivot. It is not chart coverage.

## Reproduction

Let

```text
I = { i | J+1 <= i <= mu_S },
K = { j | J+1 <= j <= n_(S+1) }.
```

Given `p=(i0,j0) in I x K`, source-coordinate residual data

```text
rho : Nat x Nat -> R
```

restrict to the residual block by

```text
rho_IK(i,j) = rho(i,j),    i in I, j in K.
```

Likewise a source-coordinate following factor

```text
Csrc : Nat -> T -> R
```

restricts along the residual columns by

```text
C_K(j,t) = Csrc(j,t),    j in K.
```

The selected-entry chart at `p` has selected variable `u` and normalised block

```text
A^p_ij = 1        if (i,j) = (i0,j0),
A^p_ij = rho_ij  otherwise.
```

The source-substituted residual block is

```text
D^p_ij = u A^p_ij.
```

For residual-row weights `w : I -> R`, entrywise:

```text
(diag(w) D^p)_ij = w_i (u A^p_ij)
                 = (u w_i) A^p_ij.
```

After putting the selected row and column first, the diagonal becomes

```text
diag(u w_i0, (u w_i)_{i != i0}).
```

If the old recurrence state satisfies the Case 2 gap, then every old residual
row weight equals the selected row weight:

```text
pre.case2ResidualRowWeight(i) = pre.case2ResidualRowWeight(i0).
```

Thus the already-proved arbitrary selected-pivot `Q/P` identity applies to the
source-restricted residual and following data.

If a supplied successor recurrence state satisfies the Case 2 post-data
package, then for each residual row level

```text
post.weight(i) = u * pre.weight(i).
```

Therefore the pivot-first diagonal on the right side can be written with
successor weights at the selected residual row level and the pivot-complement
residual row levels.

## Scope

This checkpoint proves:

- restriction of source-coordinate residual data to the Case 2 residual block;
- restriction of source-coordinate following factors to the residual columns;
- source-pair wrappers for arbitrary selected-pivot recurrence-gap `Q/P`;
- source-pair successor-weight transport and `Q/P` wrappers from supplied
  post-data.

It does not prove:

- that Aoyagi displays non-top-left Case 2 pivot charts;
- affine blow-up atlas construction or arbitrary-pivot chart coverage;
- source-order transition formulas for non-displayed pivots;
- that a chart produces the supplied post-state;
- chart regularity or Jacobian facts;
- exponent updates or transition invariants;
- source comparability;
- normal crossings or RLCT extraction.
