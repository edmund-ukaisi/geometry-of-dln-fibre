# A4 Case 2 Arbitrary Selected-Entry Source Substitution

Status: reproduced finite algebra for an arbitrary selected Case 2 residual
entry; not a source proof of arbitrary-pivot chart coverage.

## Source Data

In Case 2, Aoyagi blows up the residual-block center

```text
d_ij = 0,    J+1 <= i <= mu_S,    J+1 <= j <= n_(S+1).
```

The PDF displays the top-left chart selecting `d_(J+1,J+1)`. For a formal
chart-family scaffold, the finite center also has charts obtained by selecting
any residual-block entry. This note records only the algebra shared by those
selected-entry charts.

Rows remain prefix-minimum bounded:

```text
I = { i | J+1 <= i <= mu_S },
```

while columns use the actual active width:

```text
K = { j | J+1 <= j <= n_(S+1) }.
```

## Reproduction

Choose a pivot entry `(i0,j0) in I x K`. Let `r0 : I` and `c0 : K` be the
corresponding finite row and column indices. In the selected-entry chart, write
the selected variable as `u` and define the normalised residual matrix

```text
A^p_ij = 1        if (i,j) = (r0,c0),
A^p_ij = rho_ij  otherwise.
```

The source-substituted residual block is

```text
D^p_ij = u A^p_ij.
```

For row weights `w : I -> R`, entrywise:

```text
(diag(w) D^p)_ij = w_i (u A^p_ij)
                 = (u w_i) A^p_ij.
```

Hence

```text
diag(w) D^p = diag(i => u w_i) A^p.
```

Putting `r0` and `c0` first gives

```text
(diag(w) D^p)^(p-first)
  =
diag(u w_r0, (u w_i)_{i != r0}) (A^p)^(p-first).
```

If `C : K -> T` is the following factor, then the same equality is compatible
with multiplication after reindexing the columns of `C` into pivot-first order:

```text
((diag(w) D^p) C)^(row p-first)
  =
(diag(u w_r0, (u w_i)_{i != r0}) (A^p)^(p-first)) C^(col p-first).
```

The conditional `Q/P` wrapper then applies the existing pivot-first algebra if
the selected pivot-row weight divides every pivot-complement row weight after
pivot-first reindexing:

```text
u w_r0 divides u w_i,    i in I with i != r0.
```

Flat residual-row weights are a sufficient condition. The theorem still only
uses supplied finite algebra; it does not prove that Aoyagi's source chart
family has been constructed or covered.

## Scope

This checkpoint proves:

- source row/column subtype extraction from a finite Case 2 center membership
  proof;
- arbitrary selected-entry source substitution;
- pivot-first transport of diagonal row weights and following factors;
- conditional arbitrary selected-pivot `Q/P` under explicit divisibility or
  flat row weights.

It does not prove:

- affine blow-up atlas construction or chart coverage;
- that the PDF displays arbitrary non-top-left selected-entry charts;
- chart regularity or Jacobian facts;
- recurrence post-state production;
- exponent updates or transition invariants;
- source comparability;
- normal crossings or RLCT extraction.
