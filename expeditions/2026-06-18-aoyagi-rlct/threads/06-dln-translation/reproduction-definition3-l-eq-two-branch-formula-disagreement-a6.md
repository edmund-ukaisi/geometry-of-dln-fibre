# Reproduction - Definition 3 `L=2` branch formula disagreement

Date: 2026-06-24.

Status: pen-and-paper reproduction before Lean.

## Question

The `L=2` finite classification says Definition 3 source data exists in either
the repeated-positive `ell=1` branch or the all-source triangle `ell=2`
branch.  These branches can overlap.  Does Theorem 2's displayed finite lambda
formula agree on the overlap?

## Source Anchors

Aoyagi Definition 3, PDF pp. 8-9, defines a selected value set

```text
M = { M^(S_j) : j = 1,...,ell+1 }
```

and imposes conditions by value membership in this selected set.  In
particular, a source width whose value equals one of the selected values is not
subject to the nonselected clauses.

Theorem 2, PDF p. 9, then uses the chosen `ell`, selected widths, ceiling
integer `M`, residue `a`, and pair sum in the displayed lambda and order
formulas.

## Concrete Profile

Take

```text
L = 2,   r = 0,
M^(1) = 2,   M^(2) = 3,   M^(3) = 3.
```

In Lean this is encoded by

```text
H(s) = if s=1 then 2 else if s=2 then 3 else if s=3 then 3 else 0.
```

The regular term is zero because `r=0`.

## Repeated-Positive Branch

Use `ell=1` and select source positions `1,2`.  The selected values are

```text
u = 2,   v = 3.
```

They are positive, and the selected value set `{2,3}` covers all source-range
values because `M^(3)=3`.  Hence the nonselected clauses are vacuous and
Definition 3 source data exists.

For `ell=1`, the finite formula package gives

```text
lambda = regularTerm + u*v/2 = 0 + 2*3/2 = 3,
theta = 1.
```

## All-Source Triangle Branch

Use `ell=2` and select all three source positions.  The triangle inequalities
hold:

```text
2*2 < 2+3+3,
2*3 < 2+3+3,
2*3 < 2+3+3.
```

The total selected width is `T=8`, so the even-parity triangle package uses

```text
ceilWidth = T/2 = 4,
a = 2,
theta = 1.
```

The selected pair sum is

```text
2*3 + 2*3 + 3*3 = 21.
```

The finite lambda expression is therefore

```text
0 + 2*(2-2)/8 - ((T/2 - 1) + 2/2)^2/2 + 21/2
= 0 - 4^2/2 + 21/2
= 5/2.
```

## Conclusion

Under the printed Definition 3 conditions as currently formalised, the same
source-range reduced-width profile admits two valid source-data choices whose
Theorem 2 finite lambda formulas are different:

```text
3 != 5/2.
```

This is not a Lean inconsistency.  It is a diagnostic showing that a final
source-facing theorem cannot quantify over arbitrary Definition 3 source-data
choices for this profile unless an additional source convention chooses a
branch or proves that one of these branches should be excluded.

## Lean Target

Add to `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`:

```text
AoyagiDefinition3SourceData.exists_L_eq_two_two_three_three_formula_disagreement
```

The theorem should construct the repeated-positive and all-source source-data
packages for the concrete profile above and prove the two finite lambda values
are respectively `3` and `5/2`.

## Nonclaims

- This is not a correction of Aoyagi's theorem.
- This does not prove the analytic RLCT is ambiguous.
- This does not use or cite any quiver-based result.
- This does not construct charts, Eq5 payloads, normal crossings, pole order,
  or RLCT extraction.
- This only records a finite Definition 3/Theorem 2 formula diagnostic under
  the currently formalised printed conditions.
