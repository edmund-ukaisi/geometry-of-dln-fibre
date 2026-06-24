# Reproduction - Definition 3 `L=2` branch order disagreement

Date: 2026-06-24.

Status: pen-and-paper reproduction before Lean.

## Question

The `(2,3,3)` diagnostic shows that overlapping Definition 3 branch choices can
give different finite Theorem 2 lambda values.  Can the overlap also affect
the finite order formula, even when lambda happens to agree?

## Source Anchors

Aoyagi Definition 3, PDF pp. 8-9, defines the selected value set

```text
M = { M^(S_j) : j = 1,...,ell+1 }
```

and applies the nonselected clauses by value membership in this selected set.
Theorem 2, PDF p. 9, then uses the chosen `ell`, residue `a`, and selected
widths to compute both lambda and order

```text
theta = a(ell-a)+1.
```

## Concrete Profile

Take

```text
L = 2,   r = 0,
M^(1) = 1,   M^(2) = 2,   M^(3) = 2.
```

In Lean this is encoded by

```text
H(s) = if s=1 then 1 else if s=2 then 2 else if s=3 then 2 else 0.
```

The regular term is zero because `r=0`.

## Repeated-Positive Branch

Use `ell=1` and select source positions `1,2`.  The selected values are

```text
u = 1,   v = 2.
```

They are positive, and the selected value set `{1,2}` covers all source-range
values because `M^(3)=2`.  Hence the nonselected clauses are vacuous and
Definition 3 source data exists.

For `ell=1`, the finite formula package gives

```text
lambda = regularTerm + u*v/2 = 0 + 1*2/2 = 1,
theta = 1.
```

## All-Source Triangle Branch

Use `ell=2` and select all three source positions.  The triangle inequalities
hold:

```text
2*1 < 1+2+2,
2*2 < 1+2+2,
2*2 < 1+2+2.
```

The total selected width is `T=5`, so the odd-parity triangle package uses

```text
ceilWidth = T/2 + 1 = 3,
a = 1,
theta = 1*(2-1)+1 = 2.
```

The selected pair sum is

```text
1*2 + 1*2 + 2*2 = 8.
```

The finite lambda expression is

```text
0 + 1*(2-1)/8 - (T/2 + 1/2)^2/2 + 8/2
= 1/8 - (2 + 1/2)^2/2 + 4
= 1/8 - 25/8 + 4
= 1.
```

## Conclusion

Under the printed Definition 3 conditions as currently formalised, the same
source-range reduced-width profile admits two valid source-data choices with
the same finite lambda formula value but different finite order formulas:

```text
lambda_ell1 = lambda_ell2 = 1,
theta_ell1 = 1,
theta_ell2 = 2.
```

This complements the `(2,3,3)` diagnostic: branch overlap can affect lambda,
and even when lambda agrees it can affect the finite order payload.

## Lean Target

Add to `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`:

```text
AoyagiDefinition3SourceData.exists_L_eq_two_one_two_two_order_disagreement
```

The theorem should construct the repeated-positive and all-source source-data
packages for the concrete profile above and prove the two finite lambda values
are both `1`, while the finite order formulas are `1` and `2`.

## Nonclaims

- This is not a correction of Aoyagi's theorem.
- This does not prove analytic RLCT or pole-order ambiguity.
- This does not use or cite any quiver-based result.
- This does not construct charts, Eq5 payloads, normal crossings, pole order,
  or RLCT extraction.
- This only records a finite Definition 3/Theorem 2 formula diagnostic under
  the currently formalised printed conditions.
