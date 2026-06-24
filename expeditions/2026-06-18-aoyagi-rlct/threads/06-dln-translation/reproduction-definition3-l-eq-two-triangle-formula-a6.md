# Reproduction - A6 Definition 3 `L=2` triangle formula package

Date: 2026-06-24.

Status: pen-and-paper reproduction before Lean implementation.

## Question

For `L=2`, the landed Definition 3 classification says source data exists
exactly in the repeated-positive branch or in the all-source triangle branch.
This slice focuses only on the all-source triangle branch and computes the
explicit finite quantities used by Aoyagi's Theorem 2 formula.

It does not touch the repeated-positive `ell=1` branch, where the selected
pair is noncanonical and needs a separate case split.

## Source Anchor

Aoyagi PDF pp. 8-9 states Definition 3 and Theorem 2's formula.  For three
source layers (`L=2`), the all-source choice has

```text
ell = 2,       C.cut j = j + 1,
m = (w1, w2, w3).
```

The Definition 3 selected strict inequalities are exactly

```text
2*w1 < w1+w2+w3,
2*w2 < w1+w2+w3,
2*w3 < w1+w2+w3.
```

The nonselected clauses are vacuous because every source layer is selected.

## Positive-Remainder Ceiling Datum

Let

```text
T = w1 + w2 + w3 = 2*ceilPred + a,     0 < a <= 2.
```

The generic positive-remainder constructor gives the Definition 3 ceiling
datum with

```text
ceilWidth = ceilPred + 1,
aParam    = a.
```

The Theorem 2 order formula is therefore

```text
theta = a*(2-a) + 1.
```

This is pure finite arithmetic.  The positive-remainder decomposition is
supplied; this slice does not prove Euclidean division or uniqueness.

## Pair Sum

For `ell=2`, Lean's selected-width pair sum is

```text
sum_i sum_j if i.val < j.val then m_i*m_j else 0.
```

With `m=(w1,w2,w3)`, only the pairs `(0,1)`, `(0,2)`, and `(1,2)` contribute,
so

```text
aoyagiSelectedWidthPairSum 2 m
  = w1*w2 + w1*w3 + w2*w3.
```

## Lambda Formula

The finite Theorem 2 formula is by definition

```text
aoyagiTheorem2Lambda_fromCeilData 2 2 H r m data
```

with the `ceil` display:

```text
regularTerm
+ a*(2-a)/(4*2)
- (2*(2-1)/4) * (ceilWidth + (a-2)/2)^2
+ pairSum/2.
```

Substituting `ceilWidth = ceilPred+1` simplifies

```text
ceilWidth + (a-2)/2
  = ceilPred + a/2.
```

Thus the explicit target expression is

```text
aoyagiTheorem2RegularTerm 2 H r
+ (a*(2-a))/8
- ((ceilPred + a/2)^2)/2
+ (w1*w2 + w1*w3 + w2*w3)/2.
```

All casts are into `Q` for this formula.

## Guardrails

This slice must not:

- assert arbitrary Definition 3 source-data existence;
- assert anything about the repeated-positive `ell=1` branch;
- add a source-rank wrapper or final socket without a consumer;
- construct charts, Eq5 payloads, normal crossings, pole order, or RLCT;
- use anything from the quiver-based paper.
