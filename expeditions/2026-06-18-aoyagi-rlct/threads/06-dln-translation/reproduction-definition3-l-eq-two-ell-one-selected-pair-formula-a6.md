# Reproduction - A6 Definition 3 `L=2`, `ell=1` selected-pair formula package

Date: 2026-06-24.

Status: pen-and-paper reproduction before Lean implementation.

## Question

The repeated-positive branch of the `L=2` Definition 3 classification has
`ell=1`, hence exactly two selected source cutpoints.  The selected pair is not
canonical from the bare fact that some two source-range reduced widths repeat:
different repeated equalities can choose different selected cutpoints.

The safe source-facing theorem therefore exposes the selected pair `C` instead
of hiding it behind a generic repeated-branch statement.

## Source Anchor

Aoyagi PDF pp. 8-9 defines the selected cutpoints and Theorem 2 formula.  For
`L=2`, an `ell=1` selected pair has two selected widths

```text
m0 = u,
m1 = v.
```

If every source-range reduced width lies in the selected value set and both
selected values are positive, the already-landed constructor

```text
of_ell_eq_one_selectedValueSet_covers
```

builds Definition 3 source data.  The nonselected clauses are vacuous because
the cover is by selected values.

## Ceiling Datum

For `ell=1`, use a supplied positive-remainder decomposition with remainder
`a=1`:

```text
u + v = ceilPred + 1.
```

The positive-remainder constructor gives

```text
ceilWidth = ceilPred + 1,
aParam    = 1.
```

The order formula is

```text
1 * (1 - 1) + 1 = 1.
```

## Pair Sum and Lambda

For `ell=1`, the selected pair sum has one contributing pair:

```text
aoyagiSelectedWidthPairSum 1 m = u*v.
```

The Theorem 2 lambda expression simplifies because the ceiling-quadratic
coefficient is

```text
ell*(ell-1)/4 = 0.
```

Also the `a*(ell-a)/(4*ell)` term is zero for `ell=1`, `a=1`.  Hence

```text
aoyagiTheorem2Lambda_fromCeilData 2 1 H r m data
  = aoyagiTheorem2RegularTerm 2 H r + u*v/2.
```

This is finite formula bookkeeping only.

## Guardrails

This slice must not:

- claim a canonical formula for the whole repeated-positive branch without
  exposing the selected pair;
- automatically choose quotient/remainder data;
- add a source-rank wrapper or final socket;
- construct Eq5 payloads, charts, normal crossings, pole order, or RLCT.
