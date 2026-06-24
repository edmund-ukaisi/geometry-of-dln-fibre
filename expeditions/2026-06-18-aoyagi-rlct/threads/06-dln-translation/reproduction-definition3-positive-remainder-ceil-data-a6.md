# Reproduction - Definition 3 positive-remainder ceiling data

Date: 2026-06-24.

Status: pen-and-paper reproduction before Lean.

## Question

The current Definition 3 ceiling-data constructor uses Euclidean division to
produce some `ceilWidth` and `aParam` from a selected-width family.  The
equal-width lane also has an explicit closed form.  This slice isolates the
general explicit positive-remainder form:

```text
sum_j m_j = ell * q + a,        1 <= a <= ell.
```

Under this decomposition, Definition 3's ceiling integer is `q + 1` and the
residue parameter is `a`.

## Source Anchors

In the notation of Aoyagi Definition 3, PDF pp. 8-9, write

```text
T = sum_j M^(S_j).
```

It then chooses an integer `M` satisfying

```text
M - 1 < T / ell <= M
```

and defines

```text
a = T - (M - 1) ell.
```

Lean calls the source integer `M` by the name `ceilWidth`, because Aoyagi also
uses `M` for reduced widths and for a selected-width set.

## Pen-and-paper Calculation

Assume

```text
0 < ell,
T = ell * q + a,
1 <= a <= ell.
```

Then

```text
T / ell = q + a / ell.
```

Because `1 <= a <= ell`, the fraction `a / ell` lies in `(0, 1]`.  Therefore

```text
q < T / ell <= q + 1.
```

Comparing with Aoyagi's defining inequality

```text
M - 1 < T / ell <= M,
```

we take

```text
ceilWidth = M = q + 1.
```

The residue definition then gives

```text
aParam = T - (ceilWidth - 1) * ell
       = T - q * ell
       = a.
```

Equivalently, the selected-sum identity stored by Lean is exactly

```text
T = ell * (ceilWidth - 1) + aParam
  = ell * ((q + 1) - 1) + a
  = ell * q + a.
```

The case `a = ell` is intentional.  It corresponds to the divisible case under
the positive-remainder convention, where the usual zero remainder is replaced
by residue `ell` and the quotient is reduced by one.

## Lean Shape

Add a pure finite-arithmetic constructor:

```text
AoyagiDefinition3CeilData.ofSelectedSumPositiveRemainder
    (ell : Nat) (m : Fin (ell + 1) -> Int) (ceilPred : Int) (a : Nat)
    (hell : 0 < ell)
    (ha_pos : 0 < a) (ha_le : a <= ell)
    (hsum : (sum j : Fin (ell + 1), m j) =
      (ell : Int) * ceilPred + a) :
    AoyagiDefinition3CeilData ell m
```

with fields

```text
ceilWidth = ceilPred + 1,
aParam = a.
```

Here `ceilPred` is the predecessor `ceilWidth - 1`; in the displayed
calculation above it is `q`.  This is the useful primitive because it also
specializes to the equal-width constructor with
`ceilPred = w + q`.

## Nonclaims

- No uniqueness theorem for `ceilWidth`, `aParam`, `q`, or `a` is packaged.
- No theorem that every selected-width family has such a supplied
  decomposition, although it follows from Euclidean division.
- No source-facing explicit package unless a downstream theorem needs to
  expose the fields `data.ceilWidth` and `data.aParam`.
- No arbitrary selected-cutpoint existence or Definition 3 classification.
- No Eq5 payload, Lemma 5 exactness, active-ratio lower bound, chart count,
  chart production, normal crossings, pole order, or RLCT extraction.
