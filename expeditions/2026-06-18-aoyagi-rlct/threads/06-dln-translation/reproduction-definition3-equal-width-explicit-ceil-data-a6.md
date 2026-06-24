# Reproduction - Definition 3 equal-width explicit ceiling data

Date: 2026-06-24.

Status: pen-and-paper reproduction before Lean.

## Question

The existing equal-width lane proves that, when every source-range reduced
width is the same positive value `w`, Aoyagi Definition 3 admits the
consecutive selected cutpoints with `ell = L`.  The current Lean package still
uses a generic Euclidean constructor for the resulting Definition 3
`ceilWidth` and `aParam`.

This slice records the explicit values in the equal-width case from a supplied
positive-remainder decomposition of `w`.

## Source Anchors

Aoyagi Definition 3 and the equal-width example on PDF pp. 8-9.  In the
example, if

```text
M^(1) = M^(2) = ... = M^(L+1),
```

then Aoyagi takes `ell = L`, chooses the integer `M` satisfying

```text
M - 1 < ((L + 1) M^(1)) / L <= M,
```

and defines

```text
a = (L + 1) M^(1) - (M - 1) L.
```

Lean calls Aoyagi's ceiling integer `ceilWidth`, because the paper also uses
`M` for the selected-width set and for the individual reduced widths.

## Pen-and-paper Calculation

Let the common selected reduced width be `w`.  In the equal-width lane there
are `L+1` selected widths and `ell = L`, so the selected sum is

```text
sum_j m_j = (L + 1) w.
```

Assume a positive-remainder decomposition

```text
w = L q + a,        1 <= a <= L.
```

This convention includes the divisible case by taking `a = L` and reducing
the quotient by one.  Then

```text
((L + 1) w) / L = w + w/L
                = w + q + a/L.
```

Since `1 <= a <= L`, the fraction `a/L` lies in `(0,1]`.  Hence the integer
selected by Aoyagi's inequality is

```text
ceilWidth = w + q + 1.
```

Indeed,

```text
ceilWidth - 1 = w + q < w + q + a/L <= w + q + 1 = ceilWidth.
```

The corresponding residue is

```text
aParam
  = (L + 1) w - (ceilWidth - 1) L
  = (L + 1) w - (w + q) L
  = w - L q
  = a.
```

Equivalently, the selected-sum identity stored by Lean is

```text
(L + 1) w = L (ceilWidth - 1) + aParam
          = L (w + q) + a.
```

The last equality follows exactly from `w = L q + a`.

## Lean Shape

Add a pure finite-arithmetic constructor in namespace
`AoyagiDefinition3CeilData`:

```text
def equalWidthOfDecomposition
    (L w q a : Nat) (ha_pos : 0 < a) (ha_le : a <= L)
    (hw : w = L * q + a) :
    AoyagiDefinition3CeilData L (fun _ : Fin (L + 1) => (w : Int))
```

with fields

```text
ceilWidth = (w : Int) + (q : Int) + 1,
aParam = a.
```

Then add a source-facing package in namespace
`AoyagiDefinition3SourceData` combining:

1. consecutive equal-width selected cutpoints;
2. the constant selected-width family `m j = w`;
3. `m = aoyagiSelectedReducedWidths H r C`;
4. the explicit ceiling datum above;
5. the standard downstream nonnegativity, Nat-width, strict selected, and
   selected-width upper-bound facts.

The source-facing package should require only the constant reduced-width
hypothesis and the decomposition hypotheses.  Positivity of `L` and `w`
follow from `0 < a`, `a <= L`, and `w = L*q + a`.

## Nonclaims

- No arbitrary selected-cutpoint or Definition 3 source-data existence theorem.
- No uniqueness theorem for `ceilWidth` or `aParam`.
- No proof that every positive `L,w` has the displayed positive-remainder
  decomposition, although it is elementary.
- No Eq5 payload, Lemma 5 exactness, active-ratio lower bound, chart count,
  chart production, normal crossings, pole order, or RLCT extraction.
