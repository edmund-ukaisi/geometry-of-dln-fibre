# Reproduction - Definition 3 and Theorem 2 formula translation

Date: 2026-06-22.

Status: first A6 formula-notation slice.  This is finite arithmetic and
source notation translation only.

## Source Anchor

Aoyagi Definition 3 starts on PDF p. 8 and continues on p. 9.  Theorem 2 is
on PDF p. 9.  The proof-side version of the same algebra appears around PDF
pp. 24-25, before the final assembly on p. 28.

Definition 3 sets

```text
M^(s) = H^(s) - r,        s = 1,...,L+1.
```

It then selects source indices `S_j`, `j=1,...,ell+1`, and writes the selected
object as

```text
{ M^(S_j) : j = 1,...,ell+1 }.
```

Aoyagi also denotes that selected object by `M`, and later reuses the same
letter `M` for a ceiling integer.  The Lean translation must keep these names
separate.

Let

```text
T = sum_{k=1}^{ell+1} M^(S_k).
```

Definition 3 then chooses the integer `M` satisfying

```text
M - 1 < T / ell <= M
```

and defines

```text
a = T - (M - 1) ell.
```

The strict left inequality and weak right inequality force the residue range

```text
1 <= a <= ell
```

when `0 < ell`.  The endpoint `a = ell` is allowed; the equal-width example
on PDF p. 9 shows this should not be replaced by `a < ell`.

## Formula Reproduction

Write

```text
P = sum_{1 <= i < j <= ell+1} M^(S_i) M^(S_j)
R = (-r^2 + r(H^(1) + H^(L+1))) / 2.
```

Theorem 2 displays the same `lambda` in three forms:

```text
lambda =
  R + a(ell-a)/(4 ell)
    - ell(ell-1)/4 * (T/ell)^2
    + P/2
```

```text
= R + a(ell-a)/(4 ell)
    - ell(ell-1)/4 * (M + (a-ell)/ell)^2
    + P/2
```

```text
= R - (ell-a-1)(ell-a)/4
    - ell(ell-1)/4 * (M^2 + 2((a-ell)/ell)M)
    + P/2.
```

Theorem 2 also states

```text
theta = a(ell-a) + 1.
```

This `theta` is Aoyagi's RLCT order/pole multiplicity, not this repository's
component-count notation.

## Pen-and-paper Check

From the Definition 3 identity,

```text
a = T - (M - 1)ell,
```

we get

```text
T = (M - 1)ell + a = ell*M + (a - ell).
```

Dividing by `ell` gives

```text
T/ell = M + (a - ell)/ell,
```

which is the first-to-second display rewrite.

For the second-to-third display, set `x = ell - a`, so
`(a - ell)/ell = -x/ell`.  The non-regular terms in the second display are

```text
a(ell-a)/(4ell)
  - ell(ell-1)/4 * (M + (a-ell)/ell)^2.
```

Expanding the square gives

```text
- ell(ell-1)/4 * M^2
- ell(ell-1)/4 * 2((a-ell)/ell)M
- ell(ell-1)/4 * ((a-ell)^2/ell^2)
+ a(ell-a)/(4ell).
```

The pure `a,ell` part is

```text
a(ell-a)/(4ell) - (ell-1)(ell-a)^2/(4ell).
```

With `x = ell-a`, this becomes

```text
(ell-x)x/(4ell) - (ell-1)x^2/(4ell)
  = (ell*x - x^2 - ell*x^2 + x^2)/(4ell)
  = x(1-x)/4
  = -(x-1)x/4
  = -(ell-a-1)(ell-a)/4.
```

Thus the second and third displayed formulas agree.

## Lean Translation

The Lean file `lean/DLNFibre/DLN/Aoyagi/FinalFormula.lean` keeps this as a
formula layer:

- `aoyagiReducedWidthInt H r s = (H s : Int) - (r : Int)` avoids Nat
  truncation before rank-width hypotheses are supplied.
- `aoyagiSelectedReducedWidths H r C` reads the selected indexed widths from
  `AoyagiSelectedCutpoints`.
- `aoyagiSelectedWidthValueSet` names the selected value set, but the formula
  uses the indexed family because repeated selected values count in the sum.
- `AoyagiDefinition3CeilData` stores `ell_pos`, `ceilWidth`, `aParam`,
  `selectedSum_eq`, `aParam_pos`, and `aParam_le`.
- `theorem2OrderFormula` names the displayed `theta = a(ell-a)+1` arithmetic
  without claiming RLCT extraction.
- `aoyagiTheorem2Lambda_average`, `aoyagiTheorem2Lambda_ceil`, and
  `aoyagiTheorem2Lambda_expanded` name the three displayed formulas.

Lean proves the finite rewrites:

- `AoyagiDefinition3CeilData.selectedWidthAverage_eq_ceil`;
- `aoyagiTheorem2Lambda_average_eq_fromCeilData`;
- `aoyagiTheorem2Lambda_ceil_eq_expanded`;
- `aoyagiTheorem2Lambda_average_eq_expanded_ofCeilData`.

## Kill Conditions

- Do not use the same name for the selected object and the ceiling integer.
- Do not replace the indexed selected family by only a value set when summing;
  duplicates matter.
- Do not assume `a < ell`; Definition 3 permits `a = ell`.
- Do not divide by `ell` without `0 < ell`.
- Do not formalise `H^(s)-r` as Nat subtraction without explicit
  `r <= H^(s)` hypotheses.
- Do not call this an RLCT theorem.  The Lean slice proves formula
  bookkeeping only; normal-crossing-to-RLCT extraction remains the single
  planned cited analytic boundary.
