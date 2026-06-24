# Reproduction - A6 Definition 3 `ell=1` ceiling-data simplification

Date: 2026-06-24.

Status: pen-and-paper reproduction before Lean implementation.

## Question

The selected-pair formula packages construct an explicit `ell=1` ceiling datum.
For downstream final sockets, it is better to know that every Definition 3
ceiling datum at `ell=1` has the same finite arithmetic shape.  Then later
theorems do not depend on the particular constructor used for `data`.

## Source Anchor

Aoyagi PDF pp. 8-9 define the ceiling/residue datum by

```text
sum_j m_j = ell * (ceilWidth - 1) + a,
0 < a <= ell.
```

Lean records this as `AoyagiDefinition3CeilData`.

## `aParam`

If `ell=1`, the residue bounds are

```text
0 < aParam <= 1.
```

Since `aParam` is a natural number, this forces

```text
aParam = 1.
```

## `ceilWidth`

Substitute `ell=1` and `aParam=1` into the selected-sum identity:

```text
sum_j m_j = 1 * (ceilWidth - 1) + 1 = ceilWidth.
```

Thus

```text
ceilWidth = sum_j m_j.
```

If the two selected widths are `u` and `v`, then

```text
ceilWidth = u + v.
```

## Order Formula

Aoyagi Theorem 2's displayed order formula is

```text
aParam * (ell - aParam) + 1.
```

With `ell=1` and `aParam=1`, this is

```text
1 * (1 - 1) + 1 = 1.
```

## Lambda Formula

The ceiling form of the finite lambda expression is

```text
regularTerm
  + a*(ell-a)/(4*ell)
  - ell*(ell-1)/4 * (...)
  + pairSum/2.
```

For `ell=1` and `a=1`, both correction terms vanish:

```text
a*(ell-a)/(4*ell) = 0,
ell*(ell-1)/4 = 0.
```

So for any `AoyagiDefinition3CeilData 1 m`,

```text
aoyagiTheorem2Lambda_fromCeilData L 1 H r m data
  = aoyagiTheorem2RegularTerm L H r
      + aoyagiSelectedWidthPairSum 1 m / 2.
```

If `m 0 = u` and `m 1 = v`, the pair sum is `u*v`, giving

```text
aoyagiTheorem2Lambda_fromCeilData L 1 H r m data
  = aoyagiTheorem2RegularTerm L H r + u*v/2.
```

## Guardrails

This slice is finite arithmetic for an already supplied `ell=1` ceiling datum.
It does not construct selected cutpoints, prove Definition 3 source data,
choose a branch, build Eq5 data or charts, identify pole order, prove normal
crossings, or extract RLCT.
