# Reproduction - Definition 3 equal-width Theorem 2 formula package

Date: 2026-06-26.

Status: pen-and-paper reproduction before Lean.

## Question

The equal-width Definition 3 lane already constructs consecutive selected
cutpoints with `ell = L` and explicit ceiling data from a positive-remainder
decomposition

```text
w = L q + a,        0 < a <= L.
```

This slice computes the remaining finite Theorem 2 formula fields for that
same source-backed branch: the selected pair sum, the order expression, and
the unfolded finite lambda formula.

## Source Anchors

Aoyagi Definition 3 and the equal-width example on PDF pp. 8-9.  Theorem 2's
finite displayed formula on the same pages uses:

- selected count `ell`;
- selected widths `M^(S_j)`;
- the ceiling integer `M`, called `ceilWidth` in Lean;
- the residue `a`, called `aParam` in Lean;
- the pair sum over `1 <= i < j <= ell+1`;
- the order expression `a(ell-a)+1`.

No quiver-paper input is used.

## Pen-and-paper Calculation

In the equal-width branch, `ell = L` and every selected width is `w`.  There
are `L+1` selected values, so the number of unordered selected pairs is

```text
binom(L+1, 2) = (L+1)L/2.
```

Therefore

```text
sum_{0 <= i < j <= L} m_i m_j
  = ((L+1)L/2) w^2.
```

In Lean's rational-valued pair-sum notation this is

```text
aoyagiSelectedWidthPairSum L (constant w)
  = ((L+1)L w^2) / 2.
```

The previously reproduced ceiling-data calculation gives

```text
ceilWidth = w + q + 1,
aParam    = a.
```

Hence the finite order formula is exactly

```text
aParam * (L - aParam) + 1 = a * (L - a) + 1.
```

Finally, unfolding Lean's ceiling-form definition of the finite Theorem 2
lambda gives

```text
regularTerm
  + a(L-a)/(4L)
  - (L(L-1)/4) * ((w+q+1) + (a-L)/L)^2
  + ((L+1)Lw^2)/4.
```

The last term is half of the selected pair sum, because Aoyagi's displayed
formula uses `pairSum / 2`.

## Lean Shape

Add a reusable pair-sum helper in `FinalFormula.lean`:

```text
aoyagiSelectedWidthPairCount_cast
aoyagiSelectedWidthPairSum_const
```

Then add a source-facing package in namespace
`AoyagiDefinition3SourceData`:

```text
exists_consecutive_equalWidth_theorem2Formula_of_constant_reducedWidth_decomposition
```

It should reuse
`exists_consecutive_explicitCeilData_of_constant_reducedWidth_decomposition`
and additionally return:

```text
data.theorem2OrderFormula = a * (L - a) + 1
aoyagiSelectedWidthPairSum L m = ((L+1)Lw^2)/2
aoyagiTheorem2Lambda_fromCeilData L L H r m data = ...
```

## Nonclaims

- No arbitrary Definition 3 branch-selection theorem.
- No final Theorem 2 socket for arbitrary source data.
- No Eq5 payload, Lemma 5 exactness, active-ratio lower bound, chart count,
  chart production, normal crossings, pole order, or RLCT extraction.
