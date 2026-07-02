# Reproduction - Definition 3 `ell=1` Source-Data Rank-Width Removal

Date: 2026-07-02.

Status: controller reproduction; review pending.

## Question

The existing theorem

```text
AoyagiDefinition3SourceData.exists_ell_one_theorem2Formula_of_sourceData_rankWidth_general
```

proves the finite Theorem 2 formula for a supplied

```text
S : AoyagiDefinition3SourceData L 1 H r C,
```

but still asks separately for source-range rank-width:

```text
forall s, 1 <= s -> s <= L+1 -> r <= H s.
```

For `ell=1`, that rank-width input follows from Definition 3 source data
itself.

## Source Anchors

Aoyagi Definition 3 on PDF pp. 8-9 is the source for the selected and
nonselected reduced-width inequalities.  In Lean these clauses are the fields
of `AoyagiDefinition3SourceData`.

When `ell=1`, there are two selected reduced widths

```text
m_0 = M^(S_0),        m_1 = M^(S_1).
```

The strict selected inequalities are

```text
m_0 < m_0 + m_1,
m_1 < m_0 + m_1.
```

The nonselected upper inequality has coefficient `ell-1 = 0`.

## Pen-and-paper Derivation

Let

```text
S : AoyagiDefinition3SourceData L 1 H r C.
```

First, the two strict selected inequalities give positivity of the two
selected values:

```text
m_1 < m_0 + m_1    implies    0 < m_0,
m_0 < m_0 + m_1    implies    0 < m_1.
```

Second, the already-landed lemma

```text
S.reducedWidth_mem_selectedValueSet_of_ell_eq_one
```

shows every source-range reduced width lies in the selected value set.  Thus
for any `s` with `1 <= s <= L+1`, the integer

```text
aoyagiReducedWidthInt H r s = H(s) - r
```

is either `m_0` or `m_1`.  Since both are positive, this reduced width is
nonnegative.

Unfolding the integer reduced width,

```text
0 <= (H(s) : Int) - (r : Int)
```

is equivalent to

```text
r <= H(s).
```

Therefore Definition 3 source data with `ell=1` supplies the whole
source-range rank-width hypothesis.

Finally, applying the existing rank-width theorem with this derived
rank-width gives the same finite formula package:

```text
u = H(C.cut 0) - r,
v = H(C.cut 1) - r,
ceilWidth = u+v,
aParam = 1,
theorem2OrderFormula = 1,
pairSum = u*v,
lambda = regularTerm + u*v/2.
```

## Lean Shape

Add, in namespace `AoyagiDefinition3SourceData`:

```text
sourceRangeRankWidth_of_ell_eq_one
exists_ell_one_theorem2Formula_of_sourceData_general
```

The second theorem should have the same conclusion as
`exists_ell_one_theorem2Formula_of_sourceData_rankWidth_general`, but without
the separate rank-width hypothesis.

## Nonclaims

- No theorem infers `ell=1`; it is supplied in the type of `S`.
- No canonical selected pair is chosen.
- No branch-independent formula is asserted for arbitrary Definition 3 data.
- No Eq5 payload, normal-crossing chart, or analytic pole-order/RLCT
  extraction is constructed.
