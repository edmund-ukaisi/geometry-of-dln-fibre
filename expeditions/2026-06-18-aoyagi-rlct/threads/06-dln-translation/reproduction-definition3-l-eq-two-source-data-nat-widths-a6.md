# Reproduction - Definition 3 `L=2` Source-Data Nat Widths

Date: 2026-07-02.

Status: controller reproduction; implemented and reviewed.

## Question

The landed theorem

```text
AoyagiDefinition3SourceData.exists_L_eq_two_theorem2Formula_branchDisjunction_of_sourceData
```

turns `L=2` Definition 3 source-data existence into a disjunction of finite
Theorem 2 branch packages, but it still asks the caller to supply natural
widths `w1,w2,w3` with

```text
aoyagiReducedWidthInt H r 1 = w1,
aoyagiReducedWidthInt H r 2 = w2,
aoyagiReducedWidthInt H r 3 = w3.
```

This slice checks that those natural witnesses follow from the same supplied
source-data existence.

## Source Anchors

Aoyagi Definition 3 on PDF pp. 8-9 supplies selected/nonselected reduced-width
inequalities.  The existing Lean classification

```text
exists_sourceData_iff_repeatedPositive_or_triangle_of_L_eq_two
```

is the formal finite reproduction for `L=2`: source-data existence is
equivalent to either:

- a repeated-positive branch, where all three source reduced widths are
  positive and two values repeat; or
- an all-source triangle branch, where the three strict inequalities

```text
2*x < x+y+z,   2*y < x+y+z,   2*z < x+y+z
```

hold for the three source-range reduced widths.

## Pen-and-paper Derivation

Let

```text
S : AoyagiDefinition3SourceData 2 ell H r C.
```

Apply the `L=2` classification to `exists ell C, S`.

In the repeated-positive branch, positivity is part of the classification:

```text
0 < x, 0 < y, 0 < z.
```

Hence every source-range reduced width is nonnegative, so

```text
r <= H(s)
```

for `s=1,2,3`.

In the triangle branch, write the three reduced widths as `x,y,z`.  From

```text
2*y < x+y+z,   2*z < x+y+z
```

we get

```text
y < x+z,       z < x+y.
```

Adding gives

```text
y+z < 2*x+y+z,
```

so `0 < x`.  The same cyclic argument gives `0 < y` and `0 < z`.  Again each
reduced width is nonnegative, hence `r <= H(s)`.

With rank-width in hand, set

```text
w1 = H(1)-r,   w2 = H(2)-r,   w3 = H(3)-r.
```

Then the existing reduced-width rewrite gives the three Nat-valued identities
needed by the branch-disjunction theorem.

## Lean Shape

Add in namespace `AoyagiDefinition3SourceData`:

```text
sourceRangeRankWidth_of_L_eq_two_sourceData
exists_reducedWidthNatTriple_of_L_eq_two_sourceData
exists_L_eq_two_theorem2Formula_branchDisjunction_of_sourceData_natWidths
```

The final theorem should existentially return `w1,w2,w3`, the three Nat-width
identities, and the same existing branch disjunction.  It must remain a
disjunction: the source does not choose a canonical branch and the overlap
diagnostics show branch-independent lambda/order payloads are unsafe.

## Nonclaims

- No generalization to `L > 2`.
- No canonical branch choice, uniqueness, or branch agreement.
- No Eq5 payload, chart production, normal crossings, or analytic
  pole-order/RLCT extraction.
