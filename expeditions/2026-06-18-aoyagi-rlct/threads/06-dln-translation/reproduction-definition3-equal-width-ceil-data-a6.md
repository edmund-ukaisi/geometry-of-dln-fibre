# Reproduction - Definition 3 equal-width ceiling data

Date: 2026-06-24.

Status: pen-and-paper reproduction before Lean.

## Question

The previous equal-width slice constructs Definition 3 source data when every
source-range reduced width is a positive constant `w`, taking `ell = L` and
all consecutive source layers as selected cutpoints.  Existing downstream
theorems still require a separate source-range rank-width hypothesis to turn
source data into selected reduced-width ceiling data.

This slice asks whether the same equal-width hypothesis already proves that
rank-width hypothesis.

## Source Anchors

Aoyagi Definition 3 and the equal-width example on PDF pp. 8-9.  The source
assumption is

```text
M^(1) = M^(2) = ... = M^(L+1) = w
```

with positive width `w`.  In Lean,

```text
aoyagiReducedWidthInt H r s = (w : Int)
```

means

```text
H(s) - r = w
```

as an integer equality.

## Pen-and-paper Calculation

Assume

```text
1 <= s <= L+1  implies  M^(s) = H(s)-r = w
```

for a natural number `w`.  Since `w >= 0`, the equality implies

```text
H(s) - r >= 0.
```

Therefore

```text
r <= H(s)
```

for every source layer `1 <= s <= L+1`.  Thus the constant reduced-width
hypothesis implies the source-range rank-width hypothesis consumed by

```text
AoyagiDefinition3SourceData.exists_selectedReducedWidthCeilData_of_rankWidth.
```

Combining this rank-width consequence with the previous equal-width source-data
constructor gives:

1. consecutive cutpoints `C.cut j = j.val + 1`;
2. `AoyagiDefinition3SourceData L L H r C`;
3. selected reduced-width family

```text
m = aoyagiSelectedReducedWidths H r C;
```

4. a Definition 3 ceiling datum `data`;
5. the standard downstream package: Nat-subtraction rewrites, nonnegativity,
   strict selected inequalities, selected-width upper bounds, and Nat-indexed
   nonnegativity;
6. the extra equal-width fact

```text
forall j, m j = (w : Int).
```

The extra fact follows because every selected cutpoint is a source-range layer
and the source-range reduced width is constant.

## Lean Shape

Add to `Definition3Bridge.lean`, in namespace
`AoyagiDefinition3SourceData`:

```text
AoyagiDefinition3SourceData.sourceRangeRankWidth_of_constant_reducedWidth
```

with statement:

```text
theorem sourceRangeRankWidth_of_constant_reducedWidth
    {L : Nat} {H : Nat -> Nat} {r w : Nat}
    (hconst :
      forall s : Nat, 1 <= s -> s <= L + 1 ->
        aoyagiReducedWidthInt H r s = (w : Int)) :
    forall s : Nat, 1 <= s -> s <= L + 1 -> r <= H s
```

Then add the packaged equal-width ceiling-data constructor:

```text
AoyagiDefinition3SourceData.exists_consecutive_selectedReducedWidthCeilData_of_constant_reducedWidth_pos
```

with hypotheses `0 < L`, `0 < w`, and `hconst`, returning consecutive
cutpoints, the equal-width `AoyagiDefinition3SourceData`, and the selected
reduced-width ceiling-data package with `forall j, m j = (w : Int)`.

## Nonclaims

- No arbitrary selected-cutpoint or Definition 3 source-data existence theorem.
- No explicit closed form for the Definition 3 ceiling integer or residue.
- No Eq5 family construction or Lemma 5 exactness.
- No active-ratio lower bound, chart count, chart production, normal crossings,
  pole order, or RLCT extraction.
