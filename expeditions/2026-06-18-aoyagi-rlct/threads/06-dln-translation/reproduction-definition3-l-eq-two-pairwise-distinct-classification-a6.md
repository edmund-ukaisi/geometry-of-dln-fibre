# Reproduction - Definition 3 `L=2` pairwise-distinct classification

Status: xhigh checked; formalised.

## Source Shape

This isolates Aoyagi Definition 3 in the smallest nontrivial source range:

```text
L = 2,    source layers s = 1,2,3.
```

Write the three reduced widths as

```text
w_s = H(s) - r
```

or, in Lean's integer notation,

```text
w_s = aoyagiReducedWidthInt H r s.
```

Assume source-range rank-width nonnegativity

```text
r <= H(s)        for s=1,2,3
```

and pairwise distinct reduced widths

```text
w_1 != w_2,    w_1 != w_3,    w_2 != w_3.
```

The rank-width hypothesis is not needed for the final all-source constructor,
but it is needed to use the existing `ell=1` obstruction theorem, whose proof
uses nonnegativity of the reduced widths.

## Step 1: possible values of `ell`

A Definition 3 selected-cutpoint record has `ell+1` strictly increasing
positive cutpoints, and source data records each cutpoint as at most `L+1=3`.
Therefore

```text
1 <= C.cut 0 < C.cut 1 < ... < C.cut ell <= 3.
```

So `ell+1 <= 3`, hence `ell <= 2`.  Definition 3 also has `ell > 0`, so

```text
ell = 1  or  ell = 2.
```

## Step 2: exclude `ell=1`

For `ell=1`, there are exactly two selected cutpoints.  The existing Lean
theorem

```text
AoyagiDefinition3SourceData.reducedWidth_mem_selectedValueSet_of_ell_eq_one_rankWidth
```

says that, under source-range rank-width nonnegativity, every source-range
reduced-width value lies in the selected value set.

But with `L=2`, two selected cutpoints are two distinct elements of
`{1,2,3}`.  One source position is missing.  Since the three reduced widths are
pairwise distinct, the missing source value cannot equal either selected
source value.  Thus the missing value cannot lie in the selected value set.

This contradicts the `ell=1` theorem.  Therefore

```text
ell = 2.
```

## Step 3: cutpoints for `ell=2`

Now there are three strictly increasing positive cutpoints, all at most `3`:

```text
1 <= C.cut 0 < C.cut 1 < C.cut 2 <= 3.
```

Hence they are forced:

```text
C.cut 0 = 1,    C.cut 1 = 2,    C.cut 2 = 3.
```

Equivalently, for every `j : Fin 3`,

```text
C.cut j = j.val + 1.
```

## Step 4: remaining Definition 3 condition

With `ell=2` and the forced cutpoints `1,2,3`, every source-range
reduced-width value lies in the selected value set.  Hence the value-level
nonselected clauses in the Lean Definition 3 structure are vacuous.  The
selected strict inequalities are exactly

```text
2*w_1 < w_1+w_2+w_3,
2*w_2 < w_1+w_2+w_3,
2*w_3 < w_1+w_2+w_3.
```

Thus, under pairwise distinct reduced widths and rank-width nonnegativity,
existence of Definition 3 source data for `L=2` is equivalent to the all-source
strict selected inequalities.

## Lean Targets

Add to `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`:

```text
AoyagiDefinition3SourceData.ell_eq_two_of_L_eq_two_rankWidth_pairwiseDistinct
AoyagiDefinition3SourceData.cut_eq_consecutive_of_L_eq_two
AoyagiDefinition3SourceData.exists_sourceData_iff_allSourceStrict_of_L_eq_two_rankWidth_pairwiseDistinct
```

The last theorem should state:

```text
(exists ell C, AoyagiDefinition3SourceData 2 ell H r C)
  iff
(forall s, 1 <= s -> s <= 3 ->
  2 * aoyagiReducedWidthInt H r s
    < sum j : Fin 3, aoyagiReducedWidthInt H r (j.val+1)).
```

## Nonclaims

- This is only the `L=2` pairwise-distinct finite classification.
- It does not classify repeated-width profiles.
- It does not repair Definition 3 for arbitrary profiles.
- It does not compute `ceilWidth` or `aParam`.
- It does not construct Eq5 payloads, charts, source production, pole order,
  or RLCT.

## Check

xhigh checker `Maxwell the 3rd` passed the reproduction after requiring the
final theorem to keep `hr` and pairwise distinctness explicit, and to phrase
the nonselected clause value-theoretically rather than position-theoretically.
The Lean targets follow that shape.
