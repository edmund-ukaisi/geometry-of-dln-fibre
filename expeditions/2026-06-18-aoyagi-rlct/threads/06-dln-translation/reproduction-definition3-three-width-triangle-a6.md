# Reproduction - Definition 3 three-width triangle constructor

Status: xhigh checked; formalised.

## Source Shape

This is a source-facing specialisation of Aoyagi Definition 3 to the smallest
nontrivial all-source case.  Take `L=2`, so the source range has three reduced
widths

```text
w_1 = M^(1) - r,    w_2 = M^(2) - r,    w_3 = M^(3) - r.
```

In Lean these are the integer reduced widths

```text
aoyagiReducedWidthInt H r 1 = w1,
aoyagiReducedWidthInt H r 2 = w2,
aoyagiReducedWidthInt H r 3 = w3.
```

Select every source layer:

```text
ell = L = 2,
C.cut j = j.val + 1      for j : Fin 3.
```

## Definition 3 Calculation

The selected sum is

```text
w_1 + w_2 + w_3.
```

Since `ell=2`, Definition 3's selected strict inequalities are exactly

```text
2*w_1 < w_1 + w_2 + w_3,
2*w_2 < w_1 + w_2 + w_3,
2*w_3 < w_1 + w_2 + w_3.
```

These are the strict triangle-type inequalities saying that no chosen width is
at least the sum of the other two.  Under these three inequalities, the
all-source selected strict hypothesis required by the existing constructor
holds for every source index `s=1,2,3`.

The nonselected clauses in Definition 3 are vacuous in the all-source
selection: every source-range reduced-width value occurs as a selected value.
The downstream selected-width ceiling package still needs rank-width
nonnegativity, so we keep the explicit source-range hypothesis

```text
forall s, 1 <= s -> s <= 3 -> r <= H s.
```

With that hypothesis, the existing all-source strict/rank-width package
produces consecutive cutpoints, `AoyagiDefinition3SourceData 2 2 H r C`,
selected reduced widths `m`, and a Definition 3 ceiling datum.  The output
also records

```text
m 0 = w_1,    m 1 = w_2,    m 2 = w_3.
```

## Lean Target

Add to `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`:

```text
AoyagiDefinition3SourceData.exists_consecutive_three_widths_selectedReducedWidthCeilData_of_triangle_rankWidth
```

Then refactor

```text
AoyagiDefinition3SourceData.exists_consecutive_nonconstant_widths_one_two_two_selectedReducedWidthCeilData
```

to use this general three-width constructor with `(w1,w2,w3)=(1,2,2)`.

## Nonclaims

- This is not arbitrary selected-cutpoint/source-data existence.
- This is not a classification of Definition 3 profiles.
- This is not a uniqueness theorem for cutpoints or ceiling data.
- This does not compute closed-form `ceilWidth` or `aParam`.
- This does not construct Eq5 payloads, finite exponent formula facts, charts,
  pole order, or RLCT.

## Check

xhigh reviewer `Chandrasekhar the 3rd` approved the theorem as a correctly
scoped all-source `L=2` constructor.  The focused Lean module check passed.
