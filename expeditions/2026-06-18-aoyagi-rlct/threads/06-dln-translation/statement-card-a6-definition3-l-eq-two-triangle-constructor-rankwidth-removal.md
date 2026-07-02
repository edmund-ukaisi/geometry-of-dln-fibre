# Statement Card - A6 Definition 3 `L=2` triangle constructor rank-width removal

## Statement

For `L=2`, suppose the three source-range reduced widths have natural
witnesses

```text
aoyagiReducedWidthInt H r 1 = (w1 : Int),
aoyagiReducedWidthInt H r 2 = (w2 : Int),
aoyagiReducedWidthInt H r 3 = (w3 : Int),
```

and satisfy the three triangle inequalities

```text
2*w1 < w1+w2+w3,
2*w2 < w1+w2+w3,
2*w3 < w1+w2+w3.
```

Then Lean constructs the all-source selected Definition 3 data and ceiling
datum with consecutive cutpoints, without an explicit caller-supplied
rank-width hypothesis:

```text
exists C m data,
  (forall j, C.cut j = j.val + 1) and
  AoyagiDefinition3SourceData 2 2 H r C and
  m = aoyagiSelectedReducedWidths H r C and
  ...
```

The output records the three selected reduced widths:

```text
m 0 = (w1 : Int),  m 1 = (w2 : Int),  m 2 = (w3 : Int).
```

## Lean Declarations

```text
AoyagiDefinition3SourceData.exists_consecutive_three_widths_selectedReducedWidthCeilData_of_triangle
```

The concrete diagnostic example

```text
AoyagiDefinition3SourceData.exists_consecutive_nonconstant_widths_one_two_two_selectedReducedWidthCeilData
```

now calls this rank-width-free wrapper.

## Dependency

The wrapper delegates to the existing `_rankWidth` constructor after deriving
its rank-width input from:

```text
AoyagiDefinition3SourceData.sourceRangeRankWidth_of_L_eq_two_triangle_widths
```

## Nonclaims

Finite branch-specific Definition 3 arithmetic only: no canonical branch
choice, no branch-independent formula, no Eq5 payloads, no chart production,
no normal crossings, no pole-order theorem, and no RLCT extraction.
