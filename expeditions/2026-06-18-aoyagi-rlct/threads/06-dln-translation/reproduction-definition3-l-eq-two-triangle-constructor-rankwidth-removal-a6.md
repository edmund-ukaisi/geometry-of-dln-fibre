# Reproduction - Definition 3 `L=2` triangle constructor rank-width removal

Date: 2026-07-02.

Status: pen-and-paper reproduction completed and formalised.

## Question

The existing all-source three-width triangle constructor

```text
exists_consecutive_three_widths_selectedReducedWidthCeilData_of_triangle_rankWidth
```

requires a separate source-range rank-width input

```text
hr : forall s, 1 <= s -> s <= 3 -> r <= H s.
```

Can this input be derived from the same natural-width triangle data already
passed to the constructor?

Answer: yes.  The branch-specific theorem

```text
sourceRangeRankWidth_of_L_eq_two_triangle_widths
```

already proves exactly this rank-width hypothesis from the natural reduced
width identities and the three triangle inequalities.

## Calculation

Assume natural witnesses

```text
aoyagiReducedWidthInt H r 1 = (w1 : Int),
aoyagiReducedWidthInt H r 2 = (w2 : Int),
aoyagiReducedWidthInt H r 3 = (w3 : Int),
```

and triangle inequalities

```text
2*w1 < w1+w2+w3,
2*w2 < w1+w2+w3,
2*w3 < w1+w2+w3.
```

The earlier finite arithmetic theorem converts these inequalities into the
all-source strict selected inequality and then invokes the general
all-selected rank-width theorem.  Therefore

```text
forall s, 1 <= s -> s <= 3 -> r <= H s
```

is available without a separate caller input.

Passing that derived hypothesis to the existing `_rankWidth` constructor gives
the same output:

```text
exists C m data,
  C.cut j = j.val + 1,
  AoyagiDefinition3SourceData 2 2 H r C,
  m = aoyagiSelectedReducedWidths H r C,
  m 0 = w1, m 1 = w2, m 2 = w3,
  ...
```

The concrete `(1,2,2)` nonconstant-width example should therefore call the new
rank-width-free wrapper and no longer manufacture a local `hr`.

## Source Boundary

This is finite Definition 3 arithmetic for Aoyagi PDF pp. 8-9.  It uses only
the already-formalised all-source strict inequality and rank-width lemmas in
the Aoyagi Definition 3 bridge.  It does not use quiver results and does not
touch analytic chart production.

## Nonclaims

This is not arbitrary Definition 3 source-data existence, not branch
selection, not branch independence, not Eq5 construction, not chart
production, not normal crossings, not pole order, and not RLCT extraction.
