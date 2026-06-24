# Review - Definition 3 all-source selected ceiling data

Reviewer: xhigh `Anscombe the 3rd`.

Status: passed.

## Verdict

The slice is mathematically valid and non-redundant.  It is an API/provenance
step, not new arithmetic.

The previous theorem
`AoyagiDefinition3SourceData.exists_consecutive_of_all_selected_strict`
constructs the consecutive all-source cutpoints and source data.  The generic
package
`AoyagiDefinition3SourceData.exists_selectedReducedWidthCeilData_of_rankWidth`
then turns any such source data plus source-range rank-width into the selected
reduced-width family and Definition 3 ceiling datum.  Combining them is useful
because it removes a repeated supplied source-data hypothesis from the
all-source lane.

## Required Shape

Keep the source-range rank-width hypothesis explicit:

```text
forall s, 1 <= s -> s <= L+1 -> r <= H s.
```

The strict all-source selected inequality alone does not imply rank-width
nonnegativity.  The theorem should not state any closed form for `ceilWidth` or
`aParam`; the general ceiling datum is the Euclidean-division datum already
constructed by the existing generic package.

## Nonclaims

The theorem does not prove rank-width from matrix/source-rank data, arbitrary
selected-cutpoint existence, a classification of Definition 3, closed-form or
unique ceiling data, Eq5 payloads, finite exponent formula equalities, chart
production, pole order, or RLCT extraction.
