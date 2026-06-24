# Review - Definition 3 three-width triangle constructor

Reviewer: xhigh `Chandrasekhar the 3rd`.

Status: passed.

## Verdict

No issues found.

The theorem

```text
AoyagiDefinition3SourceData.exists_consecutive_three_widths_selectedReducedWidthCeilData_of_triangle_rankWidth
```

is correctly restricted to the `L=2`, all-source case.  Its three hypotheses

```text
2*w_i < w1+w2+w3
```

are converted into the all-source selected strict family by enumerating the
source indices `s=1,2,3`, then delegating to
`exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict_rankWidth`.

The all-source nonselected clauses are handled by the existing all-source
constructor: every source-range reduced-width value lies in the selected value
image, so both nonselected fields are vacuous.  This matches the value-level
nonselected condition in the formal Definition 3 source-data structure.

The rank-width hypothesis

```text
forall s, 1 <= s -> s <= 3 -> r <= H s
```

is explicit and is used only downstream for Nat-subtraction rewrites and
nonnegativity in the selected reduced-width ceiling package.

The refactor of

```text
AoyagiDefinition3SourceData.exists_consecutive_nonconstant_widths_one_two_two_selectedReducedWidthCeilData
```

is sound: it calls the new theorem with `(w1,w2,w3)=(1,2,2)` and adds only the
nonconstancy witness `m 0 != m 1`.

## Nonclaims Checked

The theorem does not claim arbitrary source-data existence, Definition 3
classification, analytic chart production, source production, pole order, or
RLCT extraction.

## Verification

The reviewer also checked:

```text
lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
```

from the Lean project root.  The controller independently checked the same
module with `LEAN_NUM_THREADS=1`.
