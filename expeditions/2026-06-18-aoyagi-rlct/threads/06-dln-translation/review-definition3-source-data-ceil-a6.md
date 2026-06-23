# Review - A6 Definition 3 source-data ceiling

Date: 2026-06-23.

Reviewer: xhigh read-only scout `Kant`.

## Verdict

Qualified pass after source-data correction.

The generic ceiling/residue construction is mathematically sound for arbitrary
integer selected sums.  Lean's integer Euclidean division gives

```text
T = T % e + e*(T/e),      0 <= T % e < e
```

for `e > 0`.  The zero-remainder case correctly sets `a = ell`; the nonzero
case correctly sets `a = T % e`.

## Source-Fidelity Correction

The first draft of `AoyagiDefinition3SourceData` was not an exact source-shaped
package: it omitted the displayed dominance condition and used an index-level
nonselected predicate.  Aoyagi's Definition 3 conditions are value-level, using
membership in the selected value set `M`.

The Lean wrapper has therefore been corrected to record:

- selected cutpoints bounded by `L+1`;
- selected strict inequalities;
- value-level selected dominance for widths whose value is not in the selected
  value set;
- value-level nonselected inequalities for widths whose value is not in the
  selected value set.

The theorem `AoyagiDefinition3SourceData.exists_ceilData` itself uses only
`ell_pos` to construct the ceiling datum and carries `selected_strict` forward.
It still does not construct selected cutpoints.

## Remaining Caveats

- No existence or uniqueness of selected cutpoints.
- No proof that the selected value set exists for arbitrary width data.
- No downstream use of the nonselected inequalities yet.
- No normal crossings, pole order, or RLCT extraction.
