# Review - A2 selected-entry local source-stratum original-loss bridge

Date: 2026-06-25.

Reviewer: xhigh `Jason`.

## Verdict

Accepted.  No formalisation or mathematical-boundary issues found.

## Checks

The endpoint theorem remains conditional on the explicit local source/image
equality hypothesis:

```text
Ulocal ∩ sourceStratum =
Ulocal ∩ chartMap pivot '' signedBoxSet Rres
```

The proof uses this equality only to identify relative filters near `x0` and
to rewrite restricted measures after shrinking the final open set into
`Ulocal`; it does not prove or imply global source-stratum/chart-image
equality.

The helper lemmas were checked:

- `nhdsWithin_eq_of_mem_nhds_inter_eq` is the standard fact that intersecting
  by a neighborhood does not change `nhdsWithin`, applied to both source sets.
- `restrict_inter_eq_of_subset_inter_eq` first proves the literal set equality
  `U ∩ s = U ∩ t` from `U ⊆ Ulocal` and then rewrites restricted measures.

The final shrink is valid: the proof sets `U = Uchart ∩ Ulocal`, uses
monotonicity to pass finite `lintegral` from `Uchart ∩ chartImage` to
`U ∩ chartImage`, and then uses the local equality inside `Ulocal` to rewrite
the base restricted measure, hence the product measure, to `U ∩ sourceStratum`.

## Build Check

The reviewer also checked the target file with `lake env lean` from the Lean
project root; the file compiled and contained no `sorry`, `admit`, or new
`axiom`.
