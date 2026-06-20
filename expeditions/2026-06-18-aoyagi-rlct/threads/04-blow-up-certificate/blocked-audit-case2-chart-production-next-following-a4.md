# Blocked audit - Case 2 chart production and next following data

Status: stronger source-chart production claims remain blocked.

Two xhigh scouts audited Aoyagi PDF pp. 19-22 and the current Lean API after
commit `147c7d5`.  Both found that the source supports the displayed local
Case 2 algebra, but not the stronger chart-production or transition claims.

## Source boundary

The PDF displays:

- the Case 2 center and selected chart with pivot `(J+1,J+1)`;
- the printed post-data package and the update `b'_i = u_{S,J+1} b_i`;
- the row/column operations `P`, `Q`, the transported following factor
  `C' = Q^-1 C`, and the cleared block `D'''`;
- prose assertions that the inductive statement continues with `J` increased,
  or advances with `S` increased in terminal branches.

This is enough for finite local block algebra and for carefully named supplied
post-data compatibility.  It is not enough, by itself, for coordinate
production of the next chart family, recurrence data, exponent data, or a
global transition invariant.

## Blocked stronger targets

| Target | Existing Lean support | Missing bridge | Nonclaim |
| --- | --- | --- | --- |
| Chart-produced recurrence post-data | `case2DisplayedSourceChartMap_case2Succ_postData`, weight-update wrappers | A source/Lean construction deriving the entire post-state from coordinates, including old-level preservation, new-label assignment, and gap transport | Do not call the wrapper chart-produced recurrence data. |
| Chart-produced corrected exponent post-data | corrected selected-label constructor and projections | A coordinate/Jacobian derivation of the corrected prefix-minimum vector; the printed PDF vector is not the corrected one | Do not present corrected data as the printed source vector. |
| Successor chart-family boundary at `(S,J+1)` | domain handoff and nonempty next-center lemmas | Construction of chart regularity, transition regularity, coverage, and the selected-entry family for the successor state | Do not derive a successor chart family from the continuation sentence alone. |
| Full source-produced next `C'^(S+1)` or following product | lower-tail identity for `Q^-1 C`; terminal-last split identities | A source-produced full next matrix in all continuing and terminal branches, including old top rows and suffix handling | Do not identify the tail with the full next `C'^(S+1)`. |
| Transition invariant | local product identities plus corrected supplied post-data packages | Global invariant, atlas coverage, regular transitions, Jacobian arithmetic, normal crossings, and printed-vector repair | Do not name a theorem as a transition invariant unless these caveats are in the statement. |

## Safe next theorem

The safe Lean support theorem is only the continuing-branch adapter

```text
case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_nextSameStageProduct_sourceFollowingFactor
```

plus the supplied-boundary and concrete corrected-post-data projections.  It
rewrites the already-proved post-pivot next-block product using the already
proved lower-tail identity

```text
case2DisplayedPostPivotFollowingFactor =
  case2SourceFollowingFactor (J := J+1).
```

This removes a nuisance adapter while preserving the boundary that chart
production remains supplied or blocked.

## Next route

Future work has two honest routes:

- build an independent selected-entry atlas/transition construction, with
  regularity and coverage, rather than reading it out of Aoyagi's prose; or
- keep the current supplied-boundary interface and continue proving finite
  algebraic consequences beneath that boundary.
