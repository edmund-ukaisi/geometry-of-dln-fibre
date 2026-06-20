# A4 Case 2 Source-Chart Terminal Model Constructor

Status: reproduced the constructor-level bridge from the displayed
source-chart boundary to the actual-width terminal relabel model.  This is a
composed supplied-boundary API, not a terminal transition theorem.

## Source Anchor

Aoyagi PDF pp. 20-22 display the top-left Case 2 chart.  The existing Lean
constructor

```text
of_sourceChartMap_case2Succ_updateSelected
```

packages the displayed source-chart pivot value into the concrete recurrence
successor

```text
post = pre.case2Succ(case2DisplayedSourceChartMap(...)(J+1,J+1))
```

and the corrected selected-label exponent update.  The later terminal
source-model wrappers package supplied old-top and suffix data for the stopped
actual-width branch.

## Pen-And-Paper Reproduction

Start with:

- a pre recurrence state over `(S,J)`;
- pre exponent certificates;
- the `leastValue = level` invariant and Case 2 gap;
- supplied chart-family predicates;
- actual next-width exhaustion;
- supplied terminal old-top/suffix data `Atop`, `Ctop`, and `F`.

The displayed source-chart constructor gives a displayed supplied boundary
whose successor recurrence state is the concrete `case2Succ` state and whose
exponent post-data are the corrected selected-label overrides.

The terminal relabel-weight theorem then applies to that boundary.  Its
surviving scalar is the relabelled post-state weight

```text
(pre.case2Succ(case2DisplayedSourceChartMap(...)(J+1,J+1)))
  .stageRelabelSuccZero.weight(J+1).
```

Thus the stopped terminal entry-ideal candidate is available for the concrete
source-chart boundary and a terminal model indexed by that scalar.

## Lean Shape

The public theorem is:

```text
exists_terminalModelEntryIdeal_eq_relabelProductCandidate_of_sourceChartMap_actualWidth
```

The attempted prettier statement with a local `data` value in the theorem type
timed out in Lean, so the accepted statement writes the concrete relabelled
post-state weight directly in the model's `b0` parameter.  This is definitionally
the relabelled weight of the boundary constructed by
`of_sourceChartMap_case2Succ_updateSelected`.

## Boundaries

- `Atop`, `Ctop`, and `F` remain supplied terminal source-model fields.
- The result uses supplied chart-family regularity predicates; it does not
  prove chart coverage or regularity from coordinates.
- The terminal matrix is a candidate, not source-produced `C'^(S+1)`.
- Actual-width exhaustion is required.
- The relabelled recurrence/exponent data are bookkeeping, not an automatic
  terminal transition invariant or gap/tail transport theorem.
- No Jacobian/volume arithmetic, normal crossings, RLCT extraction,
  termination, transition invariant, or printed-vector repair is proved.

## Kill Conditions

- Do not index the terminal model by `post.weight(J+1)` unless `post` is
  definitionally the concrete relabelled source-chart post-state expected by
  the theorem.
- Do not infer source-produced old top rows, remaining suffix, or
  `C'^(S+1)` from this constructor.
