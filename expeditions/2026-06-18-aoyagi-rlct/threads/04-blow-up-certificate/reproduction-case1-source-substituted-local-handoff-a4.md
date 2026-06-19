# A4 Case 1(2) Source-Substituted Local Handoff

Status: reproduced the source-facing combination of the selected-old source
substitution boundary with the displayed row-strip local handoff.

## Source Situation

The previous local handoff wrote the left row-weight diagonal as

```text
monomialRec (mulStepAt factoredBase.step u (J+J1)).
```

This was already the correct source recurrence after applying the hidden old
substitution `old = u * old'`, but it did not name a substituted source
recurrence state.

The selected-old substitution boundary supplies such a state `source`, under
explicit same-domain factorisation data. After the first-jump hypotheses
identify the selected old-label level with `J+J1`, and after the local level
map is identified with `factoredBase.level`, the supplied source recurrence
satisfies

```text
source.step = mulStepAt factoredBase.step u (J+J1).
```

Here `source` is the pulled-back recurrence after the selected-old
substitution, not the raw pre-chart coordinate recurrence.

## Pen-And-Paper Calculation

The displayed local handoff proves a `Q/P` source-order identity with left
diagonal, for a displayed residual-row index `rho`,

```text
b_rho^source =
  monomialRec (mulStepAt factoredBase.step u (J+J1))
    (case2ResidualRowLevel rho).
```

The selected-old substitution boundary, together with first-jump level
identification, proves that for every source row level `r`,

```text
monomialRec (mulStepAt factoredBase.step u (J+J1)) r
  = monomialRec source.step r
  = source.weight r.
```

Substituting this equality into the local handoff gives the same displayed
top-left source-order identity with left diagonal directly expressed as

```text
source.weight (case2ResidualRowLevel rho).
```

The right diagonal remains supplied post-state weights. No new chart or
post-data production is introduced.

## Lean Boundary

Lean now proves

```text
Case1DisplayedRowStripSuppliedTransitionBoundary.sourceOrder_identity_substitutedSourceWeights
```

from:

- the supplied displayed row-strip transition boundary;
- supplied selected-old factored-base data;
- an explicit equality identifying the boundary's exponent/level map with
  `factoredBase.level`;
- a supplied normalized displayed pivot block.

## Caveats

- This is still a supplied local handoff.
- This does not prove that `source` is produced by a chart.
- This does not construct the selected-old chart or factored-base state.
- This does not identify the hidden old label behind the `Unit` generator.
- This does not prove chart coverage, regularity, Jacobian accounting, normal
  crossings, or RLCT extraction.
