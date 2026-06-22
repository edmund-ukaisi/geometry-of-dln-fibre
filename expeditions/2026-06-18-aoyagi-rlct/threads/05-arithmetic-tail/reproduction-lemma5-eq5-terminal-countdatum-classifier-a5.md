# Reproduction - Lemma 5 Eq5 terminal counted-datum classifier

Status: reproduced; Lean checked; supplied terminal-minimum classifier
adapter.

## Source Boundary

The terminal bridge already defines a supplied terminal-candidate family and
the terminal-minimum counted-datum classifier type

```text
TC.TerminalMinimumCountDatumClassifier.
```

This slice supplies that classifier from Eq5 own-block payload data for each
label already in `TC.terminalMinimumLabels`.  It does not prove that every
terminal-minimum label has such Eq5 data from Aoyagi's printed equations; the
Eq5 payload data and classifier injectivity are hypotheses.

## Calculation

For a terminal-minimum label `label = (S,k)`, define

```text
classify(label) = some (pOf label, T label S).
```

Since `label ∈ TC.terminalMinimumLabels`, the membership theorem gives

```text
introducedLabel L width Sfinal Jfinal label.1 label.2.
```

Unfolding `introducedLabel` gives the state comparison needed by the Eq5
common-domain payload:

```text
label.1 < Sfinal
or
label.1 = Sfinal and label.2 <= Jfinal.
```

The supplied Eq5 data for `label` gives:

- an Eq5 piecewise source vector;
- own-block membership `cut.block (pOf label) label.1`;
- last-point source range;
- selected-width bound, or a source-shaped route deriving it;
- label formula for `label.2`;
- nonbase inequality.

The Eq5 common-domain payload proves

```text
some (pOf label, T label label.1)
  in aoyagiLemma5CountDatumSet (N+1) a M m TC.family.baseValue.
```

This is the `mapsTo` field of `TC.TerminalMinimumCountDatumClassifier`.
The `injOn` field is the supplied injectivity of `classify` on
`TC.terminalMinimumLabels`.

## Lean Targets

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_widthBound
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_blockWidth
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_leftEndpointMin
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_offSelected
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_offSelected_lt
```

## Kill Conditions

- Do not derive Eq5 payload data for terminal-minimum labels.
- Do not derive classifier injectivity.
- Do not derive the nonbase inequality.
- Do not build a back-to-label map or `UpperBoundClassifier`.

## Nonclaims

No Eq5 branch construction, no proof that all terminal-minimum labels have Eq5
own-block witnesses, no source-derived injectivity, no back-to-label map, no
`UpperBoundClassifier`, no exactness, no Lemma 5 order count, no pole order,
no normal crossings, and no RLCT extraction is proved here.
