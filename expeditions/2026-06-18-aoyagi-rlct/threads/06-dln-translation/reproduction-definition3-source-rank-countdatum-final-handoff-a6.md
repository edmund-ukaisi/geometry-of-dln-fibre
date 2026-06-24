# Reproduction - Definition 3 source-rank counted-datum final handoff

Status: xhigh checked; parked.

This is a proposed A6/A2 handoff.  It is not a new Lemma 5 result and not a
new chart-production result.  It asks whether the newly landed Definition 3
terminal counted-datum classifier final bridge can consume the A2
source-rank-stratum rank-width bridge, so callers do not restate the
source-range rank-width hypothesis separately.

Xhigh review passed the substitution as a thin leaf API, but the controller
parks it for now: the rank-width regular-shift reduction removes duplicated
source-rank provenance at a more central arithmetic boundary.

## Inputs

Fix a chain length `N`, source spaces `W 0, ..., W N`, base edge maps `B`, a
source-rank stratum predicate

```text
x in paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge,
```

and the dimension convention

```text
H(k+1) = finrank(W k)    for k : Fin (N+1).
```

Also fix Definition 3 source data at `L=N`:

```text
Ssrc : AoyagiDefinition3SourceData N (n+1) H r C.
```

The already proved A2/A6 rank-width bridge gives

```text
paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth W B hx hH :
  forall s, 1 <= s -> s <= N+1 -> r <= H s.
```

## Target handoff

For each selected-width family and ceiling datum produced from `Ssrc`, assume
the same payload required by the Definition 3 terminal counted-datum classifier
final bridge:

```text
TC : AoyagiLemma5SuppliedTerminalCandidateFamily ...
classifier : TC.TerminalMinimumCountDatumClassifier
hinj : Set.InjOn TC.branchLabel TC.fullBranches
```

together with supplied A0 finite certificates:

```text
p in activePairs,
ratioAt p = theorem2 lambda from data,
all active ratios are >= that displayed value,
one displayed-ratio chart count equals TC.terminalMinimumLabels.card,
all displayed-ratio chart counts are <= that card.
```

The chart-certificate version replaces the bare exponent data `D` by
`Cnc.exponentData` and the raw extraction hypothesis by
`Cnc.ExtractionHypothesis`.

## Calculation

The existing Definition 3 terminal counted-datum classifier final bridge has
the form:

```text
Ssrc
  + source-range rank-width
  + A0 extraction
  + terminal counted-datum classifier payload for produced m,data
  -> exists m,data, supplied final boundary and selected-width side data.
```

The only missing input in the source-rank setting is the source-range
rank-width hypothesis.  It is supplied by the A2 bridge:

```text
source-rank stratum membership
  + H(k+1)=finrank(W k)
  -> forall s, 1<=s -> s<=N+1 -> r<=H s.
```

Substituting that theorem for the rank-width argument gives the desired
source-rank final handoff:

```text
Ssrc
  + source-rank stratum membership
  + H(k+1)=finrank(W k)
  + A0 extraction
  + terminal counted-datum classifier payload for produced m,data
  -> exists m,data, supplied final boundary and selected-width side data.
```

The chart version is identical after replacing `D` by `Cnc.exponentData`.

## Why this is a source-hypothesis reduction

This proposed wrapper removes a repeated source-range rank-width input from a
final handoff.  The replacement hypothesis is Aoyagi's source-rank-stratum
membership plus the explicit dimension convention already used by the
source-rank final, Eq5, and regular-shift handoffs.

It does not reduce the A5 or A0 obligations.  The counted-datum classifier,
branch-label injectivity, active-ratio lower bound, displayed-ratio chart
count, all-chart upper bound, chart certificate, and extraction hypothesis
remain supplied.

## Nonclaims

- No selected cutpoints or Definition 3 source data are constructed.
- No rank-width fact is proved from arbitrary dimensions; the source-rank
  stratum and dimension convention are required.
- No counted-datum classifier or branch-label injectivity is constructed.
- No active-ratio bound or chart-count theorem is proved.
- No normal-crossing chart certificate, pole-order theorem independent of A0,
  or RLCT theorem is proved.
