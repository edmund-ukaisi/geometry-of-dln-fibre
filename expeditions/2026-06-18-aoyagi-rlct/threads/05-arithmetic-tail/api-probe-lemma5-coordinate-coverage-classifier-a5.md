# API Probe - Lemma 5 coordinate coverage classifier

Probe: Lovelace, xhigh-effort subagent.
Date: 2026-06-21.

Files inspected: `Lemma5DisplayedVector.lean`, `Lemma5SuppliedFamily.lean`,
and `Lemma5TerminalBridge.lean`.

## Recommended Next Slice

Add a generic assembly theorem in `Lemma5SuppliedFamily.lean`: if each
interior coordinate has a supplied raw branch set whose value image is the
full same-coordinate interval, then filtering out the supplied base value gives
an `AoyagiLemma5SuppliedNonbaseFamily`.

Suggested shape:

```text
AoyagiLemma5SuppliedNonbaseFamily.ofCoordinateValueCoverage
```

Inputs:

- `rawBranches : Nat -> Finset beta`
- `value : beta -> Int`
- `baseValue : Nat -> Int`
- base-value membership in each same-coordinate interval
- value-image coverage of the full same-coordinate interval at each interior
  coordinate
- value-injectivity on each raw branch set
- cross-coordinate disjointness of raw branch sets

The constructor should define the nonbase branch set at coordinate `j` by
filtering out branches whose value is the base value.

A useful helper:

```text
(s.filter fun b => f b != y).image f = (s.image f).erase y
```

## Counted-Datum Classifier Bridge

Add a bridge near `AoyagiLemma5CountDatumClassifier`:

```text
AoyagiLemma5SuppliedNonbaseFamily.countDatumClassifierOfBranchCoord
```

Given a coordinate function `branchCoord : beta -> Nat`, a proof that every
branch in `F.branches j` has coordinate `j`, and supplied injectivity of the
tagged classifier

```text
none      |-> none
some b    |-> some (branchCoord b, F.value b)
```

on `F.fullBranches`, construct an `AoyagiLemma5CountDatumClassifier` for the
full branch set.

## Boundary

The existing equation `(3)`/`(4)`/`(5)` coverage in
`Lemma5DisplayedVector.lean` is one-coordinate and rising-region only.  It can
feed coordinate-by-coordinate value-image hypotheses, but it cannot honestly
construct a full supplied nonbase family for every interior coordinate without
extra supplied coverage for plateau/falling coordinates.

No change is needed in `Lemma5TerminalBridge.lean`; it already has the
terminal upper-bound wrapper once a classifier/no-extra boundary is supplied.

## Risks

The missing supplied data remain full-coordinate coverage, base-value
membership, branch injectivity, and cross-coordinate disjointness.  The Eq5
offset set is currently formula-level; actual Eq5 branch certificates would
need a separate displayed-vector lemma equating their value image with
`aoyagiLemma5Eq5OffsetValueSet`.
