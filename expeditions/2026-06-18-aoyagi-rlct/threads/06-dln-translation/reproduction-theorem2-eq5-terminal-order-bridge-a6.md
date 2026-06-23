# Reproduction - Theorem 2 Eq5 terminal-order bridge

Date: 2026-06-23.

Status: finite A5-to-A6 handoff.  This note does not prove source-backed
Lemma 5 exactness.

## Source Position

Aoyagi's Theorem 2 order formula is the displayed integer

```text
a(ell-a)+1.
```

The Lean notation for this number is `data.theorem2OrderFormula`.  The A5
Eq5 endpoint-family bridge already proves, under a large supplied Eq5 payload,
that the supplied terminal minimum labels have exactly this cardinality:

```text
TC.terminalMinimumLabels.card = data.theorem2OrderFormula.
```

This is a finite cardinality statement.  The payload still includes the Eq5
endpoint family, source vectors, selected-block membership, width dominance,
label formula, endpoint-family equality, terminal injectivity data, and the
terminal branch-label equations.

## Calculation

The A6 exact-count socket asks for the same equality as its final input:

```text
hterminal :
  TC.terminalMinimumLabels.card = data.theorem2OrderFormula.
```

Therefore the new bridge performs only the following composition:

```text
Eq5 endpoint block-width payload
  -> TC.terminalMinimumLabels.card = data.theorem2OrderFormula
  -> existing Theorem 2 exact terminal-count wrapper.
```

For the displayed-ratio chart-final form, the remaining inputs are unchanged:

```text
Cnc.exponentData.ratioAt p =
  aoyagiTheorem2Lambda_fromCeilData L (n+1) H r m data

forall active p',
  aoyagiTheorem2Lambda_fromCeilData L (n+1) H r m data
    <= Cnc.exponentData.ratioAt p'

Cnc.exponentData.countInChartAtRatio
  (aoyagiTheorem2Lambda_fromCeilData L (n+1) H r m data) c
    = TC.terminalMinimumLabels.card

forall charts c',
  Cnc.exponentData.countInChartAtRatio
    (aoyagiTheorem2Lambda_fromCeilData L (n+1) H r m data) c'
      <= TC.terminalMinimumLabels.card.
```

The active-ratio certificate identifies the displayed lambda with the finite
minimum.  The displayed-ratio chart-count certificate identifies the finite
order with `TC.terminalMinimumLabels.card`.  The Eq5 payload then rewrites that
cardinality to `data.theorem2OrderFormula`.

## Lean Shape

The bridge packages the large supplied Eq5 payload in

```text
AoyagiLemma5SuppliedEq5EndpointBlockWidthOrderPayload data TC.
```

The package has the same mathematical inputs as

```text
terminalMinimumLabels_card_eq_theorem2OrderFormula_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze.
```

The first theorem extracts the exact count:

```text
AoyagiLemma5SuppliedEq5EndpointBlockWidthOrderPayload
  .terminalMinimumLabels_card_eq_theorem2OrderFormula
```

The downstream wrappers then feed this exact count into the existing A6
equality bridge.  The final-boundary wrappers use the same selected cutpoints
`P.cut` carried by the supplied Eq5 payload in their selected-width provenance
hypothesis, so the A5 payload and A6 final boundary do not silently drift
apart.

## Nonclaims

- No construction of Eq5 endpoint families.
- No source proof that Aoyagi's printed Eq3/Eq4/Eq5 families cover all
  terminal minima.
- No source-backed Lemma 5 exactness theorem.
- No global normal-crossing chart production or chart coverage.
- No active-ratio lower-bound proof.
- No displayed-ratio chart-count proof.
- No selected cutpoint existence or rank-width proof.
- No Case 1 or Case 2 source-production progress.
- No Aoyagi Lemma 1, Theorem 4, regular-coordinate additivity, or analytic
  ideal-transport citation.
- No pole order or RLCT theorem beyond the explicitly supplied
  normal-crossing extraction hypothesis.
