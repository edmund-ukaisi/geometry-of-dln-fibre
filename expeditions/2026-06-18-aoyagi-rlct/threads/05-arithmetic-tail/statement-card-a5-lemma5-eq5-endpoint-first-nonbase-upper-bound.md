# Statement Card - A5 Lemma 5 Eq5 endpoint first-nonbase upper bound

## Lean Statement

```text
DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.
  terminalMinimumLabels_card_le_of_eq5EndpointChain_firstInteriorNonbase
```

## Claim

For a supplied terminal-candidate family `TC`, explicit Eq5 endpoint-chain
data for every label in `TC.terminalMinimumLabels` give

```text
TC.terminalMinimumLabels.card <= a * (N + 1 - a) + 1
```

provided the deterministic first-nonbase-or-base selector is injective on
`TC.terminalMinimumLabels`.

The selector is

```text
label |-> aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase
           (N + 1) (Hlabel label) TC.family.baseValue.
```

## Hypotheses

- `a <= N+1`;
- selected-width sum
  `sum_i m_i = (N+1)*(M-1)+a`;
- for every terminal-minimum label, an Eq5 piecewise source vector;
- for every terminal-minimum label, the Eq5 terminal-room inequality;
- for every terminal-minimum label, an endpoint chain `Hlabel label` with
  `H_0=m_0`, `H_(N+1)=0`, and agreement with the Eq5 endpoint values;
- injectivity of the deterministic first-nonbase-or-base selector on
  `TC.terminalMinimumLabels`.

## Source Anchor

Aoyagi Lemma 5, PDF pp. 25-27.  The source supports the interval-count shape
and Eq5 endpoint-chain binary increments only under explicit endpoint-chain
and terminal-room data.

## Proof Route

For each terminal-minimum label, the existing Eq5 endpoint-chain theorem gives
binary Lemma 4 increment-prefix deltas from the supplied terminal-room and
endpoint-chain hypotheses.  The existing first-nonbase cardinal theorem then
builds the counted-datum maps-to proof from those binary increments and uses
the supplied selector injectivity to bound the candidate set by the counted
datum codomain.

## Nonclaims

This does not construct `TC.TerminalMinimumCountDatumClassifier` from Aoyagi's
source.  It does not prove selector injectivity, source label construction,
branch-label injectivity, back-to-label coverage, no-extra coverage,
terminal-label exactness, pole order, normal crossings, or RLCT extraction.

## Verification

```text
cd lean && env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.Lemma5Eq5TerminalClassifier
```
