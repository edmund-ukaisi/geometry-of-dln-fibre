# Reproduction - Lemma 5 Eq5 endpoint-family cardinal squeeze

Date: 2026-06-22.

Scope: terminal exactness/cardinality wrapper that replaces the abstract
terminal branch-coordinate hypothesis by an explicit equality between the
terminal family's nonbase supplied family and the strictest Eq5 endpoint
constructor.  This is still a supplied terminal-candidate theorem, not a
source-backed Lemma 5 order count.

## Inputs Already Available

The previous terminal cardinal-squeeze wrapper proves exactness and the
finite cardinality

```text
TC.terminalMinimumLabels.card = a * (N+1-a) + 1
```

from:

```text
terminal Eq5 payloads on TC.terminalMinimumLabels,
terminal (p, alpha) injectivity,
branchCoord b = j for b in TC.family.branches j,
TC.branchS (some b) = cut.point (branchCoord b) - 1,
TC.family.value b = (TC.branchK (some b) : Z) - 1,
the terminal endpoint base label.
```

The new endpoint-to-terminal adapter proves the branch-coordinate input from
the explicit equality

```text
TC.family.toAoyagiLemma5SuppliedNonbaseFamily =
  ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord ...
```

together with the endpoint constructor's supplied component-coordinate facts.

## Composition

Use the endpoint-family equality to derive the selected-block input via

```text
branchBlock_of_toNonbase_eq_eq5EndpointCoverage_leftEndpoint.
```

Use the supplied `branchK`/value relation to derive the value-label input via

```text
valueLabel_of_branchK_value.
```

Then apply the existing value-label/pAlpha terminal cardinal-squeeze route and
keep every other terminal hypothesis unchanged.  The resulting wrappers have a
clearer supplied-family interface for future endpoint-instantiated terminal
candidates.

## Lean Targets

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5EndpointFamily_branchCoordVal_cardSqueeze
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5EndpointFamily_branchCoordVal_cardSqueeze
```

## Nonclaims

- No Eq5 branch construction.
- No source production of endpoint records.
- No source-label legality.
- No base-filter survival for source records.
- No proof of the family equality from Aoyagi's source.
- No source proof of terminal Eq5 payload coverage.
- No source proof of terminal `(p, alpha)` injectivity.
- No direct counted-datum back-to-label construction.
- No source-backed no-extra terminal-minimum coverage.
- No Lemma 5 order count, pole order, normal crossings, or RLCT extraction.
