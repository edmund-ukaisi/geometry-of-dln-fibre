# Reproduction - Lemma 5 Eq5 terminal order formula bridge

Date: 2026-06-23.

Status: finite A5 handoff under the already supplied Eq5 endpoint-family
payloads.  This note does not repair the source-backed Lemma 5 exactness
obstruction.

## Existing Exact Count

The existing Eq5 block-width cardinal-squeeze theorem proves

```text
TC.terminalMinimumLabels.card = a * (N + 1 - a) + 1
```

from the supplied terminal Eq5 payloads, endpoint-family equality, blockwise
actual-width dominance, source selected inequality, terminal label block data,
terminal `(p, alpha)` injectivity, branch-coordinate formulas, and base-label
formula.  Those hypotheses are all still supplied at this boundary.

## Definition 3 Specialization

Now specialize the terminal candidate family to

```text
a = data.aParam
M = data.ceilWidth
ell = N + 1
```

for

```text
data : AoyagiDefinition3CeilData (N + 1) m.
```

The two Eq5 exact-count inputs

```text
a <= N + 1
sum_i m_i = (N + 1) * (M - 1) + a
```

are exactly `data.aParam_le` and `data.selectedSum_eq`.

By definition,

```text
data.theorem2OrderFormula =
  data.aParam * ((N + 1) - data.aParam) + 1.
```

Therefore the exact Eq5 terminal-minimum count rewrites to

```text
TC.terminalMinimumLabels.card = data.theorem2OrderFormula.
```

## Lean Target

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze
```

## Nonclaims

- No source construction of Eq5 endpoint families.
- No source proof of terminal Eq5 payload coverage.
- No source proof of terminal `(p, alpha)` injectivity.
- No source proof of the endpoint-family equality.
- No source proof of branch-label injectivity or no-extra coverage.
- No counted-datum classifier or back-to-label construction.
- No pole order, normal crossings, or RLCT extraction.
