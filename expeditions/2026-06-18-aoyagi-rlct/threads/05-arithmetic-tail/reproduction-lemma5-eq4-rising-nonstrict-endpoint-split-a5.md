# Reproduction - Lemma 5 Eq4 rising non-strict endpoint split

Date: 2026-06-21.

Scope: endpoint inventory for Aoyagi Lemma 5 equation `(4)` in the rising
range, when the strict endpoint case `p+1<a` fails.

This is a dispatcher over existing boundary facts.  It does not construct an
Eq4 displayed vector or prove source coverage.

## Source Inventory

Aoyagi Lemma 5 equation `(4)` has two relevant endpoint boundaries in Lean's
zero-based notation:

- the special Eq4 boundary index

  ```text
  p + (ell-a) + 1;
  ```

- the repaired selected-index guard

  ```text
  p+1 <= a.
  ```

The strict nonterminal endpoint case is

```text
p+1 < a.
```

The already-formalised facts are:

- if `p+1=a`, the special Eq4 boundary is the terminal selected endpoint;
- if `p=a`, the repaired guard `p+1<=a` fails, so no supplied Eq4 piecewise
  vector of the repaired shape exists;
- in the rising region, Eq5 strict offsets still have the erased-endpoints
  deficit.

## Pen-And-Paper Derivation

Assume the rising-side inequality

```text
p <= a.
```

Failure of the strict case is

```text
not (p+1 < a).
```

For natural numbers this means

```text
a <= p+1.
```

Together with `p<=a`, there are exactly two cases:

```text
p+1 = a
```

or

```text
p = a.
```

The first case is terminal collision.  Under a supplied Eq4 piecewise
certificate, existing Lean theorems give:

```text
C.point (p+(ell-a)+1)-1 = C.point ell-1,
not C.block b (C.point (p+(ell-a)+1)-1) for all b,
T(C.point ell-1)=0 iff W_(ell+1)=M-p+1.
```

The certificate remains supplied.  The statement is conditional on every such
certificate; it is not an existence theorem.

The second case is repaired-guard failure.  Existing Lean theorems give:

```text
p = a,
Eq5Offsets(p) = (HtildeInterval(p).erase upperEndpoint).erase lowerEndpoint,
not AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T.
```

The nonexistence statement is only for the repaired supplied Eq4 piecewise
shape and the fixed parameters shown.

## Lean Targets

```text
aoyagiLemma5Eq4_risingNonStrictEndpoint_iff_predBoundary_or_eq_a
aoyagiLemma5Eq4_boundaryIndex_not_lt_ell_iff_predBoundary_or_eq_a
aoyagiLemma5Eq4_risingNonStrictEndpoint_predBoundary_or_no_piecewiseSourceVector
aoyagiLemma5Eq4TerminalCollisionPayload
aoyagiLemma5Eq4GuardFailurePayload
aoyagiLemma5Eq4_risingNonStrictEndpoint_split
```

## Kill Conditions

- Do not claim `¬ Eq4PiecewiseSourceVector iff p=a`.
- Do not claim Eq4 exists in the `p+1=a` case.
- Do not claim terminal zero in the `p+1=a` case without the last-width
  compatibility condition.
- Do not claim Eq4 fills the lower endpoint at `p=a`.
- Do not infer source-label legality, classifier coverage, injection,
  back-to-label coverage, Lemma 5 order count, pole order, normal crossings,
  or RLCT extraction.
