# Reproduction - Case 2 Source-Production Obligation Actual-Width Cterm Frontier

Date: 2026-06-22.

Status: finite supplied-obligation consumer.  This is not source production.

## Source Boundary

In Aoyagi Case 2, the actual-width stopped branch is the boundary where

```text
n(S+1) = J+1.
```

At this boundary there is no next post-pivot same-stage row range.  The
existing Lean obligation already exposes two supplied facts:

```text
ob.actualWidth_frontier hwidth
ob.actualWidth_Cterm_eq hwidth
```

where the first gives the actual-width source-chart frontier with terminal
factor

```text
case2DisplayedSourceTerminalOriginalRows C
```

and the second identifies the supplied terminal matrix:

```text
Cterm = case2DisplayedSourceTerminalOriginalRows C.
```

## Finite Rewrite

Specialize the actual-width frontier to the actual source suffix

```text
sourceSuffixProduct κ Ctail S hSuffix.
```

The terminal side has the form

```text
(case2DisplayedSourceTerminalWeight ... *
  case2DisplayedSourceTerminalOriginalRows C) *
sourceSuffixProduct κ Ctail S hSuffix.
```

Using the supplied equality

```text
case2DisplayedSourceTerminalOriginalRows C = Cterm
```

rewrite only this terminal factor.  The finite center principalization,
level-invariant payload, and exponent-certificate payload are unchanged.

## Lean Targets

```text
Case2DisplayedSuppliedChartFamilyBoundary.ActualWidthSourceSuffixSuppliedCtermPayload
Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.actualWidth_frontier_suppliedCterm
```

## Nonclaims

This does not construct `Cterm`, `Csucc`, `C'^(S+1)`, source suffixes,
successor charts, chart coverage, transition regularity, coordinate post-data,
Jacobian arithmetic, normal crossings, pole order, termination, RLCT, or a
repair of the printed Case 2 vector.
