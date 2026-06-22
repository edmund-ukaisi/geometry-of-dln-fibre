# Reproduction - Lemma 5 Eq5 endpoint-to-terminal branch coordinates

Date: 2026-06-22.

Scope: finite interface alignment between the strictest supplied Eq5 endpoint
family and a supplied terminal-candidate family.  This is not a source
construction of Eq5 branches, endpoint records, source labels, or terminal
minimum coverage.

## Family Equality Boundary

Let `TC` be a supplied terminal-candidate family.  Its nonbase branch data are
the nonbase part of `TC.family`:

```text
TC.family.toAoyagiLemma5SuppliedNonbaseFamily.
```

Let `F_endpoint` be the already formalized strictest endpoint constructor

```text
ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord
```

formed from supplied strict Eq5 alpha branches, supplied upper/lower endpoint
records, supplied base values, supplied alpha-domain coverage, supplied
endpoint value formulas, supplied strict alpha injectivity, and supplied
component-coordinate facts.

Assume explicitly:

```text
TC.family.toAoyagiLemma5SuppliedNonbaseFamily = F_endpoint.
```

This is the entire bridge.  It says that the terminal family's nonbase branch
sets are the endpoint constructor's filtered branch sets.  It does not prove
that Aoyagi's printed equations produce those sets.

## Coordinate Transport

For an interior terminal coordinate `j in Icc 1 N`, the same index is an
interior endpoint coordinate for `ell = N+1`:

```text
j in Icc 1 ((N+1)-1).
```

Given `b in TC.family.branches j`, the family equality rewrites this membership
as

```text
b in F_endpoint.branches j.
```

The endpoint coverage file already proves coordinate correctness for this
strictest constructor:

```text
branchCoord b = j.
```

Therefore the terminal nonbase branch-coordinate hypothesis needed by the
terminal branch-label injection wrappers follows from the family equality and
the endpoint constructor's supplied component-coordinate facts.

## Selected-Block Adapter

If, in addition, the terminal source label satisfies the supplied left-endpoint
formula

```text
TC.branchS (some b) = cut.point (branchCoord b) - 1,
```

then the existing `branchBlock_of_branchCoord_leftEndpoint` adapter gives

```text
cut.block j (TC.branchLabel (some b)).1.
```

This is still a terminal-family interface theorem.  The `branchS` formula is
not derived from Aoyagi's source here.

## Lean Targets

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.branchCoord_of_toNonbase_eq_eq5EndpointCoverage
AoyagiLemma5SuppliedTerminalCandidateFamily.branchBlock_of_toNonbase_eq_eq5EndpointCoverage_leftEndpoint
```

## Nonclaims

- No Eq5 branch construction.
- No source production of endpoint records.
- No source-label legality.
- No base-filter survival theorem for a source record.
- No terminal Eq5 payload coverage.
- No terminal `(p, alpha)` injectivity.
- No direct counted-datum back-to-label construction.
- No source-backed no-extra terminal-minimum coverage.
- No Lemma 5 order count, pole order, normal crossings, or RLCT extraction.
