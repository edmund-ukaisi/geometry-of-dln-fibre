# Review - A6 Definition 3 `L=2`, `ell=1` selected-pair formula package

Date: 2026-06-24.

Reviewer: xhigh read-only reviewer `Mill the 3rd`.

## Verdict

Pass.  No required changes.

## Fidelity Check

The reviewer checked
`AoyagiDefinition3SourceData.exists_ell_one_selectedPair_theorem2Formula_of_cover_remainder_rankWidth`
against Aoyagi Definition 3 and Theorem 2, PDF pp. 8-9.

The theorem exposes the selected pair `C : AoyagiSelectedCutpoints 1` instead
of hiding it behind a repeated-positive disjunction.  It fixes `ell=1`, uses a
cover by the selected value set, and requires both selected values to be
positive.

## Formula Check

The reviewer accepted the finite projections:

```text
ceilWidth = ceilPred + 1,
aParam = 1,
theorem2OrderFormula = 1,
aoyagiSelectedWidthPairSum 1 m = u*v,
lambda = regularTerm + u*v/2.
```

The simplification is valid because the `ell=1` ceiling-quadratic coefficient
vanishes and the `a*(ell-a)/(4*ell)` term is zero for `a=ell=1`.

## Nonclaim Check

No source-rank wrapper, final socket, canonical repeated-branch formula, Eq5
construction, chart construction, normal-crossing theorem, pole-order theorem,
or RLCT theorem was introduced.
