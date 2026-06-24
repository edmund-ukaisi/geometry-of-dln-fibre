# Review - A6 Definition 3 general `L`, `ell=1` selected-pair formula package

Date: 2026-06-24.

Reviewer: xhigh independent reviewer `Aristotle the 3rd`.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`;
- `reproduction-definition3-ell-one-selected-pair-cover-formula-general-a6.md`;
- `statement-card-a6-definition3-ell-one-selected-pair-cover-formula-general.md`.

Review questions:

- no hidden canonical selected-pair or branch-independent claim;
- arbitrary-`L` source range and regular-term dependence;
- value-level cover against Aoyagi Definition 3's selected value set;
- `ell=1` ceiling, order, pair-sum, and lambda arithmetic;
- nonvacuity and residual hypotheses.

## Findings

No findings.

The theorem keeps the selected pair supplied through `C`, `u`, and `v`.  It
does not select a canonical branch or assert branch independence.  The
value-level cover is exactly the selected-value-set cover used to build
Definition 3 source data, and the arbitrary-`L` dependence is limited to
source-range guards plus `aoyagiTheorem2RegularTerm L H r`.

The `ell=1` arithmetic checks out:

```text
ceilPred = u + v - 1,
ceilWidth = u + v,
aParam = 1,
theorem2OrderFormula = 1,
aoyagiSelectedWidthPairSum 1 m = u*v,
lambda = regularTerm + u*v/2.
```

The reproduction and statement card match these boundaries and avoid
canonical-branch, Eq5, chart, pole-order, or RLCT claims.

## Verification

Reviewer verification:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
```

passed.

## Residual Boundary

The theorem is conditional on a supplied selected pair and value-level cover;
it does not construct such a pair.  For impossible edge cases such as `L=0`,
the selected-cutpoint and range hypotheses are simply uninhabited.
