# Statement card - A5 Lemma 5 Eq5 endpoint filtered cardinality

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_branch_card_eq_intervalSize_sub_one`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_fullBranches_card`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord_fullBranches_card`

## Claim

For the supplied Eq5 endpoint nonbase-family constructor, each interior
filtered coordinate branch set has cardinality `aoyagiLemma5IntervalSize ell a
j - 1`, and the full tagged supplied branch set has cardinality
`a * (ell - a) + 1`.  The strictest wrapper derives the raw injectivity and
raw disjointness hypotheses from supplied strict alpha injectivity and supplied
component-coordinate facts.

## Proved

Lean proves the endpoint-shaped one-coordinate filtered count and two
endpoint-shaped full tagged branch counts, one for the general endpoint
constructor and one for the alpha-injective/component-coordinate constructor.

## Assumed

Supplied strict branch families, alpha map, branch value map, endpoint records,
base value, `a <= ell`, base-value membership in the same-coordinate interval,
strict alpha-domain coverage, strict value formulas, endpoint value formulas,
raw value injectivity and raw disjointness for the general wrapper; or supplied
strict alpha injectivity and component-coordinate facts for the strictest
wrapper.  The full tagged count also assumes `1 <= ell`.

## Deferred

Eq5 branch construction, source production of endpoint records, source-label
legality, survival of particular source records through the base filter,
terminal-candidate construction, terminal-minimum label classification,
source-backed no-extra coverage, Lemma 5 order count, pole order, normal
crossings, and RLCT extraction.

## Cited

None; this is finite Lean bookkeeping over supplied hypotheses and previously
formalized definitions.

## Verification

Focused Lean check:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean
```

## Review

Independent xhigh review passed.  Review artifact:
`review-lemma5-eq5-endpoint-filtered-cardinality-a5.md`.
