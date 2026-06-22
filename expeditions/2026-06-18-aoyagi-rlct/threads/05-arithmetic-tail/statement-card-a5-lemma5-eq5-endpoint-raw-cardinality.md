# Statement card - A5 Lemma 5 Eq5 endpoint raw cardinality

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5EndpointRawBranches_card_eq_intervalSize_of_value_injective`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5EndpointRawBranches_card_eq_intervalSize_of_alpha_injective`

## Claim

At one interior coordinate, the supplied Eq5 endpoint raw branch set has
cardinality equal to Aoyagi's same-coordinate interval size, once its values
cover the interval and are injective.

## Proved

Lean proves the cardinality by composing:

- the previous raw value-image equality for the Eq5 endpoint raw branch set;
- finite image cardinality under supplied raw value injectivity;
- the existing Htilde interval value-set cardinality theorem.

The second theorem derives the raw value injectivity from the already-proved
strict-alpha-injective endpoint wrapper.

## Assumed

`a <= ell`, interior coordinate `j in Icc 1 (ell-1)`, strict Eq5 alpha-domain
coverage, strict branch value formulas, upper endpoint value formula, rising
lower endpoint value formula, and either raw value injectivity or strict alpha
injectivity.

## Deferred

Strict Eq5 and endpoint branch construction, source-label legality,
source proof of strict alpha injectivity, source production of endpoint
records, base-filter survival, filtered nonbase cardinality, terminal-minimum
coverage, Lemma 5 order count, pole order, normal crossings, and RLCT
extraction.

## Cited

None; this is finite Lean bookkeeping over supplied hypotheses and previously
formalized definitions.

## Verification

Focused Lean check:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean
```

## Review

Independent xhigh review by Arendt passed on 2026-06-22 after a cwd note in
the verification command was repaired.  Review artifact:
`review-lemma5-eq5-endpoint-raw-cardinality-a5.md`.
