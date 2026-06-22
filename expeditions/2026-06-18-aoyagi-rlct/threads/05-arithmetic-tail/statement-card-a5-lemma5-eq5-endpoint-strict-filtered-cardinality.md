# Statement card - A5 Lemma 5 Eq5 strict endpoint filtered cardinality

## Lean Name

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_strict_branch_card_eq_intervalSize_sub_one`

## Claim

For the strictest supplied Eq5 endpoint constructor, the filtered
one-coordinate branch set has cardinality

```text
aoyagiLemma5IntervalSize ell a j - 1
```

at every interior coordinate `j in Icc 1 (ell-1)`.

## Proved

Lean specializes the already-proved general endpoint filtered-count theorem to
the constructor where raw value injectivity is derived from strict alpha
injectivity and raw cross-coordinate disjointness is derived from supplied
component-coordinate facts.

## Assumed

The supplied strict Eq5 branch family, supplied upper/lower endpoint records,
base-value interval membership, strict alpha-domain coverage, strict branch
value formulas, endpoint value formulas, strict alpha injectivity, and
component branch-coordinate facts.

## Deferred

Eq5 branch construction, source production of endpoint records, source-label
legality, source proof of strict alpha injectivity, base-filter survival for a
specific source record, terminal-minimum label counting, source-backed
no-extra coverage, Lemma 5 order count, pole order, normal crossings, and RLCT
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

xhigh review passed.  Review artifact:
`review-lemma5-eq5-endpoint-strict-filtered-and-terminal-branchcoord-a5.md`.
