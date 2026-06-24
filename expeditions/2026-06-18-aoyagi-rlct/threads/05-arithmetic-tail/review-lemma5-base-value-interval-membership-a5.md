# Review - A5 Lemma 5 base-value interval membership

Date: 2026-06-24.

Reviewer: Hubble, xhigh read-only review.

Status: passed with no blocking findings.

## Scope

Reviewed the Lean theorem

```text
aoyagiLemma5BaseValue_mem_intervalValueSetNat_of_baseChainBounds
```

in `Lemma5SuppliedFamily.lean`, the supporting interval APIs in
`HtildeChainArithmetic.lean`, the reproduction note, statement card, and the
expedition ledger updates for the A5 base-value interval-membership cleanup.

## Findings

No blocking findings.

The Lean cleanup is narrowly scoped and formally correct.  The theorem uses
only the supplied lower and upper base-chain bounds,
`aoyagiHtildeChainBounds_mem_intervalValueSet`, the Nat-indexed interval-value
wrapper, and the supplied coordinate equality.  The interior guard
`j in Icc 1 (ell-1)` is converted to `j < ell+1` before unfolding the
Nat-indexed wrapper.

Boundary and source discipline are clean.  The reproduction and statement card
keep `baseH` and the coordinate equality supplied, and explicitly deny
Eq3/Eq4/Eq5 construction, source-label legality, no-extra coverage,
injectivity, terminal exactness, pole order, normal crossings, and RLCT
extraction.

The reviewer ran read-only focused Lean checks:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean
lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean
```

Both passed.  The reviewer also scanned the two Lean files and found no
`sorry`, `axiom`, `native_decide`, or `#exit`.

## Residual Risk

The independent review did not run a full build.  The controller separately
ran the focused module build, full `DLNFibre` build, project sorry audit, and
diff whitespace check.
