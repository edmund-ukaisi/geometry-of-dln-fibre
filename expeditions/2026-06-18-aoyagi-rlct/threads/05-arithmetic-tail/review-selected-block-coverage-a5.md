# Review - selected-block coverage

Reviewer: xhigh `Pauli`.

Status: passed.

## Scope

This review covers:

```text
AoyagiSelectedCutpoints.block_mem_selectedSpan
AoyagiSelectedCutpoints.exists_block_of_mem_selectedSpan
AoyagiSelectedCutpoints.exists_block_iff_mem_selectedSpan
```

The intended claim is only coverage of the selected span
`S_1-1 <= S < S_(ell+1)-1`.

## Findings

No blocking findings.

The three selected-span coverage theorems are source-faithful to the half-open
interval bookkeeping in Aoyagi Lemma 5.  The zero-based translation is
consistent:

```text
point C b = S_(b+1),
block C b S  iff  S_(b+1)-1 <= S < S_(b+2)-1.
```

The endpoint and subtraction checks pass.  The existence proof uses the first
`j` with `S < point C j - 1`; the lower span bound rules out `j=0`, and the
predecessor gives the lower bound for block `j-1`.  The strict upper bound
`S < point C ell - 1` correctly excludes the terminal selected cutpoint
`S_(ell+1)-1`.

The coverage theorem does not overclaim total source-layer coverage.  It proves
exactly the selected span and explicitly leaves source layers before `S_1-1`,
at `S_(ell+1)-1`, and after it outside this API.

## Verification

Reviewer reported:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
git diff --check -- lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
```
