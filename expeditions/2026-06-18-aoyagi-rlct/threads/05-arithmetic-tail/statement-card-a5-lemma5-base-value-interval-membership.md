# Statement card - A5 Lemma 5 base-value interval membership

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean`

Name:

- `aoyagiLemma5BaseValue_mem_intervalValueSetNat_of_baseChainBounds`

## Claim

If a supplied base chain `baseH` is componentwise squeezed between Aoyagi's
displayed lower and upper `Htilde` chains, and the supplied `baseValue j`
agrees with `baseH` at every interior selected coordinate, then `baseValue j`
belongs to the Nat-indexed interval value set used by the Lemma 5 counted
datum codomain.

## Inputs Kept Explicit

- `a <= ell`;
- componentwise bounds
  `aoyagiHtildeLowerChain ell a M m <= baseH` and
  `baseH <= aoyagiHtildeUpperChain ell a M m`;
- supplied coordinate equality
  `baseH (aoyagiLemma5InteriorCoord ell j hj) = baseValue j`.

## Not Proved

No construction of the base branch from Aoyagi's printed Eq3/Eq4/Eq5, no
source-label legality, no chart-family coverage, no Lemma 5 exactness, no
terminal-label count, no pole order, no normal crossings, and no RLCT
extraction.

## Verification

Focused check passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.Lemma5SuppliedFamily
```

Full verification passed:

```text
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The sorry audit reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.

## Review

Xhigh independent review passed with no blocking findings.  Durable artifact:
`review-lemma5-base-value-interval-membership-a5.md`.
