# Statement card - A5 Lemma 4 prefix-profile computations

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma4IncrementPrefix_eq_upperHighCount_add_of_eq_upperNat_sub`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4IncrementPrefix_eq_lowerHighCount_of_eq_lowerNat`

## Claim

For the Lemma 4 prefix normal form, an upper Htilde value with offset `r`
has prefix value `upperHighCount + r`, and a lower Htilde value has prefix
value `lowerHighCount`.

## Proved

Lean unfolds `aoyagiLemma4IncrementPrefix`, the relevant Htilde chain, and the
corresponding Htilde increment prefix, then closes the integer algebra by
`ring`.

## Assumed

Only the displayed coordinate equality is supplied:

```text
H j = aoyagiHtildeUpperNat ell a M m j.val - r
```

or

```text
H j = aoyagiHtildeLowerNat ell a M m j.val.
```

## Deferred

Eq5 endpoint-profile assembly, binary prefix deltas, two-value Lemma 4
increments, Eq5 vector construction, endpoint realisation, classifier data,
order count, pole order, normal crossings, and RLCT extraction.

## Review

Focused Lean check passed for `DLNFibre.DLN.Aoyagi.HtildeChainArithmetic`.
Independent xhigh scout `Feynman` confirmed the corrected proof skeletons.
