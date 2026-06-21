# Statement Card - A5 Lemma 5 Eq5 Offset Finset Adapter

## Lean Name

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_offsetValue_mem_introducedLabelFinset_of_lastPoint_widthBound`

## Claim

For one supplied equation `(5)` piecewise certificate and one own-block source
index `S`, the branch value `T S` is simultaneously:

```text
T S in aoyagiLemma5Eq5OffsetValueSet ell a p M m
T S in aoyagiHtildeIntervalValueSetNat ell a M m p
T S = k-1
Sigma.mk S k in introducedLabelFinset L n S k
```

## Inputs

Exactly the inputs of the existing Eq5 own-block interval/finite-domain
wrapper: supplied Eq5 piecewise data, last-cutpoint source range, explicit
actual-width lower bound, and the label relation
`k = Htilde'_p + 1 - alpha`.

## Proves

Only a conjunction of existing facts:

- strict-offset membership from the supplied own branch;
- interval membership and finite introduced-label membership from the existing
  wrapper.

## Does Not Prove

- A simultaneous construction over all offset values.
- Displayed-vector construction, terminality, admissibility, chart coverage,
  Lemma 5 order count, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equation `(5)`, PDF p. 27.
