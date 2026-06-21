# Statement Card - A5 Lemma 5 Introduced-Label Finset Adapters

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_piecewise_ownCoordinate_mem_introducedLabelFinset_of_lastPoint`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_piecewise_ownCoordinate_mem_introducedLabelFinset_of_lastPoint`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_intervalValue_mem_introducedLabelFinset_of_lastPoint_widthBound`

## Claim

The existing Eq3, Eq4, and Eq5 introduced-label wrappers also give finite-domain
membership in `introducedLabelFinset` for the same post-advance state `(S,k)`.

For Eq3/Eq4 this packages:

```text
T(S)=k-1
Sigma.mk S k in introducedLabelFinset L n S k
```

For Eq5 it packages:

```text
T(S) in aoyagiHtildeIntervalValueSetNat ell a M m p
T(S)=k-1
Sigma.mk S k in introducedLabelFinset L n S k
```

## Inputs

The hypotheses are exactly those of the corresponding introduced-label wrapper:
the supplied piecewise certificate, last-cutpoint source range, actual-width
compatibility or width lower bound, and Eq3's explicit slack where applicable.

## Proves

Only finite-domain membership via `mem_introducedLabelFinset.mpr` from the
already-proved `introducedLabel` conclusion.

## Does Not Prove

- `LabelExponentCertificate` or any terminal-exponent / least-value data.
- New source-label legality hypotheses.
- Displayed-vector construction, terminality, admissibility, chart coverage,
  Lemma 5 order count, normal crossings, or RLCT extraction.

## Source

This is an API adapter over previous Aoyagi Lemma 5 source-label wrappers and
the local finite-domain definition in `BlowupArithmetic.lean`.  It adds no new
PDF calculation.
