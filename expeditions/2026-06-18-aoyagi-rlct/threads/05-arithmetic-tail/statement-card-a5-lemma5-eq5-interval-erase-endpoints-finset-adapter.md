# Statement Card - A5 Lemma 5 Eq5 Erased-Endpoints Finset Adapter

## Lean Name

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_eraseEndpoints_mem_introducedLabelFinset_of_lastPoint_widthBound`

## Claim

In the rising region, one supplied Eq5 strict-offset branch is a member of the
same-coordinate interval after erasing both endpoints, and it retains its
finite-domain introduced-label membership:

```text
T S in (HtildeIntervalValueSet_p.erase Htilde'_p).erase Htilde_p
T S = k-1
Sigma.mk S k in introducedLabelFinset L n S k.
```

## Inputs

- Rising-region guards `1 <= p`, `p <= a`, and `p <= ell-a`.
- Supplied Eq5 piecewise source-vector certificate.
- Own-block membership `C.block p S`.
- Last selected cutpoint range `C.point ell <= L+1`.
- Explicit actual-width lower bound
  `aoyagiSelectedWidthNat ell m p <= n(S+1)`.
- Label identity `k = Htilde'_p + 1 - alpha`.

## Proves

Only a one-branch adapter from strict Eq5 offset membership to membership in
the same-coordinate interval with both endpoints erased, plus the existing
label predecessor and introduced-label finite-domain facts.

## Does Not Prove

- Construction of Eq5 displayed vectors or all Eq5 branches.
- Realisation of the erased endpoints by equations `(3)` or `(4)`.
- Any `LabelExponentCertificate`, terminal exponent, or least-value field.
- Terminality, admissibility, chart coverage, Lemma 5 order count, normal
  crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equation `(5)`, PDF pp. 26-27, plus finite-set equality
`aoyagiLemma5Eq5_offsets_eq_interval_erase_endpoints_of_le_min`.
