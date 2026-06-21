# Reproduction - Lemma 5 Eq5 Erased-Endpoints Finset Adapter

Status: checked finite-set/API wrapper.

This note records the one-branch consequence of the finite-set equality that
identifies Eq5 strict offsets with the same-coordinate interval after erasing
both endpoints.  It does not package all Eq5 offsets at once.

## Source

Aoyagi Lemma 5, PDF pp. 26-27:

- Equation `(5)` supplies strict interior values between the lower and upper
  same-coordinate endpoints.
- In the rising region, these strict Eq5 values are the interval values with
  both endpoints removed.

The Lean equality already proved this finite-set statement as:

```text
aoyagiLemma5Eq5_offsets_eq_interval_erase_endpoints_of_le_min
```

The existing source-label wrapper already proves, for one supplied Eq5 branch,
that the branch value belongs to the strict Eq5 offset finite set and that its
label lies in the introduced-label finite domain.

## Reproduction

Work in the rising region:

```text
1 <= p,  p <= a,  p <= ell-a.
```

For a fixed supplied Eq5 piecewise certificate and a fixed own-block source
index `S`, the existing one-branch adapter gives:

```text
T S in Eq5OffsetValueSet_p
T S = k-1
Sigma.mk S k in introducedLabelFinset L n S k.
```

The existing finite-set equality gives:

```text
Eq5OffsetValueSet_p
  = (HtildeIntervalValueSet_p.erase Htilde'_p).erase Htilde_p.
```

Substituting the equality into the offset-membership statement gives:

```text
T S in (HtildeIntervalValueSet_p.erase Htilde'_p).erase Htilde_p.
```

The value equality and finite-domain membership are unchanged from the
one-branch adapter.

## Lean Target

```text
aoyagiLemma5Eq5_ownBlock_eraseEndpoints_mem_introducedLabelFinset_of_lastPoint_widthBound
```

## Kill Conditions

- Keep the rising-region guards `1 <= p`, `p <= a`, and `p <= ell-a`.
- Keep the supplied Eq5 piecewise certificate.
- Keep the last-cutpoint range and actual-width lower-bound hypotheses.
- Do not infer all Eq5 branches or any displayed-vector family.
- Do not infer endpoint realisation by equations `(3)` or `(4)`.
- Do not infer Lemma 5 order count, terminality, chart sequence, normal
  crossings, or RLCT extraction.
