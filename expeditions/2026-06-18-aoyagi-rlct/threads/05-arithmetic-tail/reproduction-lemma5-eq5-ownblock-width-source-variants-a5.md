# Reproduction - Lemma 5 Eq5 own-block width-source variants

Status: reproduced; Lean checked; one-branch payload adapters.

## Source Boundary

The Eq5 own-block counted/introduced payload needs a selected-width lower
bound at the own-block source layer.  The previous block-width wrapper used an
explicit block-local actual-width lower-bound hypothesis.  This slice adds the
two source-shaped width dominance routes already isolated in the
`AoyagiSelectedCutpoints` API:

- selected left-endpoint width identities plus a block-local minimum
  condition;
- selected cutpoint width identities plus off-selected-layer dominance, with
  both non-strict and strict variants.

These routes derive only the width bound needed by the existing payload.

## Calculation

For `C.block p S`, each selected-width dominance theorem proves

```text
aoyagiSelectedWidthNat ell m p <= n(S+1).
```

The own-block payload then applies unchanged and gives

```text
some (p,T S) in aoyagiLemma5CountDatumSet
T S = k - 1
(S,k) in introducedLabelFinset.
```

The positive-coordinate guard `1 <= p` is still derived from the Eq5 alpha
data `1 <= alpha < p`.

## Lean Targets

```text
aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_leftEndpointMin
aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_offSelected
aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_offSelected_lt
```

## Kill Conditions

- Do not drop the selected-width source hypotheses.
- Do not infer the nonbase inequality; `T S != baseValue p` remains explicit.
- Do not turn introduced-label membership into terminal-exponent or least-value
  data.

## Nonclaims

No Eq5 vector construction, no nonbase-status proof, no classifier
construction, no branch-label injectivity, no back-to-label coverage, no Lemma
5 order count, no pole order, no normal crossings, and no RLCT extraction is
proved here.
