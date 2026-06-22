# Reproduction - Lemma 5 Eq5 own-block block-width payload

Status: reproduced; Lean checked; one-branch payload adapter.

## Source Boundary

The previous Eq5 own-block payload proved that one supplied equation `(5)`
own-block branch gives both counted-datum membership and introduced-label
membership, assuming a raw selected-width bound

```text
aoyagiSelectedWidthNat ell m p <= n(S+1).
```

This slice derives that bound from the selected-block actual-width lower-bound
API.  It is still conditional on supplied Eq5 piecewise data and on explicit
actual-width lower bounds over each selected block.

## Calculation

Assume `C.block p S`.  The selected-block width API gives

```text
aoyagiSelectedWidthNat ell m p <= n(S+1)
```

from the block-local actual-width lower-bound hypothesis

```text
forall i : Fin ell, forall r,
  C.point i <= r -> r < C.point (i+1) ->
    aoyagiSelectedWidthNat ell m i <= n r.
```

The existing raw-width payload then applies unchanged.  The positive
coordinate guard `1 <= p` is derived from the Eq5 strict alpha data:

```text
1 <= alpha < p.
```

Therefore the branch supplies:

```text
some (p,T S) in aoyagiLemma5CountDatumSet
T S = k - 1
(S,k) in introducedLabelFinset.
```

## Lean Target

```text
aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_blockWidth
```

## Kill Conditions

- Do not drop the supplied actual-width lower-bound hypothesis.
- Do not infer the nonbase inequality; `T S != baseValue p` remains a
  hypothesis.
- Do not treat introduced-label membership as a terminal-exponent certificate.

## Nonclaims

No Eq5 vector construction, no nonbase-status proof, no classifier
construction, no branch-label injectivity, no back-to-label coverage, no Lemma
5 order count, no pole order, no normal crossings, and no RLCT extraction is
proved here.
