# Statement card - A5 Lemma 5 Eq5 nonfirst block admissibility

## Lean Name

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_nonfirstBlock_mem_intervalValueSetNat_of_alphaDomain_of_postPLowerGuard`

## Claim

For a supplied equation `(5)` piecewise certificate, strict alpha-domain
membership, and the explicit post-`p` lower guard, every nonfirst selected
block point satisfies

```text
T S in aoyagiHtildeIntervalValueSetNat ell a M m b.
```

The nonfirst condition is `1<=b`.

## Proved

Lean mirrors the Eq5 branch classifier's case split:

- `preAlpha` uses the alpha-domain-produced pre-alpha lower guard;
- `alphaToP` uses the alpha-domain-produced alpha-to-`p` lower guard;
- `postP` uses the supplied `aoyagiLemma5Eq5PostPLowerGuard`;
- `tail` uses automatic lower-endpoint membership.

## Assumed

The Eq5 piecewise certificate, strict alpha-domain membership, explicit
post-`p` lower guard, nonfirst block condition, and block membership are
supplied.

## Deferred

The first branch, Eq5 source-vector construction, source-label legality,
post-`p` guard production from source hypotheses, terminal `tilde t=0`, chart
coverage, selected-span exactness, Lemma 5 count, normal crossings, pole
order, and RLCT extraction.

## Review

- xhigh pen-and-paper scout `Faraday` validated the wrapper and kill
  conditions.
- Focused Lean check passed for `Lemma5DisplayedVector.lean`.
- Independent xhigh reviewer `Confucius` found no fidelity or claim-soundness
  break.
