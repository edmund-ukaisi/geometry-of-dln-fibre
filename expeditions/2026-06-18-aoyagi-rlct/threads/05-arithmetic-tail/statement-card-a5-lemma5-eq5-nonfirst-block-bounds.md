# Statement card - A5 Lemma 5 Eq5 nonfirst block bounds

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_nonfirstBlock_bounds_of_alphaDomain_of_postPLowerGuard`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_nonfirstBlock_bounds_of_alphaDomain_of_terminalRoom`

## Claim

For a supplied equation `(5)` piecewise certificate, strict alpha-domain
membership, and either the explicit post-`p` lower guard or the terminal-room
inequality, every nonfirst selected block point satisfies the vectorwise
Htilde bounds:

```text
aoyagiHtildeLowerNat ell a M m b <= T S
T S <= aoyagiHtildeUpperNat ell a M m b.
```

The nonfirst condition is `1<=b`.

## Proved

Lean unwraps the existing same-coordinate interval-membership theorem through
`aoyagiHtilde_mem_intervalValueSet_iff_bounds`.  The terminal-room theorem
uses the existing equivalence between terminal-room and the post-`p` lower
guard under strict alpha-domain membership.

## Assumed

The Eq5 piecewise certificate, strict alpha-domain membership, nonfirst block
condition, block membership, and either `aoyagiLemma5Eq5PostPLowerGuard` or
`p + 2*a - alpha <= ell` are supplied.

## Deferred

The first branch, Eq5 source-vector construction, source-label legality,
post-`p` guard production from source hypotheses, terminal `tilde t=0`, chart
coverage, selected-span exactness, Lemma 5 count, normal crossings, pole
order, and RLCT extraction.

## Review

- Focused Lean check passed for `DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector`.
- Independent xhigh reviewer `Pauli` found no fidelity or claim-soundness
  break.
