# Reproduction - Lemma 5 Eq5 counted-datum bridge

Status: reproduced; Lean checked.

## Source

Aoyagi Lemma 5 counts nonbase same-coordinate Htilde interval values across
interior selected coordinates.  The existing Eq5 admissibility lemmas prove
that a supplied equation `(5)` piecewise vector is in the same-coordinate
Htilde interval on every nonfirst selected block, under strict alpha-domain
guards and either a supplied post-`p` guard or the concrete terminal-room
inequality.

This slice connects that interval-admissibility result to the counted-datum
codomain.

## Calculation

Fix a supplied Eq5 piecewise vector `T`, a selected block point
`C.block b S`, and assume `1 <= b`.  The block condition gives `b < ell`, so

```text
b in Finset.Icc 1 (ell-1).
```

Under strict alpha-domain membership and the supplied post-`p` guard, the
existing nonfirst Eq5 theorem gives

```text
T S in aoyagiHtildeIntervalValueSetNat ell a M m b.
```

If the value is not the supplied base value at this coordinate,

```text
T S != baseValue b,
```

the counted-datum maps-to adapter gives

```text
some (Sigma.mk b (T S)) in
  aoyagiLemma5CountDatumSet ell a M m baseValue.
```

The terminal-room variant uses the existing terminal-room version of Eq5
nonfirst interval admissibility in place of the explicit post-`p` guard.

## Lean Targets

```text
aoyagiLemma5Eq5_nonfirstBlock_countDatumSet_mem_of_alphaDomain_of_postPLowerGuard
aoyagiLemma5Eq5_nonfirstBlock_countDatumSet_mem_of_alphaDomain_of_terminalRoom
```

## Kill Conditions

- Dropping `1 <= b` or `C.block b S` loses the interior counted-coordinate
  proof.
- Dropping strict alpha-domain membership or the post-`p`/terminal-room guard
  loses Eq5 interval admissibility.
- Dropping `T S != baseValue b` loses membership in the erased interval.

## Nonclaims

- No Eq5 vector is constructed.
- No proof is given that the value is nonbase.
- No proof is given that alpha-domain membership, terminal-room, or the
  post-`p` guard follow from Aoyagi source hypotheses.
- No classifier, injection, back-to-label map, order count, pole order, normal
  crossings, or RLCT extraction is proved.
