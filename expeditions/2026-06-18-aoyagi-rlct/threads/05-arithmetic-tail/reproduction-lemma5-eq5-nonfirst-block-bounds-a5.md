# Reproduction - Lemma 5 Eq5 nonfirst block bounds

Status: reproduced; Lean checked; xhigh review survived.

## Source

Aoyagi PDF pp. 26-27 gives equation `(5)` as a piecewise family of displayed
source-vector values.  The previously landed nonfirst-block admissibility slice
proved that, under the strict alpha-domain guards and the explicit post-`p`
lower guard, every nonfirst selected block value belongs to its same-coordinate
Htilde interval.

This slice records the vectorwise inequality form of that statement.

## Calculation

Fix a supplied Eq5 piecewise certificate `T`, a selected block point
`C.block b S`, and assume `1<=b`.  The nonfirst admissibility theorem gives

```text
T S in aoyagiHtildeIntervalValueSetNat ell a M m b.
```

Because `C.block b S` includes `b<ell`, this natural-indexed interval is the
finite interval at `j = <b,b<ell+1>`.  By the definition of the Htilde interval,
membership is equivalent to the two inequalities

```text
aoyagiHtildeLowerNat ell a M m b <= T S
T S <= aoyagiHtildeUpperNat ell a M m b.
```

Thus the proof is only:

1. use the already proved Eq5 nonfirst interval-membership theorem;
2. convert from the natural-indexed interval wrapper to the finite-indexed
   interval using `b<ell+1`;
3. unwrap `aoyagiHtilde_mem_intervalValueSet_iff_bounds`.

The terminal-room variant replaces the supplied post-`p` lower guard by the
existing finite equivalence

```text
aoyagiLemma5Eq5PostPLowerGuard ell a p alpha
  <-> p + 2*a - alpha <= ell
```

under strict alpha-domain membership.

## Lean Targets

```text
aoyagiLemma5Eq5_nonfirstBlock_bounds_of_alphaDomain_of_postPLowerGuard
aoyagiLemma5Eq5_nonfirstBlock_bounds_of_alphaDomain_of_terminalRoom
```

## Kill Conditions

- Dropping `1<=b` reintroduces the first Eq5 branch, whose value is the
  ambient `layerWidth(S+1)` and is not forced into a same-coordinate Htilde
  interval.
- Dropping the post-`p` guard or terminal-room hypothesis is killed by the
  existing `ell=6,a=4,p=2,alpha=1,b=4` counterexample.
- Replacing interval membership by a source-backed vector construction would
  require a separate proof of the displayed Eq5 branch family.

## Nonclaims

- No construction of equation `(5)`'s displayed vector.
- No proof that the post-`p` guard follows from source hypotheses.
- No source-label legality, actual-width dominance, terminality, chart
  coverage, selected-span exactness, classifier/injection/back-to-label
  coverage, Lemma 5 order count, pole order, normal crossings, or RLCT
  extraction.
