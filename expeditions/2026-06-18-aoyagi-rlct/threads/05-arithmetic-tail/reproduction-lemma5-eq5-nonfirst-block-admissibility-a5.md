# Reproduction - Lemma 5 Eq5 nonfirst block admissibility

Status: reproduced; Lean checked; xhigh review survived.

## Source

Aoyagi PDF pp. 26-27 gives equation `(5)` as a piecewise family of branch
values.  In the Lean supplied-certificate model, the first branch has value
`layerWidth(S+1)` and the other branches are expressed in terms of the Htilde
chains.

This slice only assembles already-proved branch-local interval guards.  It
does not construct the displayed source vector or prove that the post-`p`
lower guard follows from the paper.

## Calculation

Fix a selected block point `C.block b S` with `1<=b`.  The `b=0` first branch
is excluded.

The supplied Eq5 branch split has four remaining cases:

- `preAlpha`: membership in the Htilde interval is equivalent to
  `b <= intervalExcess(ell,a,b)`;
- `alphaToP`: membership is equivalent to
  `alpha-1 <= intervalExcess(ell,a,b)`;
- `postP`: membership is equivalent to
  `alpha+b-p <= intervalExcess(ell,a,b)`;
- `tail`: membership is automatic because the value is `Htilde_b`.

Strict Eq5 alpha-domain membership supplies the `preAlpha` and `alphaToP`
guards.  The post-`p` guard is not implied by the strict alpha domain, so it is
kept as an explicit hypothesis:

```text
aoyagiLemma5Eq5PostPLowerGuard ell a p alpha.
```

Combining these facts gives interval membership for every nonfirst selected
block point of the supplied Eq5 certificate.

## Lean Target

```text
aoyagiLemma5Eq5_nonfirstBlock_mem_intervalValueSetNat_of_alphaDomain_of_postPLowerGuard
```

## Kill Conditions

- Dropping `1<=b` exposes the first branch, whose value is `layerWidth(S+1)`
  and is not forced into a same-coordinate Htilde interval.
- Dropping the explicit post-`p` lower guard is killed by the existing
  `ell=6,a=4,p=2,alpha=1,b=4` counterexample.
- Replacing the supplied Eq5 piecewise certificate by weaker branch data would
  require restating the exact branch-local guards separately.

## Nonclaims

- No construction of equation `(5)`'s displayed vector.
- No source-label legality, actual-width dominance, or source branch coverage.
- No proof that the post-`p` lower guard follows from source hypotheses.
- No terminal `tilde t=0`, chart sequence, selected-span exactness,
  classifier/injection/back-to-label coverage, Lemma 5 order count, pole
  order, normal crossings, or RLCT extraction.
