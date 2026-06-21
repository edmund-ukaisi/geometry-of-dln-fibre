# Reproduction - Lemma 5 Eq5 early and tail interval guards

Status: reproduced; Lean checked; xhigh review pending.

## Source

Aoyagi PDF pp. 26-27 displays equation `(5)`.  In Lean's supplied
piecewise-certificate form, the remaining non-post-`p` branches are:

```text
preAlpha:
  1 <= b, b+2 <= alpha,
  T(S) = Htilde'_b - b.

alphaToP:
  1 <= b, alpha <= b+1, b+1 <= p,
  T(S) = Htilde'_b - alpha + 1.

tail:
  p+(a-alpha)+1 <= b,
  T(S) = Htilde_b.
```

These are still supplied branch-value clauses.  The source construction of
the displayed vector and source-label legality are not part of this slice.

## Calculation

The same-coordinate Htilde interval is the closed interval

```text
Htilde_b <= H <= Htilde'_b,
```

and the gap identity is

```text
Htilde'_b - Htilde_b = intervalExcess(ell,a,b).
```

For `preAlpha`, the value is `Htilde'_b-b`.  The upper bound is automatic
because `b` is a natural-number offset.  The lower bound is exactly

```text
b <= intervalExcess(ell,a,b).
```

For `alphaToP`, the value is

```text
Htilde'_b - alpha + 1 = Htilde'_b - (alpha-1),
```

using `1<=alpha`.  The upper bound is automatic, and the lower bound is
exactly

```text
alpha-1 <= intervalExcess(ell,a,b).
```

The offset is `alpha-1`, not `alpha`.

For `tail`, the value is exactly `Htilde_b`, hence it is the lower endpoint
of the interval.  No lower guard is needed.

## Alpha-Domain Guard Production

Lean also proves that strict Eq5 alpha-domain membership supplies the early
branch guards:

```text
aoyagiLemma5Eq5PreAlphaLowerGuard_of_alphaDomain
aoyagiLemma5Eq5AlphaToPLowerGuard_of_alphaDomain
```

This uses the fact that

```text
alpha <= intervalExcess(ell,a,p)
```

implies the relevant `a` and terminal-side caps, while the branch inequalities
provide the remaining caps.  The post-`p` guard is not covered by these
lemmas; the previous exact-guard slice records the counterexample.

## Lean Targets

```text
aoyagiLemma5Eq5PreAlphaLowerGuard
aoyagiLemma5Eq5AlphaToPLowerGuard
aoyagiLemma5Eq5_preAlpha_mem_intervalValueSetNat_iff_index_le_intervalExcess
aoyagiLemma5Eq5_alphaToP_mem_intervalValueSetNat_iff_predAlpha_le_intervalExcess
aoyagiLemma5Eq5_preAlpha_mem_intervalValueSetNat_of_preAlphaLowerGuard
aoyagiLemma5Eq5_alphaToP_mem_intervalValueSetNat_of_alphaToPLowerGuard
aoyagiLemma5Eq5_tail_mem_intervalValueSetNat
aoyagiLemma5Eq5PreAlphaLowerGuard_of_alphaDomain
aoyagiLemma5Eq5AlphaToPLowerGuard_of_alphaDomain
```

## Nonclaims

- No construction of equation `(5)`'s displayed vector.
- No source-label legality or actual-width dominance.
- No proof that the post-`p` lower guard follows from the strict alpha domain.
- No terminal `tilde t=0`, chart sequence, selected-span coverage,
  classifier/injection/back-to-label coverage, Lemma 5 order count, pole
  order, normal crossings, or RLCT extraction.
