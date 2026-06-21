# Pen-and-paper reproduction - Lemma 5 equation (5) alpha-family source label

Status: reproduced; xhigh scoped.

## Source

Aoyagi PDF p. 27, equation `(5)`, uses a strict offset parameter `alpha` with

```text
1 <= alpha,
alpha < j0,
Htilde_(j0)+1 <= k < Htilde'_(j0)+1,
k = Htilde'_(j0)+1-alpha.
```

In Lean's zero-based notation paper `j0` is coordinate `p`.  The already
defined strict alpha domain is

```text
1 <= alpha <= min(excess(ell,a,p), p-1),
```

where `excess(ell,a,p)=Htilde'_p-Htilde_p`.

## Reproduction

Membership in the strict alpha domain is equivalent to the three guards

```text
1 <= alpha,
alpha <= excess(ell,a,p),
alpha < p.
```

The existing Eq5 label-bound theorem uses only the first two guards:

```text
1 <= alpha,
alpha <= Htilde'_p-Htilde_p.
```

Together with Definition 3's selected-width hypotheses, these give

```text
1 <= Htilde'_p+1-alpha <= W_p.
```

Therefore, if `k=Htilde'_p+1-alpha`, the source index satisfies
`1<=S<=L`, and the actual-width bound `W_p<=n(S+1)` is supplied, then

```text
actualWidthLabel L n S k.
```

The strict guard `alpha<p` remains recorded in the domain membership, but it is
not used by label legality itself.

## Lean Targets

```text
aoyagiLemma5Eq5_alphaFamily_mem_iff_guards
aoyagiLemma5Eq5_alphaFamily_actualWidthLabel_at_of_widthBound
```

## Nonclaims

- No construction of equation `(5)`'s displayed vector.
- No proof that any branch with this `alpha` exists.
- No cutoff-index guard or selected-span coverage.
- No terminal `tilde t=0`, vector admissibility, or chart sequence.
- No supplied-family classifier, injection, back-to-label map, Lemma 5 order
  count, pole order, normal crossings, or RLCT extraction.
