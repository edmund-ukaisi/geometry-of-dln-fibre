# Reproduction - Lemma 5 Eq5 post-p lower exact guard

Status: reproduced; Lean checked; xhigh review pending.

## Source

Aoyagi PDF pp. 26-27 displays equation `(5)`.  In Lean's zero-based selected
coordinate notation, the post-`p` clause of the supplied piecewise certificate
has the form

```text
p <= b <= p + (a-alpha),
T(S) = Htilde'_b - alpha + p - b.
```

The source passage does not prove that this clause stays inside the Htilde
interval for every post-`p` block.  The existing obstruction slice already
showed that it can fall below the lower chain.

## Calculation

Assume `p<=b`.  Then the natural-number offset has no truncation:

```text
((alpha+b-p : Nat) : Int) = alpha + b - p.
```

Thus the post-`p` value rewrites as

```text
T(S) = Htilde'_b - (alpha+b-p).
```

The Htilde gap identity gives

```text
Htilde'_b - Htilde_b = intervalExcess(ell,a,b).
```

The same-coordinate Htilde interval is exactly

```text
Htilde_b <= H <= Htilde'_b.
```

For the post-`p` value, the upper bound is automatic because
`alpha+b-p` is a natural-number offset.  The lower bound is

```text
Htilde_b <= Htilde'_b - (alpha+b-p),
```

which is equivalent to

```text
alpha+b-p <= intervalExcess(ell,a,b).
```

Therefore the precise local admissibility statement is

```text
T(S) in intervalValueSetNat(ell,a,M,m,b)
  iff alpha+b-p <= intervalExcess(ell,a,b).
```

## Guard Predicate

Lean names the global post-`p` lower guard as

```text
aoyagiLemma5Eq5PostPLowerGuard ell a p alpha
```

meaning that the offset/excess inequality holds for every post-`p` coordinate
`b`.

A sufficient finite-arithmetic condition is also formalised: if

```text
alpha <= p,
alpha <= a,
p + 2*a - alpha <= ell,
```

then the post-`p` lower guard holds.  This is only a sufficient terminal-room
condition, not a necessary condition and not a source theorem.

## Counterexample

The current strict alpha domain plus the post-`p` range does not imply the
guard.  Take

```text
ell=6, a=4, p=2, alpha=1, b=4.
```

Then `alpha=1` lies in the strict Eq5 alpha domain at `p=2`, and

```text
2 <= 4 <= 2 + (4-1).
```

But

```text
alpha+b-p = 3,
intervalExcess(6,4,4) = min(4,2,4,2) = 2,
```

so the required lower guard is false.

## Lean Targets

```text
aoyagiLemma5Eq5PostPLowerGuard
aoyagiLemma5Eq5PostPLowerGuard_of_terminalRoom
aoyagiLemma5Eq5_postP_mem_intervalValueSetNat_iff_offset_le_intervalExcess
aoyagiLemma5Eq5_postP_mem_intervalValueSetNat_of_offset_le_intervalExcess
aoyagiLemma5Eq5_postP_mem_intervalValueSetNat_of_postPLowerGuard
aoyagiLemma5Eq5_alphaDomain_and_postPRange_not_lowerGuard
aoyagiLemma5Eq5_not_postPLowerGuard_counterexample
```

## Nonclaims

- No construction of equation `(5)`'s displayed source vector.
- No proof that Aoyagi's source hypotheses imply the post-`p` lower guard.
- No proof that the strict alpha domain implies the post-`p` lower guard.
- No source-label legality, cutoff coverage, terminal `tilde t=0`, chart
  sequence, classifier/injection/back-to-label coverage, Lemma 5 order count,
  pole order, normal crossings, or RLCT extraction.
