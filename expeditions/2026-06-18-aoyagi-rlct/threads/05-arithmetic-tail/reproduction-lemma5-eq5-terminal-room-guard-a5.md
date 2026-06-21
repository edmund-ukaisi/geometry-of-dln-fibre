# Reproduction - Lemma 5 Eq5 Terminal-Room Guard

Status: reproduced; Lean checked; xhigh review pending.

## Source

Aoyagi PDF pp. 26-27 display equation `(5)`.  The post-`p` branch of the
supplied piecewise certificate has value

```text
T(S) = Htilde'_b - alpha + p - b
```

for selected-coordinate blocks satisfying

```text
p <= b <= p + (a-alpha).
```

The source passage does not state the global lower-bound guard below.  This
slice is finite arithmetic for the printed post-`p` branch, not a claim that
Aoyagi's family automatically satisfies it.

## Calculation

The existing exact-guard slice proved that post-`p` interval membership is
equivalent to

```text
alpha + b - p <= intervalExcess(ell,a,b),
```

where

```text
intervalExcess(ell,a,b) = min(b, ell-b, a, ell-a).
```

Thus the global post-`p` guard is

```text
forall b, p <= b -> b <= p + (a-alpha) ->
  alpha + b - p <= intervalExcess(ell,a,b).
```

Assume `alpha` lies in the strict Eq5 alpha domain.  Then

```text
1 <= alpha,
alpha <= intervalExcess(ell,a,p),
alpha < p.
```

In particular `alpha <= p` and `alpha <= a`.

For the forward direction, apply the guard at the terminal post-`p` coordinate

```text
b = p + (a-alpha).
```

Then the offset is

```text
alpha + b - p = a.
```

Since `intervalExcess(ell,a,b) <= ell-b`, the guard gives

```text
a <= ell - (p + (a-alpha)).
```

Equivalently,

```text
p + 2*a - alpha <= ell.
```

For the reverse direction, suppose

```text
p + 2*a - alpha <= ell.
```

For any post-`p` coordinate `b`, the offset `alpha+b-p` is bounded by each
component of the minimum:

```text
alpha+b-p <= b,
alpha+b-p <= a,
alpha+b-p <= ell-b,
alpha+b-p <= ell-a.
```

The first two use `alpha<=p`, `b<=p+(a-alpha)`.  The last two use the
terminal-room inequality.  Therefore the global post-`p` guard holds.

## Lean Targets

```text
aoyagiLemma5Eq5PostPLowerGuard_iff_terminalRoom_of_alphaDomain
aoyagiLemma5Eq5_nonfirstBlock_mem_intervalValueSetNat_of_alphaDomain_of_terminalRoom
```

The second theorem composes this iff with the existing nonfirst-block
admissibility wrapper, replacing the opaque post-`p` guard hypothesis by the
concrete terminal-room inequality.

## Nonclaims

- No construction of equation `(5)`'s displayed source vector.
- No proof that the terminal-room inequality follows from Aoyagi's source
  hypotheses.
- No source-label legality, cutoff coverage, terminal `tilde t=0`, chart
  sequence, classifier/injection/back-to-label coverage, Lemma 5 order count,
  pole order, normal crossings, or RLCT extraction.
