# Pen-and-paper reproduction - Lemma 5 interval-size profile

Status: checked elementary interval arithmetic.

This note reproduces the three-region cardinality profile displayed in
Aoyagi's Lemma 5.  It is only the finite arithmetic of the intervals between
the two `Htilde` chains.

## Source

Aoyagi PDF pp. 25-26 defines the lower and upper chains `Htilde_j` and
`Htilde'_j`.  In Lemma 5, for `j=1,...,ell-1`, the source counts the interval

```text
I_j = {H : Htilde_j <= H <= Htilde'_j}.
```

The displayed cardinality profile is:

```text
|I_j| = j+1,
  if j <= min(a, ell-a),

|I_j| = min(a, ell-a)+1,
  if min(a, ell-a)+1 <= j <= max(a, ell-a),

|I_j| = min(a, ell-a)+1+max(a, ell-a)-j,
  if max(a, ell-a)+1 <= j <= ell.
```

Lean uses a slightly boundary-inclusive form:

```text
if j <= min(a,ell-a) then ...
else if j <= max(a,ell-a) then ...
else ...
```

under `a<=ell` and `j<=ell`.

## Reproduction

The already-reproduced chain arithmetic gives:

```text
Htilde'_j - Htilde_j
  = e_j
  = min(j, ell-j, a, ell-a).
```

Therefore:

```text
|I_j| = e_j+1.
```

Let:

```text
b = min(a, ell-a),
c = max(a, ell-a).
```

Since `a<=ell`, we have `b+c=ell`.

### First Region

Assume `j<=b`.  Then `j<=a`, `j<=ell-a`, and `j<=ell-j` because
`j<=ell-a`.  Hence:

```text
e_j = j
|I_j| = j+1.
```

### Middle Region

Assume `b<=j<=c`.

If `a<=ell-a`, then `b=a` and `c=ell-a`.  The inequalities give:

```text
a<=j,  j<=ell-a,  hence a<=ell-j.
```

Thus the minimum of `j`, `ell-j`, `a`, `ell-a` is `a=b`.

If `ell-a<=a`, then `b=ell-a` and `c=a`.  The inequalities give:

```text
ell-a<=j,  j<=a,  hence ell-a<=ell-j.
```

Thus the minimum is `ell-a=b`.  In either case:

```text
e_j = b
|I_j| = b+1.
```

### Falling Region

Assume `c<=j<=ell`.

If `a<=ell-a`, then `c=ell-a`, so `ell-j<=a` and `ell-j<=ell-a`.
Also `ell-j<=j`, because `j>=ell-a>=a` and `a<=ell-a`.

If `ell-a<=a`, then `c=a`, so `ell-j<=ell-a` and `ell-j<=a`; again
`ell-j<=j`.

Thus in either case:

```text
e_j = ell-j.
```

Using `b+c=ell`, the interval size is:

```text
|I_j| = ell-j+1 = b+1+c-j.
```

This is Aoyagi's falling-region formula.

## Lean Targets

```text
aoyagiLemma5IntervalSize_eq_succ_of_le_min
aoyagiLemma5IntervalSize_eq_min_succ_of_min_le_of_le_max
aoyagiLemma5IntervalSize_eq_falling_of_max_le
aoyagiLemma5IntervalSize_sourcePiecewise
```

## Nonclaims

- No displayed-vector construction.
- No proof that the counted values are realised by admissible vectors.
- No terminal `tilde t=0`, vector admissibility, chart sequence, Lemma 5 order
  count, normal crossings, or RLCT extraction.
