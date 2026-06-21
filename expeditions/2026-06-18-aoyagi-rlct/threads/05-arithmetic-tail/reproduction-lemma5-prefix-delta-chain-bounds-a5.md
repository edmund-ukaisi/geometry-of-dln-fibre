# Reproduction - Lemma 5 Prefix-Delta Chain Bounds

Status: elementary finite bridge; formalisation-ready.

For an intermediate chain `H`, write

```text
D_j = P_j - H_j - j*(M-1),
```

where `P_j` is the selected-width prefix sum.  The displayed lower and upper
chains are

```text
Htilde_j  = P_j - (j*(M-1) + min(j,a)),
Htilde'_j = P_j - (j*(M-1) + min(a, j-(ell-a))).
```

Here `j-(ell-a)` is Lean's natural-number truncated subtraction, so it is zero
when `j <= ell-a`.

Thus the componentwise chain bounds are exactly bounds on the prefix delta:

```text
min(a, j-(ell-a)) <= D_j <= min(j,a).
```

Indeed,

```text
Htilde_j <= H_j
```

is equivalent to

```text
D_j <= min(j,a),
```

and

```text
H_j <= Htilde'_j
```

is equivalent to

```text
min(a, j-(ell-a)) <= D_j.
```

Once these prefix-delta bounds are supplied, the existing interval-value-set
membership theorem gives, under the source range hypothesis `a <= ell`,

```text
H_j in {H : Htilde_j <= H <= Htilde'_j}
```

for every chain coordinate.

## Boundary

This slice does not prove the prefix-delta bounds.  In source terms, those
bounds should follow from a binary increment-prefix sequence with total `a`,
but that is a separate arithmetic step.  This slice only records the algebraic
translation from supplied prefix-delta bounds to displayed-chain bounds.

## Nonclaims

- No binary-delta prefix-count theorem is proved here.
- No source vector is classified.
- No Case 1(2) uniqueness, branch construction, terminal-label exactness,
  pole order, normal crossings, or RLCT extraction is proved.
