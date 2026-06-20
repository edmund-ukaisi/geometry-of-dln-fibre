# Pen-and-paper reproduction - Lemma 4 two-value count

Status: checked sub-slice.  This reproduces only the elementary finite count
inside Aoyagi's Lemma 4 on PDF p. 25.  It does not prove the vector
inequalities, admissibility, or the statement that a vector corresponds to the
RLCT candidate.

## Source Target

In Lemma 4, Aoyagi considers values

```text
F_j = H_{j-1} - H_j + M^(S_{j+1})
```

that are all either `M-1` or `M`.  The count needed in the proof is:

```text
#{j : F_j = M}     = a,
#{j : F_j = M - 1} = ell-a.
```

The finite arithmetic requires the sum identity

```text
sum_j F_j = ell*(M-1) + a.
```

In the source, this sum identity is obtained from the `H_ell=0` bookkeeping and
the definition of `a`; that bridge is not part of this sub-slice.

## Count

Let

```text
n = #{j : F_j = M}.
```

Since each of the `ell` indexed entries is either `M-1` or `M`,

```text
sum_j F_j
  = n*M + (ell-n)*(M-1)
  = ell*(M-1) + n.
```

If also

```text
sum_j F_j = ell*(M-1) + a,
```

then cancellation gives

```text
n = a.
```

The remaining entries are exactly the low entries, so their count is

```text
ell-a.
```

## Boundary Checks

- `a=0`: all entries are `M-1`; no entry is `M`.
- `a=ell`: all entries are `M`; no entry is `M-1`.
- `ell=0`: the empty-index arithmetic theorem is consistent only when the sum
  identity forces `a=0`, but this is not source-facing because Aoyagi divides
  by `ell` elsewhere.
- `ell=1`: the theorem says the single entry is `M-1` for `a=0` and `M` for
  `a=1`.

## Lean Boundary

The Lean theorem is integer-valued: the family values and `M` live in `Z`,
while the index count and `a` are natural numbers.  This avoids the truncating
predecessor issue of a natural-number `M-1`.

This supports only:

- a reusable two-step integer count theorem for values `lo` and `lo+1`;
- an Aoyagi-shaped wrapper for values `M-1` and `M`;
- a corollary that the sum identity forces `a <= ell`.

It does not prove the source `H_ell=0` bridge, the `H_0` convention for `F_1`,
Lemma 4's vector inequalities, or the statement that the vector corresponds to
the candidate `lambda`.
