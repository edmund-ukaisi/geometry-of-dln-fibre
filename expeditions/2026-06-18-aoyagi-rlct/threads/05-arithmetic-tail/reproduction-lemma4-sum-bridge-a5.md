# Pen-and-paper reproduction - Lemma 4 source sum bridge

Status: checked sub-slice.  This reproduces only the finite telescoping step
inside Aoyagi's Lemma 4 on PDF p. 25, using the definitions introduced on PDF
pp. 22-23 and Definition 3 on PDF pp. 8-9.  It does not prove vector
admissibility or that a vector corresponds to the RLCT candidate.

## Source Target

Write

```text
W_j = M^(S_j),       B = sum_{j=1}^{ell+1} W_j.
```

Definition 3 defines the integer `M` and `a` by

```text
M - 1 < B/ell <= M,
a = B - ell*(M-1).
```

Hence

```text
B = ell*(M-1) + a.
```

On PDF p. 22, Aoyagi defines

```text
F_1 = W_1 + W_2 - H_1,
F_j = H_(j-1) - H_j + W_(j+1)       for 2 <= j <= ell.
```

Lemma 4 later writes all increments uniformly as

```text
F_j = H_(j-1) - H_j + W_(j+1).
```

For `j=1`, this is source-faithful only after introducing the convention

```text
H_0 := W_1.
```

## Telescope

With `H_0 = W_1`, define for all `j=1,...,ell`

```text
F_j = H_(j-1) - H_j + W_(j+1).
```

Then

```text
sum_{j=1}^ell F_j
  = sum_{j=1}^ell (H_(j-1) - H_j + W_(j+1))
  = H_0 - H_ell + sum_{j=2}^{ell+1} W_j
  = B - H_ell.
```

Aoyagi's terminal condition is

```text
H_ell = 0.
```

Therefore

```text
sum_{j=1}^ell F_j = B = ell*(M-1) + a.
```

This is exactly the sum identity assumed in the previous isolated two-value
count sub-slice.

## Consequence with the two-value hypothesis

If every `F_j` is either `M-1` or `M`, and

```text
n = #{j : F_j = M},
```

then

```text
sum_j F_j
  = n*M + (ell-n)*(M-1)
  = ell*(M-1) + n.
```

Comparing with the telescoped identity gives

```text
n = a.
```

Thus the number of `M` entries is `a`, and the number of `M-1` entries is
`ell-a`.

## Lean Boundary

The Lean theorem should assume:

- indexed selected widths `m : Fin (ell+1) -> Z`;
- an extended `H : Fin (ell+1) -> Z`;
- `H 0 = m 0`, encoding `H_0 = W_1`;
- `H (Fin.last ell) = 0`, encoding `H_ell = 0`;
- Definition 3's selected-width sum
  `sum m = ell*(M-1)+a`;
- the two-value increment hypothesis when invoking the count theorem.

It should prove:

```text
sum_j F_j = sum_j m_j
sum_j F_j = ell*(M-1)+a
#{j : F_j = M} = a
#{j : F_j = M-1} = ell-a
```

This still does not prove:

- the two-value hypothesis itself;
- the inequalities `Ttilde <= T <= Ttilde'`;
- that the resulting vector corresponds to `lambda`;
- the endpoint-corrected Lemma 3 bridge needed to conclude minimisation;
- Lemma 5's chart-family order count.

## Independent Check

Xhigh source checker `Dewey the 5th` independently derived the same telescope:

```text
sum F_j = B - H_ell.
```

With `H_ell = 0` and Definition 3's `B = ell*(M-1)+a`, the sum identity is
valid.  The checker flagged the same caveat: the formula requires the explicit
`H_0 := M^(S_1)` convention, or else `F_1` must remain a separate case.
