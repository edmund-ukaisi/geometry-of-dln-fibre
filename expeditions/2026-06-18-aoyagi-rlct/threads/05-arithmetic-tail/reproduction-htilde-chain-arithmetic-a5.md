# Pen-and-paper reproduction - Htilde chain arithmetic

Status: checked source slice.  This reproduces only the finite arithmetic of
Aoyagi's displayed `Htilde_j` and `Htilde'_j` chains on PDF pp. 24-26.  It
does not prove exponent-vector admissibility, the source `T -> (H_j),(S_j)`
correspondence, Lemma 4, Lemma 5, pole order, normal crossings, or RLCT
extraction.

## Closed Form

Write

```text
W_i = M(S_i),
P_j = sum_{i=1}^j W_i,
P_0 = 0,
Q = Aoyagi's integer M.
```

For `0 <= j <= ell`, the displayed lower chain `Htilde` is

```text
Htilde_j = P_(j+1) - j*(Q-1) - min(j,a).
```

The displayed upper chain `Htilde'` is

```text
Htilde'_j = P_(j+1) - j*Q + min(j,ell-a).
```

Equivalently, since

```text
j*Q - min(j,ell-a)
  = j*(Q-1) + (j - min(j,ell-a)),
```

`Htilde'_j` subtracts `j` baseline low increments plus the number of high
increments in the low-first pattern.

At `j=0`, both chains give

```text
Htilde_0 = Htilde'_0 = W_1.
```

This `j=0` value is not a displayed source index, but it is exactly the
`H_0=W_1` convention needed for the uniform increment formula.

## Source Branches

For `1 <= j <= ell`, the lower formula gives Aoyagi's two displayed branches:

- if `j <= a`, then `min(j,a)=j`, hence

```text
Htilde_j = P_(j+1) - j*Q;
```

- if `a < j`, then `min(j,a)=a`, hence

```text
Htilde_j = P_(j+1) - a*Q - (j-a)*(Q-1).
```

For the upper chain, put `c=ell-a`.

- if `j <= c`, then

```text
Htilde'_j = P_(j+1) - j*(Q-1);
```

- if `c < j`, then

```text
Htilde'_j = P_(j+1) - c*(Q-1) - (j-c)*Q.
```

These are the displayed formulas in Aoyagi's Lemma 4/Lemma 5 discussion.

## Increment Blocks

Let

```text
F_j(H) = H_(j-1) - H_j + W_(j+1).
```

For the lower chain, set

```text
A_j = j*(Q-1) + min(j,a).
```

Since `Htilde_j = P_(j+1)-A_j`, the prefix sums cancel:

```text
F_j(Htilde) = A_j - A_(j-1).
```

The difference of `min(j,a)` is `1` exactly while `j <= a`.  Therefore

```text
F_j(Htilde) = Q       for 1 <= j <= a,
F_j(Htilde) = Q - 1   for a < j <= ell.
```

For the upper chain, the high-increment prefix count is

```text
B_j = min(a, j-(ell-a)).
```

Here `j-(ell-a)` is truncated subtraction.  Then

```text
Htilde'_j = P_(j+1) - (j*(Q-1)+B_j),
```

and

```text
F_j(Htilde') = Q - 1   for 1 <= j <= ell-a,
F_j(Htilde') = Q       for ell-a < j <= ell.
```

Thus the two displayed chains realize the two ordered extremal placements of
the `a` high increments.

## Endpoint

At `j=ell`, both chains have the common terminal endpoint

```text
P_(ell+1) - (a*Q + (ell-a)*(Q-1)).
```

Using Definition 3's selected-width sum

```text
P_(ell+1) = ell*(Q-1)+a,
```

this endpoint is zero.

## Interval Excess

For `0 <= a <= ell` and `0 <= j <= ell`,

```text
Htilde'_j - Htilde_j
  = min(j,a) + min(j,ell-a) - j
  = min(j, ell-j, a, ell-a).
```

The right-hand side is the closed interval-excess formula already used in the
Lemma 5 arithmetic slice.  It is zero at `j=0`, at `j=ell`, and for all `j`
when `a=0` or `a=ell`.

## Lean Boundary

Safe Lean targets:

- total Nat-indexed prefix sums and selected-width accessors;
- lower and upper `Htilde` chain definitions with Fin wrappers;
- `Htilde_0=Htilde'_0=W_1`;
- both terminal endpoints equal the previously defined
  `aoyagiLemma4TerminalEndpoint`;
- ordered-block increment formulas for both chains;
- pointwise interval-excess formula linked to `aoyagiLemma5IntervalExcess`.

Deferred:

- source-faithful `T -> (H_j),(S_j)` correspondence;
- proof that `Ttilde <= T <= Ttilde'` supplies same-coordinate hypotheses;
- two-value increment hypothesis for arbitrary vectors;
- admissibility/coverage/exclusion of Lemma 5 chart families;
- pole-order interpretation, normal crossings, and RLCT extraction.

## Independent Checks

Xhigh source checker `Schrodinger the 5th` independently derived the closed
formulas, ordered increment blocks, terminal endpoint, and interval-excess
identity.  Xhigh Lean/API scout `Halley the 5th` recommended a separate
`HtildeChainArithmetic` module importing the existing Lemma 4 count arithmetic
and Lemma 5 interval arithmetic, with total Nat-indexed helpers and Fin-chain
wrappers.
