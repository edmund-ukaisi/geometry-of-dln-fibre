# Pen-and-paper reproduction draft - blow-up certificate

Status: draft reproduction/certificate design from xhigh scout `Ptolemy`,
integrated by the controller. This has not yet passed the independent
reproduction check.

Source: Aoyagi 2023 PDF pp. 14-23. Paper source only.

## State shape

Split Aoyagi's overloaded `M` notation.

```text
widths w[1..L+1]
effective m[S] = min_{1 <= q <= S} w[q]
stage S
pivot J
active block D_J : rows J+1..m[S], cols J+1..m[S+1]
tail matrices C^(S+1), ..., C^L
labels a = (s,k), 1 <= s <= L, 1 <= k <= m[s+1]
T[a] = (t_a^(1), ..., t_a^(L))
tmin[a] = min_j t_a^(j)
N[a] = Aoyagi's M_{s,k}, the Jacobian numerator
b_i monomials, with b_0 = 1
active exceptional variables U(S,J) = {(q,k): q < S} union {(S,k): k <= J}
```

Initial state: normalize the paper's "obvious" base case to `S = 1`, `J = 0`:

```text
D_0 = C^(1)
b_i = 1
T[s,k]^(j) = m[j+1]
tmin[s,k] = m[1]
N[s,k] = 0
```

This avoids the paper's undefined-looking `S = 0` notation while matching PDF
pp. 14-15. This normalization needs checker confirmation.

## Invariant

At every state, the ideal of entries satisfies

```text
< prod_{s=1}^L C^(s) >
 =
< diag(b_1, ..., b_{m[S]})
    * blockdiag(E_J, D_J)
    * prod_{s=S+1}^L C^(s) >.
```

The monomials satisfy

```text
b_i = b_{i-1} * prod_{a : tmin[a] = i-1} u_a.
```

The coordinate volume has monomial Jacobian

```text
prod_{active a} u_a^(N[a]-1) du_a
```

times the remaining smooth differentials. All `T[a]` are pairwise comparable
componentwise. This matches the inductive statement on PDF p. 15.

## Case 1

Source: PDF pp. 15-19.

Precondition: there is a first later jump

```text
h = J + J1 < m[S]
```

such that no active label has `tmin` in `J+1, ..., h-1`, and at least one active
label has `tmin = h`. Pick a minimal such label `a = (s,k)` under componentwise
order. Blow up the center

```text
D_J rows J+1..h all columns = 0,
u_a = 0.
```

### Case 1(1), `u_a` chart

Source: PDF p. 16.

```text
D rows J+1..h := u_a * D'
T[a]^(q) := J for q >= S
tmin[a] := J
N[a] += J1 * (m[S+1] - J)
```

The state keeps the same `(S,J)`. The count of labels with `tmin = h`
decreases.

### Case 1(2), pivot chart

Source: PDF pp. 16-19.

```text
D rows J+1..h := u_new * D' with pivot entry 1
u_a := u_new * u'_a
new label p = (S,J+1)
T[p]^(q) := T[a]^(q) for q < S
T[p]^(q) := J for q >= S
tmin[p] := J
N[p] := N[a] + J1 * (m[S+1] - J)
```

Then apply Aoyagi's displayed regular column and row operations `Q` and `P`.
If `J+1 <= m[S+1]`, continue with `J := J+1`; otherwise replace the processed
product by a new `C'^(S+1)` and advance to `(S+1,0)`.

## Case 2

Source: PDF pp. 19-22.

Precondition: no active label has `tmin` in `J+1, ..., m[S]-1`; equivalently
the paper writes

```text
b_{J+1} = ... = b_{m[S]}.
```

Blow up the full residual block:

```text
D_J = 0.
```

In the pivot chart:

```text
new label p = (S,J+1)
T[p]^(q) := m[q+1] for q < S
T[p]^(q) := J for q >= S
tmin[p] := J
N[p] := (m[S] - J) * (m[S+1] - J)
```

Use the same `Q/P` elimination. Again either increment `J` or advance to
`(S+1,0)`.

## Termination measure

Candidate lexicographic measure:

```text
(L+1-S, min(m[S],m[S+1])-J, count of labels at the next Case-1 jump)
```

Case 1(1) decreases the count. Case 1(2) and Case 2 increase `J` or advance
`S`.

## Terminal theorem

At `S = L+1`, PDF p. 22 gives

```text
< prod_{s=1}^L C^(s) > = < diag(b_1, ..., b_{m[L+1]}) >.
```

The local normal-crossing candidate for the squared norm is

```text
candidate = 1/2 * min { N[s,k] : tmin[s,k] = 0 }.
```

The closed-form exponent certificate to prove by induction is

```text
N[s,k]
 =
(m[1] - t^(1)) * (m[2] - t^(1))
  + sum_{j=2}^L (t^(j-1) - t^(j)) * (m[j+1] - t^(j)).
```

PDF pp. 22-23 then repackage each `T[s,k]` by sequences `H_i`, `S_i`, `F_i`.
That belongs to the arithmetic/lower-bound certificate rather than the minimal
blow-up transition certificate.

## Risks and kill-conditions

- Missing chart risk: Aoyagi displays the `u_a` chart and one pivot chart. A
  formal proof must cover all pivot entries of the blown-up `D` block, probably
  by row/column permutations plus the same `Q/P` argument.
- Regularity risk: the matrix `P` contains ratios like `b'_i / b'_{J+1}`. Kill
  the certificate if divisibility/regularity is not derivable from the `b_i`
  recurrence.
- Notation risk: split residual widths `w_s` from prefix minima `m_S`.
- Completeness kill-condition: abort if any transition leaves an uncovered tail
  matrix, a non-diagonal active block at `S = L+1`, a negative exponent, a
  non-comparable pair of `T` vectors, or a mismatch with the closed-form `N`.
