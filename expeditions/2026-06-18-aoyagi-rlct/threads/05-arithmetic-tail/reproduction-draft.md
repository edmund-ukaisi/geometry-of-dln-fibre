# Pen-and-paper reproduction draft - arithmetic tail

Status: draft reproduction from xhigh scout `Raman`, integrated by the
controller. This has not yet passed the independent reproduction check.

Source: Aoyagi 2023 PDF pp. 22-27. Paper source only.

## Definition 3 parameters

Let

```text
M^(s) = H^(s) - r,      s = 1, ..., L+1.
```

Definition 3 chooses an indexed subcollection

```text
M = (M^(S_1), ..., M^(S_(ell+1)))
```

such that, writing

```text
B = sum_{k=1}^{ell+1} M^(S_k),
```

the selected and unselected values satisfy

```text
M^(S_j) < M^(s)                 for M^(s) not in M,
B > ell M^(s)                  for M^(s) in M,
B <= (ell - 1) M^(s)           for M^(s) not in M.
```

Let `M` be the integer with

```text
M - 1 < B / ell <= M,
```

and define

```text
a = B - (M - 1) ell.
```

Notation hazard: the source prints `M` both for the selected collection and the
integer. Lean should use distinct names, for example `selected`, `meanCeil`,
and `aoyagiA`.

## Terminal exponent expression

For a terminal vector `T_{s,k}`, choose values

```text
H_j in {t^(1)_{s,k}, ..., t^(L)_{s,k}},
S_j < S_(j+1),
```

with

```text
H_j <= H_(j-1),
H_j <= M^(S_(j+1)),
H_ell = 0.
```

Aoyagi writes

```text
M_{s,k}
  = (M^(S_1) - H_1)(M^(S_2) - H_1)
    + sum_{j=2}^ell (H_(j-1) - H_j)(M^(S_(j+1)) - H_j).
```

Define

```text
F_1 = M^(S_1) + M^(S_2) - H_1,
F_j = H_(j-1) - H_j + M^(S_(j+1))      for 2 <= j <= ell.
```

Then

```text
H_j = - sum_{l=1}^j F_l + sum_{l=1}^{j+1} M^(S_l),
sum_{l=1}^ell F_l = B.
```

## Quadratic form

Eliminating `F_ell`, with

```text
mean = B / ell,
```

the variable part of `M_{s,k}` is reproduced as

```text
M_{s,k}
  = 1/2 sum_{j=1}^{ell-1} (F_j - mean)^2
    + 1/2 (sum_{j=1}^{ell-1} F_j - (ell-1) mean)^2
    - ell(ell-1)/2 * mean^2
    + sum_{1 <= i < j <= ell+1} M^(S_i) M^(S_j).
```

Since

```text
B = ell (M - 1) + a,
mean = M - 1 + a/ell,
```

the integer minimizers should have the free `F_j` values equal to `M-1` or `M`.
If `b` of the `ell-1` free values are `M`, Aoyagi's varying quadratic becomes

```text
A(b) / ell^2
  = b ((ell-a)/ell)^2
    + (ell-1-b) (-a/ell)^2
    + (b(ell-a)/ell - (ell-1-b)a/ell)^2.
```

Equivalently,

```text
A(b)
  = b(ell-a)^2
    + (ell-1-b)a^2
    + (b(ell-a) - (ell-1-b)a)^2.
```

## Lemma 3

Aoyagi differentiates this quadratic in `b`:

```text
A'(b) = ell^2 (1 + 2b - 2a).
```

The real minimizer is `b = a - 1/2`, so the integer minimizers are
`b = a - 1` and `b = a`, when both lie in the allowed range. Substitution gives

```text
A(a-1) = A(a) = a ell (ell-a).
```

Thus the varying quadratic part contributes

```text
a(ell-a)/(2 ell).
```

Aoyagi obtains

```text
2 lambda_O
  = min M_{s,k}
  = a(ell-a)/(2 ell)
    - ell(ell-1)/2 * (B/ell)^2
    + sum_{1 <= i < j <= ell+1} M^(S_i) M^(S_j).
```

The full theorem then adds the rank block from the product reduction:

```text
lambda
  = (-r^2 + r(H^(1)+H^(L+1))) / 2
    + (1/2) * (2 lambda_O).
```

## Lemmas 4 and 5

The paper defines extremal chains `H_tilde` and `H_tilde'` on PDF p. 25. They
encode two minimizing `F` patterns:

- `H_tilde`: `a` entries `F_j = M`, then `ell-a` entries `F_j = M-1`.
- `H_tilde'`: the reverse order.

Lemma 4 says: if

```text
T_tilde <= T_{s,k} <= T_tilde'
```

and all

```text
F_j = H_(j-1) - H_j + M^(S_(j+1))
```

are either `M-1` or `M`, then `T_{s,k}` corresponds to `lambda`.

Reason reproduced by the scout: since `sum F_j = B`, exactly `a` of the `ell`
values are `M`. Hence among the free `F_1, ..., F_(ell-1)`, the count `b` is
either `a` or `a-1`, exactly the Lemma 3 minimizing cases.

For Lemma 5, set

```text
I_j = { H : H_tilde_j <= H <= H_tilde'_j }.
```

The size is

```text
|I_j| =
  j + 1                                      if j <= min(a, ell-a),
  min(a, ell-a) + 1                          if min(a, ell-a)+1 <= j <= max(a, ell-a),
  min(a, ell-a) + 1 + max(a, ell-a) - j      if max(a, ell-a)+1 <= j <= ell.
```

The effective order count is

```text
1 + sum_{j=1}^{ell-1} (|I_j| - 1) = 1 + a(ell-a).
```

Aoyagi asserts equality by constructing local coordinates from the displayed
families of `T_{s,k}` on PDF pp. 26-27, especially using Case 1(2).

## Boundary hazards and kill-conditions

- Definition 3 behaves like an ordered indexed subcollection, not a literal set.
  Equal layer widths need careful treatment.
- The paper's Lemma 3 assumes `0 <= a,b <= ell-1`, but Definition 3 can appear
  to produce `a = ell`. This boundary gives single minimizer `b = ell-1` and
  `theta = 1`; source fidelity must be checked before Lean fixes the statement.
- `a = 0` is not produced by the strict Definition 3 inequality, but if allowed
  conventionally, the minimizer is `b = 0` and `theta = 1`.
- Do not use `A(a-1) = A(a)` blindly at `a = 0` or `a = ell`.
- Lemma 5's bound gives `a(ell-a)+1` after counting `|I_j|-1` plus the
  Case 1(2) pivot, not by raw summation of `|I_j|`.
- Equality in Lemma 5 depends on the piecewise `T_{s,k}` constructions being
  admissible in all index ranges. Empty ranges and exclusions must be checked
  case by case.
