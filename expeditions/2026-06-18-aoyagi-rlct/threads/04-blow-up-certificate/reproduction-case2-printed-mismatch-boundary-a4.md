# A4 Case 2 Printed Mismatch Boundary

Status: reproduced as a source-gap isolation target; Lean-proved and
post-reviewed.

## Source Situation

Aoyagi Case 2, PDF pp. 19-22, combines two pieces of data:

```text
t_(S,J+1)^i = M^(i+1),  i < S,
t_(S,J+1)^q = J,        q >= S,
```

and

```text
M'_(S,J+1) = (M(S)-J)(M^(S+1)-J).
```

Here `M^(i)` is an actual reduced layer width, while `M(S)` is the prefix
minimum. The terminal exponent formula on PDF p. 22 uses actual widths. In
the expedition notation, write:

```text
n_i    = M^(i),
mu_S   = M(S),
T_print(i) = n_(i+1) for i < S, and J for i >= S.
```

The already-proved terminal-exponent split gives:

```text
E(T_print) = (n_S-J)(n_(S+1)-J).
```

Thus the difference from the prefix-minimum formula printed in the Case 2
increment is:

```text
E(T_print) - (mu_S-J)(n_(S+1)-J)
  = (n_S-mu_S)(n_(S+1)-J).
```

Therefore the printed vector matches the prefix-minimum formula exactly in
the equal-row-width case `n_S = mu_S` or in the degenerate zero-column-factor
case `n_(S+1)=J`.

In the actual Case 2 continuation branch, the source condition

```text
J+1 <= mu_(S+1)
```

implies `J < n_(S+1)`, since `mu_(S+1) <= n_(S+1)`. Under a genuine prefix
drop `mu_S < n_S`, the two terminal exponents are therefore unequal.

## Boundary Assembly

Lean should record three finite arithmetic facts:

1. The exact difference identity:

```text
E(T_print) - (mu_S-J)(n_(S+1)-J)
  = (n_S-mu_S)(n_(S+1)-J).
```

2. The equality characterization over natural widths:

```text
E(T_print) = (mu_S-J)(n_(S+1)-J)
iff n_S = mu_S or n_(S+1)=J.
```

3. The source-branch mismatch corollary:

```text
mu_S < n_S and J+1 <= mu_(S+1)
imply E(T_print) != E(T_corrected).
```

This third statement is the one that should be quoted when excluding the
printed vector in a genuine continuation state.

## Caveats

- This does not prove a Case 2 transition theorem.
- This does not prove that the source has an erratum.
- This does not prove a reachable-state invariant forcing `mu_S = n_S`.
- This does not replace the corrected prefix-minimum certificate by source
  data.
- This does not prove chart production, pivot coverage, regularity,
  Jacobians, normal crossings, RLCT extraction, or termination.
