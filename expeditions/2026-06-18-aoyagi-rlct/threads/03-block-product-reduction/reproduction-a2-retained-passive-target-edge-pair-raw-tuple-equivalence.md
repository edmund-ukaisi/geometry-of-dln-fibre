# A2 retained-passive target edge-pair raw-tuple equivalence: reproduction

## Object

Fix a retained-passive base tuple `z` and write `coord` for its reconstructed
coordinate data.  A raw topology tuple is

```text
w = (A1passive, F2, A3passive, C, Ctop, F3).
```

The already packaged target edge-pair map sends `w` to the separated pair
`(U_F, U_C)` where

```text
X = retainedPassiveTargetRecoveredF2At z w,
Xsucc(last) = 0,
Xsucc(p.castSucc) = cast (X p.succ),

U_F(q) = F2(q) + rawA1(w,q) * coord.F2(q.castSucc) - Xsucc(q) * coord.C(q),
U_C(q) = C(q) + rawA3(w,q) * coord.F2(q.castSucc).
```

This pair map is not invertible by itself because it forgets
`A1passive`, `A3passive`, `Ctop`, and `F3`.  The honest equivalence is the raw
tuple endomap that fixes these four side fields and replaces only `(F2,C)` by
`(U_F,U_C)`.

## Inverse Calculation

Given a normalized target tuple

```text
y = (A1passive, U_F, A3passive, U_C, Ctop, F3),
```

recover

```text
X(q) = (coord.solvedA1 q)^(-1) * (coord.F2(q.succ) * U_C(q) - U_F(q)).
```

Equivalently, `X` is the first component of

```text
(retainedPassiveFormalRawF2CLinearEquivAt hz).symm (U_F, U_C).
```

Define

```text
Xsucc(last) = 0,
Xsucc(p.castSucc) = cast (X p.succ),

F2(q) = U_F(q) - rawA1(y,q) * coord.F2(q.castSucc) + Xsucc(q) * coord.C(q),
C(q) = U_C(q) - rawA3(y,q) * coord.F2(q.castSucc).
```

The side fields of the inverse are those of `y`.

## Check: Forward After Inverse

For `w = inverse(y)`, the side fields agree with those of `y`.  The backward
target recovery recurrence on `w` returns the above `X`.

At the terminal edge, the recovered value is

```text
(coord.solvedA1 q)^(-1) *
  (coord.F2(q.succ) * (C(q) + rawA3(y,q)*H(q))
    - (F2(q) + rawA1(y,q)*H(q)))
```

with `H(q)=coord.F2(q.castSucc)`.  Substituting the inverse formulas cancels
the side terms and gives

```text
(coord.solvedA1 q)^(-1) * (coord.F2(q.succ) * U_C(q) - U_F(q)) = X(q).
```

At a nonterminal edge the same substitution leaves

```text
U_F(q) + Xsucc(q)*coord.C(q) - Xsucc(q)*coord.C(q) = U_F(q),
```

using the induction hypothesis that the successor recovered value is
`X(q.succ)`.  Thus the forward target shear sends the inverse tuple back to
`(U_F,U_C)`.

## Check: Inverse After Forward

For an arbitrary `w`, let `(U_F,U_C)` be the target edge-pair shear and let
`X = retainedPassiveTargetRecoveredF2At z w`.  Applying the formal edge-pair
inverse to `(U_F,U_C)` has first component `X`: the terminal calculation is
exactly the recurrence defining `X(last)`, and the nonterminal calculation is
the recurrence defining `X(q)` after the already recovered successor is cast
into `Xsucc(q)`.

The raw inverse then gives

```text
U_C(q) - rawA3(w,q)*H(q) = C(q),
U_F(q) - rawA1(w,q)*H(q) + Xsucc(q)*coord.C(q) = F2(q).
```

So the inverse recovers the original raw tuple.

## Boundary

This proves a target-side raw tuple equivalence fixing all non-edge-pair
fields.  It does not by itself prove determinant one.  The formal edge-pair
equivalence has nontrivial determinant factors, so determinant-one must be
proved separately from a unitriangular shear factorization or a direct
determinant computation for this raw tuple endomap.
