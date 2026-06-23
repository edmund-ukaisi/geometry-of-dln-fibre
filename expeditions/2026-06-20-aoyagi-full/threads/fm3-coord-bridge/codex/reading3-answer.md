**A. YES.**  
Conjunct 1 can hold as a bare algebraic equality, but the smooth-block step is invalid for `w.1 = Erow`: `d(E0,E1)|0 = 0`, so `E0,E1` are not regular coordinates and `E0²+E1²` is not a two-coordinate quadratic block.

**B. No honest regular split.**  
FORCED non-regular by homogeneity/order, under the stated exact conjunct-1 form. `L ∘ blowup` vanishes to order `4` at `0`: every `AB` entry contains at least `y0` times a `B`-linear term. If any `w_j` is a centered regular coordinate, then `w_j²` contributes a nonzero quadratic term to `∑ w_j²`; since the RHS is a sum of squares, that quadratic term cannot cancel. But the LHS has no quadratic part. So no `nReg = 2` regular coordinate block can satisfy conjunct 1 exactly near `0`.

**C. Exact: `rlctAtOn(E0²+E1²)(0) = 1/2`.**  
Method: analytic change of variables plus direct integrability. Set  
`u0 = b00 + y1 b10`, `u1 = b01 + y1 b11`; this is a local analytic diffeomorphism in the `b00,b01` directions. Then

```text
E0² + E1² = y0² (u0² + u1²).
```

The local integral factors as `∫ |y0|^{-2λ} dy0 · ∫ (u0²+u1²)^{-λ} du0 du1`, requiring `λ < 1/2` and `λ < 1`. Hence the threshold is `min(1/2,1) = 1/2`, not `1`. Passive variables do not change it. Numerically, the singular block is worse: the “larger contribution” phrasing is reversed if contribution means RLCT value.