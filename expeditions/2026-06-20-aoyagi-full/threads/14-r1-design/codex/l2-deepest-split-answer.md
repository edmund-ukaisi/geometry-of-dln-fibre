**Truth-Value: A**

At the deepest point this is **not constant-rank-gated**. The offending `x2*x3` term is removable by an explicit finite change. The only caveat is that the literal coefficient-one square normal form uses `sqrt` of a positive analytic unit; the RLCT argument itself can avoid even that and use only unit-division plus comparison.

**FACT | PURE-ALGEBRA + UNIT-DIVISION**

Let `p = a01`, `q = b10`, `u = a11`, `v = b11`, and

```text
D = 1 - p*q + x1.
```

After your `Phi` coordinates, replace `(u,v)` by determinant-core variables

```text
U = (u*(1 + x1) - p*x3) / D
V = v - q*x2/(1 + x1).
```

This is a local diffeomorphism: denominators are units, and the Jacobian in `(u,v)` is the identity at `0`.

Then the Schur-complement identity gives exactly

```text
E11 = U*V + x2*x3/(1 + x1).
```

So

```text
F = x1^2 + x2^2 + x3^2 + (U*V + h*x2*x3)^2,
h = 1/(1 + x1).
```

This is the load-bearing algebraic reduction. The original mixed terms are not intrinsic; they are artifacts of using `(a11,b11)` rather than determinant-core variables.

**FACT | COMPLETE-THE-SQUARE, NO IFT**

Set

```text
S = 1 + h^2*x3^2,
R = sqrt(S).
```

`S` is a positive analytic unit near `0`, and `R(0)=1`.

Define

```text
y1 = x1
y3 = x3
C1 = U
C2 = V / R
y2 = R*x2 + h*x3*U*V/R
```

Equivalently, since `C2 = V/R`,

```text
y2 = R*x2 + h*x3*C1*C2.
```

Then exactly

```text
F = y1^2 + y2^2 + y3^2 + (C1*C2)^2.
```

The inverse is explicit:

```text
x1 = y1
x3 = y3
U  = C1
V  = R*C2
x2 = (y2 - h*y3*C1*C2)/R
```

with `h = 1/(1+y1)` and `R = sqrt(1+h^2*y3^2)`. The Jacobian at the origin is `1`.

So Q1/Q2: **yes**, there is a closed-form local analytic diffeomorphism. It is finite triangular completion-of-squares, not constant-rank, Morse-Bott, or IFT. If your Lean primitive set literally excludes `sqrt` of positive units, then exact coefficient-one squares need a small “positive unit has smooth square root” lemma; that is still far below the constant-rank theorem.

**FACT | RLCT SQUEEZE**

Even without the `sqrt` normalization, the RLCT value is unchanged. From

```text
F = Rreg + (A + B)^2
Rreg = x1^2 + x2^2 + x3^2
A = U*V
B = h*x2*x3
G = Rreg + (U*V)^2
```

on a small neighborhood with `|h| <= H` and `|x2|, |x3| <= eps`,

```text
F <= (1 + 2*H^2*eps^2)*Rreg + 2*(U*V)^2 <= K+ * G
```

and

```text
G <= Rreg + 2*(A+B)^2 + 2*B^2
  <= (3 + 2*H^2*eps^2) * F.
```

Thus `F` and `G` are two-sided comparable. By RLCT monotonicity/comparison,

```text
RLCT(F) = RLCT(x1^2+x2^2+x3^2 + (U*V)^2)
        = 3/2 + lambdaCore((1,1,1)).
```

For the scalar-scalar core `(U*V)^2`, `lambdaCore = 1/2`, hence the value is `2`.

**INFERENCE**

The deepest point tips to **A**. The structural reason is exactly that the singular core has no linear part: after the Schur-complement/determinant coordinate change, all regular-core entanglement collapses to the universal term

```text
U*V + h*x2*x3,
```

and the `x2^2` regular square removes it by one explicit completion-of-the-square. No constant-rank theorem is needed for this point.