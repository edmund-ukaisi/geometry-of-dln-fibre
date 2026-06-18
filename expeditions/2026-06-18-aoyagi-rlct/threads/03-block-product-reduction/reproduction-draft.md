# Pen-and-paper reproduction draft - Lemma 2 and Theorem 3

Status: draft reproduction from xhigh scout `Galileo`, integrated by the
controller. This has not yet passed the independent reproduction check.

Source: Aoyagi 2023 PDF pp. 10-13. Paper source only.

## Setup

Let `A^(s)` be an `H^(s) x H^(s+1)` matrix, so
`A^(1) ... A^(L)` is `H^(1) x H^(L+1)`. Fix product rank `r`.
After constant row/column changes, Aoyagi assumes the true product is

```text
A*^(1) ... A*^(L) = [ I_r  0
                      0    0 ].
```

Controller caution: the scout called this normalization RLCT-safe using
Aoyagi's Lemma 1. That lemma is analytic ideal-generator background on PDF p. 5.
The expedition cannot silently cite it as a second Lean analytic interface.
Either prove/avoid the needed algebraic generator replacement or include the
exact needed content in the single allowed normal-crossing extraction interface
after review.

## Lemma 2: full-rank block reduction

Hypotheses:

```text
A = [ A1  A2
      A3  A4 ],
```

where `A` is `h1 x h2`, `rank(A) = r1`, `r <= r1`, and `A1` is an
invertible `r x r` block. Work on the open chart `det(A1) != 0`.

Define

```text
Q1 = [ I_r         0
       -A3 A1^-1   I ],

Q2 = [ I_r  -A1^-1 A2
       0     I        ].
```

Then

```text
Q1 A = [ A1  A2
         0   A4 - A3 A1^-1 A2 ].
```

Set the Schur complement

```text
C4 := A4 - A3 A1^-1 A2.
```

Right multiplication gives

```text
Q1 A Q2 = [ A1  0
            0   C4 ].
```

Aoyagi's displayed coordinate form sets

```text
F2 := -A1^-1 A2,
F3 := -A3 A1^-1,
```

so that

```text
Q1 = [ I_r  0
       F3   I ],
Q2 = [ I_r  F2
       0    I ].
```

The rank conclusion is algebraic:

```text
rank(A) = rank(Q1 A Q2)
        = rank(A1) + rank(C4)
        = r + rank(C4).
```

Therefore `rank(C4) = r1 - r`.

The coordinate change is invertible on the chart `det(A1) != 0`:

```text
A2 = -A1 F2,
A3 = -F3 A1,
A4 = C4 + F3 A1 F2.
```

Reproduction status: algebraic block calculation reproduced; analytic use of
local coordinate invariance not yet checked against the allowed citation
boundary.

## Theorem 3: iterated product reduction

Target statement: after local analytic coordinate changes, there are triangular
invertible matrices

```text
P1 = [ I_r  0
       F3   I_(H^(1)-r) ],

P2 = [ I_r  F2
       0    I_(H^(L+1)-r) ],
```

such that

```text
P1 (A^(1) ... A^(L)) P2
  = [ C1   0
      0    C^(1) C^(2) ... C^(L) ],
```

with `C1` an invertible `r x r` block and each
`C^(s)` an `(H^(s)-r) x (H^(s+1)-r)` matrix.

### Base case

Partition

```text
A^(1) = [ A1^(1)  A2^(1)
          A3^(1)  A4^(1) ],
```

with `A1^(1)` invertible. Lemma 2 gives

```text
Q1^(1) A^(1) Q2^(1)
  = [ A1^(1)  0
      0        C^(1) ].
```

### Induction step

Assume for `S` layers:

```text
Q1' (A^(1) ... A^(S)) Q2'
  = [ C1'  0
      0    D ],

D := C^(1) ... C^(S),
```

with `C1'` invertible. Absorb the old right triangular matrix into the next
layer:

```text
A'^(S+1) := (Q2')^-1 A^(S+1)
          = [ A1'  A2'
              A3'  A4' ].
```

Then

```text
Q1' (A^(1) ... A^(S)) A^(S+1)
 = [ C1' A1'   C1' A2'
     D A3'     D A4'   ].
```

Assuming `A1'` is invertible, left-eliminate with

```text
Q1'' = [ I_r                   0
         -D A3' (C1' A1')^-1   I ].
```

The lower-right block becomes

```text
D A4' - D A3' (C1' A1')^-1 C1' A2'
  = D (A4' - A3' A1'^-1 A2').
```

Define

```text
C^(S+1) := A4' - A3' A1'^-1 A2'.
```

Right-eliminate with

```text
Q2'' = [ I_r  -A1'^-1 A2'
         0     I_(H^(S+2)-r) ].
```

This gives

```text
Q1'' Q1' (A^(1) ... A^(S+1)) Q2''
 = [ C1' A1'   0
     0          D C^(S+1) ].
```

Set

```text
C1'' := C1' A1',
F2'' := -A1'^-1 A2',
F3'' := F3' - D A3' (C1' A1')^-1.
```

This preserves the triangular shapes of `P1` and `P2`.

## Product/RLCT reduction after Theorem 3

After Theorem 3 and true-product normalization,

```text
P1 (A^(1) ... A^(L) - A*^(1) ... A*^(L)) P2
 =
[ C1 - I_r        -F2
  -F3             C^(1) ... C^(L) - F3 F2 ].
```

Thus the product-difference ideal is equivalent algebraically to

```text
J = < C1 - I_r, F2, F3, C^(1) ... C^(L) - F3 F2 >.
```

Since `F3 F2` lies in `<F2, F3>`, the generated ideal is also

```text
J' = < C1 - I_r, F2, F3, C^(1) ... C^(L) >.
```

The regular coordinates are

```text
C1 - I_r,
F2,
F3.
```

Their count is

```text
r^2 + r(H^(L+1)-r) + r(H^(1)-r)
  = -r^2 + r(H^(1)+H^(L+1)).
```

Aoyagi concludes

```text
lambda < A^(1) ... A^(L) - A*^(1) ... A*^(L) >
 =
(-r^2 + r(H^(1)+H^(L+1))) / 2
  + lambda < C^(1) ... C^(L) >.
```

Controller caution: the equality of generated ideals is algebraic, but the
additivity of `lambda` after splitting independent regular quadratic
coordinates is analytic/RLCT input. This must be handled by the single allowed
analytic interface or proved/avoided; it cannot become a hidden second citation.

## Boundary cases and kill-conditions

- The reduction is valid only on charts where each required `r x r` block is
  invertible. If `det(A1) = 0`, Lemma 2 needs a different chart.
- Theorem 3 has a hidden preliminary basis-choice requirement: from
  `rank(A*^(1) ... A*^(L)) = r`, one must choose `r`-dimensional subspaces
  through the layers so the restricted true factors are full rank. Product
  normalization alone does not justify every displayed `A1` invertibility.
- Zero-size blocks must be allowed: `r = 0`, `r = H^(1)`, `r = H^(L+1)`, or
  some `H^(s) = r`. Empty matrices should make the formulas degenerate
  correctly.
- The RLCT step needs the prior nonvanishing near the base point.
- The exact analytic status of local coordinate invariance, ideal-generator
  replacement, and regular-coordinate additivity remains unchecked against the
  user's single-citation boundary.
