The requested product normal form is true with one correction: a pivot of `P` alone is not enough. The local chart must also choose compatible `q x q` suffix pivots through the chain. On such a chart the change of variables is explicit and unit-Jacobian.

**L=3 Normal Form**

Write `n_i = m_i - q` and block
```text
X1 = [ a  b ]   X2 = [ e  f ]
     [ c  d ]        [ g  h ]
```
with `a,e` `q x q`, and assume `e` and `p11 = ae + bg` are invertible. Set
```text
Y2 = h - g e^{-1} f
t  = a + b g e^{-1}        so t e = p11
c~ = c + d g e^{-1}
Y1 = d - c~ t^{-1} b
```
Then, with
```text
S = [ I   0 ]      L = [ I      0 ]
    [ -g e^{-1} I ]   [ -c~ t^{-1} I ],
```
we have
```text
S X2 = [ e  f ]              L X1 S^{-1} = [ t  b  ]
       [ 0  Y2 ]                            [ 0  Y1 ]
```
and therefore
```text
L X1 X2 = [ t  b  ] [ e  f  ]
          [ 0  Y1 ] [ 0  Y2 ]
        = [ t e   t f + b Y2 ]
          [ 0     Y1 Y2      ].
```
Since `L` and `te` are invertible,
```text
rank(X1 X2) <= q    iff    Y1 Y2 = 0.
```
This is the reduced chain `(m1-q, m2-q, m3-q)`.

**General Recursion**

Let `K_L = 0`. For each `i = L-1, ..., 1`, block
```text
X_i = [ A_i  B_i ]
      [ C_i  D_i ]
```
using the `q + (m_i-q)` row split and `q + (m_{i+1}-q)` column split. Define recursively
```text
alpha_i = A_i + B_i K_{i+1}
gamma_i = C_i + D_i K_{i+1}

K_i = gamma_i alpha_i^{-1}
Y_i = D_i - gamma_i alpha_i^{-1} B_i.
```
Equivalently, with
```text
M_i = [ I   0 ]
      [ -K_i I ],
```
one has
```text
M_i X_i M_{i+1}^{-1}
  = [ alpha_i  B_i ]
    [ 0        Y_i ].
```
Thus
```text
M_1 P = product_i (M_i X_i M_{i+1}^{-1})
      = [ alpha_1 ... alpha_{L-1}   * ]
        [ 0                         Y_1 ... Y_{L-1} ].
```
On the chart where every `alpha_i` is invertible,
```text
rank P <= q    iff    Y_1 Y_2 ... Y_{L-1} = 0.
```

**Jacobian**

The change of variables is a right-to-left composition of unit-triangular shears:

- `X_i -> X_i M_{i+1}^{-1}` has determinant `det(M_{i+1}^{-1})^{m_i} = 1`.
- `(alpha_i, B_i, gamma_i, D_i) -> (alpha_i, B_i, gamma_i, Y_i)` is the Schur shear `D_i -> D_i - gamma_i alpha_i^{-1} B_i`, determinant `1`.

So the full Jacobian is `+/-1`, the sign only coming from any row/column permutations used to choose the chart. The inverses `alpha_i^{-1}` appear only as analytic unit coefficients in shears. A genuine determinant factor appears only if one wrongly normalizes pivots to identity, e.g. by scaling with `alpha_i^{-1}` instead of using unit-triangular elimination.

**Exponent Bookkeeping**

After the tail normal form, write the front matrix in the matching coordinates as
```text
X0 M_1^{-1} = [ R  S ],   R in R^{m0 x q}.
```
The `R` block is the condition that `X0` kills the rank-`q` image of the tail. It gives an ordinary Morse block of dimension `m0 q`, hence RLCT shift `m0 q / 2`.

The reduced normal equations are the entries of
```text
Z = Y_1 ... Y_{L-1}.
```
On the normal slice the squared model is, up to analytic units and smooth variables,
```text
||R||^2 + ||Z||^2.
```
These are disjoint variable blocks, so RLCTs add:
```text
(1/2) m0 q + (1/2) minAdm(m1-q, ..., mL-q)
= (1/2)[m0 q + minAdm(reduced)].
```
It is a sum because both normal blocks vanish simultaneously on the same local stratum. A minimum would correspond to a product/alternative-component model, not a sum of squares in transverse normal variables.

**Correction On The `3,3,3`, `q=1` Codimension**

The stated codimension `4` is not the tuple-space codimension. For pairs of `3 x 3` matrices,
```text
codim { rank(X1 X2) <= 1 } = 3,
```
not `4`. The number `4` is the determinantal codimension of rank `<=1` inside a free `3 x 3` product matrix, or of special components such as one factor already having rank `<=1`.

In the normal chart above, the reduced variables are two `2 x 2` matrices `Y1,Y2` with condition `Y1Y2=0`. The dense reduced stratum has
```text
rank Y1 = rank Y2 = 1,   im(Y2) subset ker(Y1),
```
which has dimension `5` in the `8`-dimensional reduced space, hence codimension `3 = minAdm(2,2,2)`. The smooth pivot/off-diagonal variables are free directions and do not affect the RLCT.