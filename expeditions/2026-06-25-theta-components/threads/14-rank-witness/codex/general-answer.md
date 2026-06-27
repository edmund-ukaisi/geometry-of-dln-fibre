**Q1. Split**

PROVEN. For every `A in Fib`, no genericity is needed.

Choose `W_0 = ker(E_r)` and `W_N` complementary to `U_N`. For each internal `i`, choose a complement `W_i` to `U_i` containing `(A_i...A_1)(W_0)`. This is possible because if `(A_i...A_1)x in U_i` for `x in W_0`, then applying `A_N...A_{i+1}` gives `E_r x = 0`; since `U_i -> U_N` is an isomorphism, the vector was already zero.

In these bases, every prefix `R_i` has no upper-right block:
```text
R_i = [ iso   0
        0   Rbar_i ]
```
while every suffix `L_i` is block upper triangular and induces `Lbar_i` on quotients. Hence the quotient endpoint block of
```text
L_i dA_i R_i
```
is exactly
```text
Lbar_i (dA_i)_quot Rbar_i.
```
So the quotient image is exactly
```text
I(Abar) = sum_i im(Lbar_i) tensor Ann ker(Rbar_i).
```

The remaining endpoint block is the subspace of maps `V_0 -> V_N` with zero quotient-to-quotient block. Its dimension is
```text
dim Hom(U_0,V_N) + dim Hom(W_0,U_N)
= r d_N + r(d_0-r)
= r(d_0+d_N-r) = delta.
```
Equivalently, the `U_0 -> U_N` overlap is counted once, so there is no extra `-r^2` correction beyond the one already built into `delta`.

Thus:
```text
rank J(A) = delta + dim I(Abar).
```

**Q2. Generic Top Stratum**

GAP as stated from the supplied facts.

For zero-product reps, `dim I(B)` is exactly the rank of the differential of the product map at `B`. Therefore
```text
dim I(B) = C_sh
```
is equivalent to saying that the product-zero scheme is generically smooth/reduced along that top component.

The clean obstruction is:
```text
Ext^1_{Lambda}(B,B),   Lambda = k A_N / <full path 0 -> N>.
```
By Voigt’s tangent-space theorem, `ker d(product) / tangent orbit` is controlled by this Ext group. Thus the desired equality holds on a dense top orbit iff the corresponding top Kostant module is rigid over this bound-quiver algebra:
```text
Ext^1_Lambda(B,B) = 0.
```

Known type-A quiver orbit-closure results give normal/CM/rational singularities for ordinary path-algebra orbit closures, but that does not by itself prove generic reducedness for the scheme cut out only by `B_N...B_1=0`. ([arxiv.org](https://arxiv.org/abs/1307.6261?utm_source=openai)) Classical “variety of complexes” results concern consecutive relations, not exactly this single long-product relation. ([arxiv.org](https://arxiv.org/abs/1504.00339?utm_source=openai))

So: PROVEN if one supplies the theorem “top Kostant modules for `kA_N/<full path>` are rigid” or “the long-product zero scheme is generically reduced along every top orbit”; otherwise this is the main GAP.

**Q3. Global Minor**

FALSE in the strong “nonvanishing on the entire generic locus” sense.

Counterexample: `N=2`, `d=(1,2,1)`, `r=0`. The equation is
```text
B_2 B_1 = 0
```
with `B_1` a column and `B_2` a row. This is the irreducible quadric `x_1 y_1 + x_2 y_2 = 0`, so `theta=1`, `Q=1`. The Jacobian row is
```text
[y_1, y_2, x_1, x_2].
```
On the smooth generic locus `B_1 != 0`, `B_2 != 0`, no single coordinate minor is nonzero everywhere: each coordinate can vanish at some smooth generic point.

If “global minor” only means “nonzero at the generic point of each top component,” then `theta=1` implies existence, but `theta>1` failing is a separate Jacobian-matroid statement, not a consequence of `theta` alone. The verified per-component behavior is evidence, not a general proof.

Target saturation `Q=d_N d_0` does not change this; common-minor existence is a column/basis issue, not a row-count issue.

**Q4. Kill Probes**

PROVEN split survives in all cases below by Q1; the only possible failure is Q2 rigidity/generic reducedness.

1. `(d,r)=((2,3,2),1)`, shifted `(1,2,1)`. Prediction: survives. This is the irreducible quadric probe above after shifting; good for killing the strong Q3 claim.

2. `(d,r)=((2,3,4),1)`, shifted `(1,2,3)`. Prediction: top rank is `delta + C_sh`, but lower-dimensional strata can have larger shifted differential rank. Good scope test: `Q` is top-generic, not all-fibre.

3. `(d,r)=((2,2,2,2),0)`. Prediction: split survives; generic top rank should be `C_sh` if the bound-quiver rigidity theorem holds. This is the smallest useful multi-arrow, multi-component zero-product stress test beyond scalar products.
