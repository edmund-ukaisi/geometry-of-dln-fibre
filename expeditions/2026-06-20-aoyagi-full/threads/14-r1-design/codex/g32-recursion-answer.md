**Verdict: witness-confirmed, with one scoping caveat.**

The general-`L` recursion step is exact. There is no new obstruction at `L >= 3` from incompatible middle reductions, provided the reduced factors are defined from one transported product pivot, not by independently Schur-reducing each factor.

Let the chain be

```text
V_L --C_L--> V_{L-1} -- ... --C_1--> V_0
P = C_1 ... C_L
p = P[0,0]
```

with `p` a unit. Define, for each vertex `i`,

```text
u_i   = C_{i+1} ... C_L e_0        in V_i
phi_i = e_0^T C_1 ... C_i          in V_i^*
```

with empty products at the ends. Then

```text
phi_i(u_i) = p
C_i u_i = u_{i-1}
phi_{i-1} C_i = phi_i.
```

After normalising `psi_i = p^{-1} phi_i`, we have `psi_i(u_i)=1`. Thus each hidden vertex has a canonically transported line `R u_i` and hyperplane `ker psi_i`, and the compatibility equations give

```text
C_i(R u_i) ⊂ R u_{i-1}
C_i(ker psi_i) ⊂ ker psi_{i-1}.
```

Choose determinant-one local analytic bases adapted to these splittings. Equivalently, choose `Q_i` so that the first coordinate is a unit multiple of `psi_i`, the lower coordinates kill `u_i`, and `Q_i u_i` is a unit multiple of `e_0`. Then every transformed factor

```text
D_i = Q_{i-1} C_i Q_i^{-1}
```

has block form

```text
D_i = [ lambda_i   0  ]
      [    0      C'_i]
```

where `C'_i` has size `(M^i - 1) x (M^{i+1} - 1)`, and `prod_i lambda_i = p`.

Taking `Q_0` and `Q_L^{-1}` to be the usual Schur row/column eliminators for the product `P` gives

```text
Q_0 P Q_L^{-1}
=
[ p     0        ]
[ 0   Schur(P)  ].
```

But inner cancellation gives

```text
Q_0 P Q_L^{-1}
=
(Q_0 C_1 Q_1^{-1})(Q_1 C_2 Q_2^{-1}) ... (Q_{L-1} C_L Q_L^{-1})
=
[ p                 0 ]
[ 0   C'_1 ... C'_L  ].
```

Therefore

```text
Schur(P) = C'_1 ... C'_L
```

exactly, for arbitrary chain length.

The middle-factor issue is resolved by the same construction. A middle `Q_i` is not chosen twice. It is chosen once from the pair `(u_i, psi_i)`, and that same choice simultaneously clears the incoming and outgoing off-diagonal blocks because

```text
C_i u_i = u_{i-1}
psi_{i-1} C_i = psi_i.
```

So the middle factor is reduced on both sides, but only as the induced map

```text
ker psi_i  ->  ker psi_{i-1}.
```

It is not two independent Schur complements fighting each other.

For the norm/RLCT point: yes, the additivity must be scoped as

```text
G3.2: exact block/product algebra in the chart
+
S1.5: analytic change-of-variables / smooth-block norm split.
```

It is not the identity `||Q_0 P Q_L^{-1}||_F^2 = ||P||_F^2`, since the `Q_i` are unimodular/analytic, not orthogonal. The valid statement is that the generators are analytically transformed to regular coordinates plus the residual product coordinates, and S1.5 supplies the RLCT-preserving norm split.

Lean caveat: I would avoid formalising a globally single polynomial `Q_i` on the whole principal open `P[0,0] != 0` unless you prove a basis-extension lemma there. Locally analytically, or after refining to charts where a chosen coordinate of each `u_i` is a unit, the determinant-one adapted bases exist. For the recursion step and RLCT chart argument, that is enough.

So: no `L >= 3` obstruction. The sound formalisation target is the transported-line/hyperplane construction above, with `C'_i` defined as the lower-right block of the adapted transformed factor.