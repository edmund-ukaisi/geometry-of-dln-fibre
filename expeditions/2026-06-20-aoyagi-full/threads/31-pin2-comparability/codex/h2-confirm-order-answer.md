**FACT: Exact Algebra**

Assume \(A_0,A_1,P_{00}\) are invertible. Define

\[
S_s=T_s-Z_sA_s^{-1}Y_s,\qquad K=Z_1P_{00}^{-1}Y_0.
\]

The block-LDU identity gives

\[
R_{\mathrm{core}}=S_0(I-K)S_1.
\]

So, with

\[
B:=S_0S_1,\qquad D:=R_{\mathrm{core}}-S_0S_1=-S_0KS_1,
\]

the scalar gap is exactly

\[
G=\left|\|B+D\|_F^2-\|B\|_F^2\right|
 =\left|2\langle B,D\rangle_F+\|D\|_F^2\right|.
\]

**INFERENCE: Generic Corner-Clean Orders**

Write

\[
A_s=I+\varepsilon X_s,\quad
Y_s=\varepsilon \widehat Y_s,\quad
Z_s=\varepsilon \widehat Z_s,\quad
T_s=\varepsilon \widehat T_s.
\]

Then

\[
P_{00}-I
=\varepsilon(X_0+X_1)
+\varepsilon^2(X_0X_1+\widehat Y_0\widehat Z_1),
\]

\[
P_{01}
=\varepsilon \widehat Y_1
+\varepsilon^2(X_0\widehat Y_1+\widehat Y_0\widehat T_1),
\]

\[
P_{10}
=\varepsilon \widehat Z_0
+\varepsilon^2(\widehat Z_0X_1+\widehat T_0\widehat Z_1).
\]

Hence generically

\[
S_{\mathrm{reg}}
=
\varepsilon^2\left(
\|X_0+X_1\|_F^2+\|\widehat Y_1\|_F^2+\|\widehat Z_0\|_F^2
\right)
+O(\varepsilon^3),
\]

so

\[
\boxed{S_{\mathrm{reg}}=\Theta(\varepsilon^2)}
\]

for generic directions.

Also,

\[
S_s
=
\varepsilon\widehat T_s
-\varepsilon^2\widehat Z_s\widehat Y_s
+O(\varepsilon^3),
\]

and, since \(P_{00}^{-1}=I+O(\varepsilon)\),

\[
K
=
\varepsilon^2\widehat Z_1\widehat Y_0
+O(\varepsilon^3).
\]

Therefore

\[
B=S_0S_1=\varepsilon^2\widehat T_0\widehat T_1+O(\varepsilon^3),
\]

\[
D=-S_0KS_1
=
-\varepsilon^4\widehat T_0\widehat Z_1\widehat Y_0\widehat T_1
+O(\varepsilon^5).
\]

So generically:

\[
\boxed{K=\Theta(\varepsilon^2)}
\]

\[
\boxed{D=\Theta(\varepsilon^4)}
\]

\[
\boxed{\|D\|_F^2=\Theta(\varepsilon^8)}
\]

and

\[
\langle B,D\rangle_F
=
-\varepsilon^6
\left\langle
\widehat T_0\widehat T_1,\,
\widehat T_0\widehat Z_1\widehat Y_0\widehat T_1
\right\rangle_F
+O(\varepsilon^7).
\]

Thus, unless this leading inner product vanishes,

\[
\boxed{\langle B,D\rangle_F=\Theta(\varepsilon^6)}
\]

and the cross term dominates \(\|D\|_F^2\). Hence

\[
\boxed{G=\Theta(\varepsilon^6)}.
\]

Since \(S_{\mathrm{reg}}=\Theta(\varepsilon^2)\), the generic corner-clean relation is

\[
\boxed{G=\Theta(S_{\mathrm{reg}}^3)}.
\]

So the gap is certainly \(O(S_{\mathrm{reg}})\), but the sharp generic order is cubic in \(S_{\mathrm{reg}}\).

**Uniform Bound**

Bounded \(P_{00}^{-1}\) is necessary to keep \(K\) from acquiring a pole, but it is not by itself sufficient for a uniform bound

\[
G\le C_{\mathrm{core}}S_{\mathrm{reg}}
\]

over a full neighbourhood.

A clean local estimate is this. Let \(\rho\) be the full layer deviation size, for example the max of the norms of \(A_s-I,Y_s,Z_s,T_s\). If \(A_0^{-1},A_1^{-1},P_{00}^{-1}\) are uniformly bounded, then

\[
\|S_s\|=O(\rho),\qquad \|K\|=O(\rho^2),
\]

so

\[
G=O(\rho^6).
\]

Therefore \(G\le C S_{\mathrm{reg}}\) follows uniformly on any domain where

\[
S_{\mathrm{reg}}\gtrsim \rho^6.
\]

A stronger and more natural transverse condition is \(S_{\mathrm{reg}}\gtrsim \rho^2\), which is exactly what the generic corner-clean germ gives.

But corner-clean alone is not enough for a uniform bound on the whole neighbourhood, because \(S_{\mathrm{reg}}\) can be made much smaller than the hidden layer deviation by cancellations among \(P_{00}-I,P_{01},P_{10}\).

**Adversarial Curve**

Take the scalar case \(r=M_0=M_1=M_2=1\), with \(t\to0\), and set

\[
A_0=1,\quad A_1=1-t^2,\quad
Y_0=t,\quad Z_1=t,\quad T_0=T_1=t,
\]

\[
Y_1=-t^2+a t^3,\qquad
Z_0=-\frac{t^2}{1-t^2},
\]

where \(a\ne0\) is fixed.

Then

\[
P_{00}=1,\qquad P_{10}=0,\qquad P_{01}=a t^3,
\]

so

\[
S_{\mathrm{reg}}=a^2t^6.
\]

Meanwhile \(P_{00}^{-1}=1\), all layer blocks still approach the deepest corner, and

\[
G=2t^6+O(t^8).
\]

Hence

\[
\frac{G}{S_{\mathrm{reg}}}\to \frac{2}{a^2},
\]

so here

\[
\boxed{G=\Theta(S_{\mathrm{reg}})}.
\]

What breaks the higher order is not the Schur algebra. What breaks is the denominator: \(S_{\mathrm{reg}}\) no longer measures the full small parameter. The visible regular product blocks have been canceled down to order \(t^3\), while the hidden factors \(T_0,T_1,Y_0,Z_1\) remain order \(t\), so \(K=O(t^2)\), \(D=O(t^4)\), and the cross term remains \(O(t^6)\).

So the safe conclusion is:

\[
\boxed{\text{Generic corner-clean germ: } G=\Theta(S_{\mathrm{reg}}^3).}
\]

\[
\boxed{\text{Uniform } G\le C S_{\mathrm{reg}} \text{ needs bounded inverses plus a lower-control condition on } S_{\mathrm{reg}}.}
\]

Bounded \(P_{00}^{-1}\) alone is not sufficient. Corner-clean is needed for the generic order statement, but not sufficient for the uniform bound unless cancellations are excluded or \(S_{\mathrm{reg}}\) is enlarged to control the hidden layer deviations.