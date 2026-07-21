Everything below follows from the stated normal form and elementary algebra; no additional preservation assumption is used.

## 1. Exact one-step witness law

Work in the ring of continuous germs on a chart. Write

\[
F=P\circ g,\qquad F_{ij}=b_1q_{ij},\qquad
b_1=\sum_{i,j}r_{ij}F_{ij}.
\]

Let \(\phi\) be the total child-to-parent source map. Thus

\[
g_{\mathrm{child}}=g_{\mathrm{parent}}\circ\phi,
\qquad
F_{\mathrm{child}}=\phi^*F=F\circ\phi.
\]

The pullback \(\phi^*\) includes the blow-up substitution and all determinant-one source shears. It never includes the left projection \(Q\).

Let

\[
\delta=\begin{cases}1,&J=0,\\0,&J>0.\end{cases}
\]

For both Case 1 charts,

\[
b'_1=u^\delta\,\phi^*b_1,
\]

where \(u\) is the existing divisor in Case 1(1), and the new exceptional divisor in Case 1(2). Consequently the witness laws are

\[
\boxed{\quad q'_{ij}=\frac{\phi^*q_{ij}}{u^\delta},\qquad
r'_{ij}=u^\delta\,\phi^*r_{ij}.\quad}
\]

Here \(q'=\phi^*q/u\) when \(J=0\) denotes a continuous quotient; it is not localization at \(u\). Its continuity follows from the blow-up center and the divisibility chain.

Indeed,

\[
F_{\mathrm{child}}
 =(\phi^*b_1)(\phi^*q)
 =b'_1q',
\]

and, whenever a parent Bézout witness exists,

\[
\sum r'_{ij}(F_{\mathrm{child}})_{ij}
=u^\delta\phi^*\!\left(\sum r_{ij}F_{ij}\right)
=u^\delta\phi^*b_1=b'_1.
\]

### Case 1(1)

Let \(e=u_{s,k}\) be the selected existing divisor. It previously first appeared at threshold \(J+J_1\), and is reassigned threshold \(J\). The chart map is

\[
d_{ab}=e\,d'_{ab}
\]

for the selected \(J_1\)-row block. The full \(b\)-vector changes by

\[
b'_i=
\begin{cases}
e\,\phi^*b_i,&J<i\le J+J_1,\\
\phi^*b_i,&\text{otherwise}.
\end{cases}
\]

Thus \(b'_1=e\,\phi^*b_1\) precisely when \(J=0\). No Schur projection occurs in this subcase.

### Case 1(2)

Let \(v=u_{S,J+1}\) be the new exceptional divisor. In the chosen pivot chart,

\[
e=v e',\qquad d_{ab}=v d'_{ab},
\]

with one selected \(d'\)-coordinate normalized to \(1\). The new divisor \(v\) receives threshold \(J\), while \(e'\) retains the former threshold. Hence

\[
b'_i=
\begin{cases}
v\,\phi^*b_i,&J<i\le J+J_1,\\
\phi^*b_i,&\text{otherwise},
\end{cases}
\]

and again \(b'_1=v\,\phi^*b_1\) exactly when \(J=0\).

If \(\beta\) denotes the raw blow-up chart and \(\sigma_P,\sigma_{\mathrm{Schur}}\) the determinant-one source shears, then, with the obvious order convention,

\[
\phi=\beta\circ\sigma_P\circ\sigma_{\mathrm{Schur}},
\qquad
\phi^*=\sigma_{\mathrm{Schur}}^*\circ\sigma_P^*\circ\beta^*.
\]

### What the left \(Q\) does

Suppose the allowed coordinate changes leave a residual core \(H_{\rm pre}\), and the row operation satisfies

\[
QH_{\rm pre}=H_{\rm child}.
\]

Then \(H_{\rm pre}=Q^{-1}H_{\rm child}\). After restoring row weights, the actual cofactor is the regular triangular matrix

\[
\widehat Q=\operatorname{diag}(b')Q^{-1}\operatorname{diag}(b')^{-1}.
\]

Its entries involve ratios \(b'_i/b'_j\) in the divisibility-allowed direction, so it is continuous. Therefore

\[
F_{\rm child}
=(\phi^*U)\widehat Q\,H_{\rm child}(\phi^*V).
\]

As a matrix cofactor, \(Q\) is invertible and remixes quotient witnesses covariantly. If \(H_{\rm child}=b'_1h\), then

\[
q'=(\phi^*U)\widehat Q\,h\,(\phi^*V).
\]

For a core Bézout coefficient matrix \(R_H\), it remixes coefficients contragrediently:

\[
R_F=((\phi^*U)\widehat Q)^{-T}R_H(\phi^*V)^{-T}.
\]

But \(Q\) does not act by composition on either witness. Interpreted as a source map, it clears one of the coordinates used to define it and has Jacobian determinant \(0\). It therefore cannot be included in \(\phi\).

For already-given witnesses on the actual matrix \(F\), the boxed pullback formulas contain the complete transformation law; there is no additional \(Q\)-composition.

A useful consistency check is that when \(J=0\), simultaneous parent witnesses for both (D) and (B) cannot actually exist. They would give

\[
1=\sum r_{ij}q_{ij},
\]

while on the child chart \(\phi^*q=u q'\), hence

\[
1=u\sum (\phi^*r_{ij})q'_{ij},
\]

which is impossible at \(u=0\).

## 2. Which identities hold at intermediate states?

### Divisibility (D): always

At every maintained state,

\[
F
=U\,\operatorname{diag}(b_i)
 \begin{bmatrix}E_J&0\\0&D_J\end{bmatrix}
 \Bigl(\prod_{s>S}C^{(s)}\Bigr)V.
\]

Since \(b_1\mid b_i\),

\[
F=b_1\,
U\,\operatorname{diag}\!\left(1,\frac{b_2}{b_1},\ldots\right)
 \begin{bmatrix}E_J&0\\0&D_J\end{bmatrix}
 \Bigl(\prod_{s>S}C^{(s)}\Bigr)V.
\]

Everything in the second factor is continuous. Thus (D) holds at every state.

### Bézout (B): not at states with a pending layer

Let \(q=F/b_1\). If \(S<L\), the factor

\[
\prod_{s>S}C^{(s)}
\]

vanishes at the chart origin. Hence

\[
q_{ij}(0)=0\qquad\text{for every }i,j.
\]

If (B) held, then on the dense set where the monomial \(b_1\neq0\),

\[
1=\sum_{i,j}r_{ij}q_{ij}.
\]

Continuity extends this identity to the origin, where its right-hand side is \(0\), a contradiction. In polynomial or analytic language, the residual ideal \(\langle q_{ij}\rangle\) is contained in the maximal ideal; indeed the pending product has positive order of vanishing.

Thus

\[
\boxed{\ S<L\quad\Longrightarrow\quad b_1\notin\langle F_{ij}\rangle.\ }
\]

When the tail is empty:

- At \(S=L,J=0\), the residual \(D_0\) still vanishes at the origin, so (B) remains false.
- At \(S=L,J\ge1\), the cleared block contains the entry \(b_1\). Hence (B) is true.
- In particular it is true at the terminal \(S=L+1\) chart.

Therefore (B) first appears when there is no pending tail and the first pivot has been cleared. A terminal Case 1(2) step \(J=0\to1\) can create (B); it is not transported from the parent, where no Bézout witness existed.

## 3. Correct invariant and terminal principality

The correct step-preserved statement is

\[
\boxed{\quad F=b_1q,\qquad
\langle F_{ij}\rangle=b_1\langle q_{ij}\rangle,\quad}
\]

together with the displayed normal form and the chain \(b_1\mid b_2\mid\cdots\). It asserts the inclusion

\[
\langle F_{ij}\rangle\subseteq\langle b_1\rangle,
\]

but does not assert that the residual ideal \(\langle q_{ij}\rangle\) is the unit ideal.

At the terminal chart,

\[
F=U\,\operatorname{diag}(b_1,\ldots,b_m)V.
\]

The divisibility chain gives

\[
\langle b_1,\ldots,b_m\rangle=\langle b_1\rangle.
\]

Since \(U(0)=V(0)=I\), both matrices have continuous inverses near the origin. Consequently

\[
\langle F_{ij}\rangle=\langle b_1\rangle.
\]

An explicit terminal Bézout witness is

\[
\boxed{\quad
r_{ij}=(U^{-1})_{1i}(V^{-1})_{j1},
\quad}
\]

because

\[
b_1=(U^{-1}FV^{-1})_{11}
=\sum_{i,j}(U^{-1})_{1i}F_{ij}(V^{-1})_{j1}.
\]

## 4. Minimal concrete Case 1 example

Take widths \((2,2,1)\), \(L=2\), and the state \(S=1,J=0,J_1=1\). Let

\[
b=(1,e),\qquad
D=\begin{pmatrix}x&y\\z&w\end{pmatrix},
\qquad
C=\binom cd,
\]

with \(\widetilde t(e)=1\). Then

\[
F=\operatorname{diag}(1,e)DC
=\binom{xc+yd}{e(zc+wd)}.
\]

The parent divisibility witness is

\[
q=\binom{xc+yd}{e(zc+wd)}.
\]

There is no parent Bézout witness because \(b_1=1\) while \(F(0)=0\).

In the Case 1(1) \(e\)-chart,

\[
x=ex',\qquad y=ey'.
\]

Then

\[
b'=(e,e),\qquad
F'=e\binom{x'c+y'd}{zc+wd},
\]

so

\[
q'=\binom{x'c+y'd}{zc+wd}=\frac{\phi^*q}{e}.
\]

In the Case 1(2) \(x\)-chart, put

\[
x=v,\quad y=va,\quad e=ve',\quad
w=h+za,\quad c=c'-ad',\quad d=d'.
\]

The last two substitutions are determinant-one source shears. Direct calculation gives

\[
F'
=v\binom{c'}{e'(zc'+hd')}.
\]

Thus

\[
b'=(v,ve'),\qquad
q'=\binom{c'}{e'(zc'+hd')}=\frac{\phi^*q}{v}.
\]

Here

\[
Q=\begin{pmatrix}1&0\\-z&1\end{pmatrix},
\qquad
P=\begin{pmatrix}1&-a\\0&1\end{pmatrix},
\]

and

\[
\begin{pmatrix}1&a\\z&h+za\end{pmatrix}
=Q^{-1}\begin{pmatrix}1&0\\0&h\end{pmatrix}P^{-1}.
\]

The \(P\)-action is exactly the tail shear \(c=c'-ad'\). The \(Q\)-action would send the source coordinate \(z\) to \(0\), so it is not part of \(\phi\); it remains the regular weighted left cofactor

\[
\begin{pmatrix}1&0\\e'z&1\end{pmatrix}.
\]

After either chart, \(q'(0)=0\), so no child Bézout witness exists. This example exhibits both the extra \(b_1\)-factor at \(J=0\) and the failure of per-step principality.