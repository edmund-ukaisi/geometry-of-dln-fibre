### 1. \((2,2,4)\) sub-core

**VERDICT — FACT:** The ideal fully monomializes; every final chart contains the divisor from blowing up \(\Delta=0\), with ratio \(2\), and this divisor binds.

**FACT.** Write
\[
\Delta=\begin{pmatrix}a&b\\c&d\end{pmatrix}.
\]
Blow up \((a,b,c,d)=0\). Up to row/column permutations, the \(a\)-chart is
\[
a=u,\quad b=u\beta,\quad c=u\gamma,\quad d=u(\gamma\beta+\delta),
\qquad J=u^3.
\]
Unimodular transformations give
\[
\Delta S\sim u
\begin{pmatrix}
X_1&\cdots&X_4\\
\delta Y_1&\cdots&\delta Y_4
\end{pmatrix}.
\]

**FACT.** Blow up \(X_1,\dots,X_4,Y_1,\dots,Y_4=0\).

- **FACT — \(X\)-pivot charts.** Put
  \[
  X_1=v,\quad X_j=v\xi_j,\quad Y_j=v\eta_j,\qquad J_{\rm new}=v^7.
  \]
  Column and row elimination gives
  \[
  \Delta S\sim uv
  \begin{pmatrix}
  1&0&0&0\\
  0&\delta z_2&\delta z_3&\delta z_4
  \end{pmatrix},
  \quad z_j=\eta_j-\eta_1\xi_j.
  \]
  Blow up \((z_2,z_3,z_4)\); in a \(z_\ell=w\) chart, \(J_{\rm new}=w^2\), and
  \[
  (b_1,b_2)=(uv,\ uv\delta w),\qquad
  J=u^3v^7w^2.
  \]

- **FACT — \(Y\)-pivot charts.** Put \(Y_1=v\), obtaining
  \[
  \Delta S\sim uv
  \begin{pmatrix}
  x&z_2&z_3&z_4\\
  \delta&0&0&0
  \end{pmatrix}.
  \]
  Blow up \(Q=(x,\delta,z_2,z_3,z_4)\); if its exceptional coordinate is \(r\), then \(J_{\rm new}=r^4\).

  \[
  \begin{array}{c|c|c}
  r & \text{remaining blow-up} & (b_1,b_2)\\ \hline
  x & (z'_2,z'_3,z'_4),\ z'_\ell=w & (uvr,\ uvr\,\delta' w)\\
  \delta & (z'_2,z'_3,z'_4),\ z'_\ell=w & (uvr,\ uvrw)\\
  z_\ell & \text{none} & (uvr,\ uvr\delta')
  \end{array}
  \]
  Here \(J=u^3v^7r^4w^2\) in the first two types and \(u^3v^7r^4\) in the last.

**FACT.** The nonzero divisor ratios are
\[
u:\frac{3+1}{2}=2,\qquad
v:\frac{7+1}{2}=4,\qquad
r:\frac{4+1}{2}=\frac52.
\]
The coordinates \(w,\delta,\delta'\) do not divide \(b_1\), so \(k=0\) there. Thus every chart binds at \(u=0\), and
\[
\operatorname{rlct}\|\Delta S\|^2=2.
\]

### 2. Full \((3,3,4)\)

**VERDICT — FACT:** Both descriptions are valid: \(4=2+2\) by disjoint additivity, but one further allowed blow-up realizes it literally as a single divisor with \(h+1=8\).

**FACT.** After the given splitting, blow up \(T=0\):
\[
T=q(1,\tau_2,\tau_3,\tau_4),\qquad J=q^3,
\]
and use column operations to make the top row \((q,0,0,0)\). Blow up \(\Delta=0\), with coordinate \(u\) and \(J=u^3\).

**FACT.** Blow up the coordinate intersection \((q,u)=0\). In the \(q\)-chart
\[
q=e,\qquad u=e\alpha,\qquad J_{\rm blow}=e,
\]
hence
\[
q^3u^3J_{\rm blow}=e^7\alpha^3.
\]
Thus \(h_e=7\), \(\operatorname{ord}_e I=1\), and
\[
\frac{h_e+1}{2}=\frac8{2}=4.
\]

**FACT.** Clearing the first bottom-column entries leaves a free \(2\times3\) residual block. In its \(X\)-pivot deepest chart, blowing its six coordinates gives \(v^5\), and blowing the remaining two-vector gives \(w\). The exact diagonal monomials are
\[
(b_1,b_2,b_3)
=(e,\ e\alpha v,\ e\alpha v\delta w),
\qquad b_1\mid b_2\mid b_3.
\]

**FACT.** Therefore the “single divisor” reading is literally correct in this deepest chart. Its Jacobian exponent is \(7\), not \(8\); \(8=M_{\rm val}\) is \(h_e+1\). Algebraically it packages
\[
(3+1)+(3+1)=4+4=8,
\]
so it is also the divisorial realization of the disjoint sum \(2+2\).

### 3. Coupled \((3,3,2,2)\) branch

**VERDICT — FACT:** The shared \(C_3\)-exceptional divisor binds with ratio \(2\); the coupled chart has \(b=(vz,v\theta z\eta)\).

**FACT.** In a \(T_{11}\)-pivot chart, blow up \(T=0\):
\[
T=v\begin{pmatrix}1&p\\q&qp+\theta\end{pmatrix}
\sim v\operatorname{diag}(1,\theta),\qquad J=v^3.
\]
After transforming \(R,C_3\), the left factor is
\[
B=\begin{pmatrix}v&0\\0&v\theta\\\delta r_1&\delta r_2\end{pmatrix}.
\]

**FACT.** Blow up \((v,\delta)\), taking \(\delta=v\alpha\), which contributes \(v\). Eliminate \(r_1\), then blow up \((\theta,\alpha)\), taking \(\alpha=\theta\beta\), which contributes \(\theta\). Row elimination gives
\[
B\sim \operatorname{diag}(v,v\theta).
\]

**FACT.** Blow up \(C_3=0\):
\[
C_3=z\begin{pmatrix}1&s\\t&ts+\eta\end{pmatrix},
\qquad J=z^3.
\]
Unimodular elimination yields
\[
BC_3\sim\operatorname{diag}(vz,\ v\theta z\eta).
\]
The total Jacobian is \(v^4\theta z^3\). Hence
\[
v:\frac{4+1}{2}=\frac52,\qquad
z:\frac{3+1}{2}=2.
\]
Thus \(z=0\), shared by both terms, binds and gives RLCT \(2\).

**INFERENCE.** This is the chart representing the stated \(t=(2,1,0)\) coupling; pivot permutations give its symmetric copies.

### 4. Literal ideal equality

**VERDICT — FACT:** After the stated final unit transformations, the ideal equality is literal; the Frobenius loss is generally only equivalent up to a positive analytic unit.

**FACT.** If
\[
UPV=\operatorname{diag}(b_i)
\]
with \(U,V\) unimodular over the chart ring, then
\[
\langle P_{ij}\rangle=\langle b_1,\ldots,b_M\rangle
\]
exactly. The inverse matrices prove both inclusions; no Gröbner computation is needed.

**FACT.** Nonorthogonal unit transformations do not generally preserve the Frobenius norm exactly. They make the pulled-back loss a positive analytic unit times the normal-crossing model.

**FACT.** The exponent can be read before full monomialization: immediately after blowing up \(\Delta=0\),
\[
I=u\langle X_j,\delta Y_j\rangle,
\]
so the residual \(D_J=(X;\delta Y)\) is not monomialized at \(S=0\). Likewise, after blowing up \(C_3=0\), the residual \(B\) remains free. The later blow-ups above are essential for literal diagonal ideal equality.