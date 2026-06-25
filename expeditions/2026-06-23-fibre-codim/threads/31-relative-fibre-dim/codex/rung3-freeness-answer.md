**(A) Verdict**

**FREE polynomial extension**, but only after choosing the Schur-chart section/retraction. It is **not** the naive statement that product-matrix entries are independent tuple coordinates.

**(B) Presentation**

Fact. Normalize the target to  
\[
E_0=\begin{pmatrix}I_r&0\\0&0\end{pmatrix}
\]
up to a fixed endpoint change. On the Schur chart, write
\[
M=\begin{pmatrix}\Delta&B_{12}\\B_{21}&B_{22}\end{pmatrix},
\qquad \det\Delta\ne0,
\qquad B_{22}=B_{21}\Delta^{-1}B_{12}.
\]

There is a regular section
\[
s(M)=(P_N(M),P_0(M))\in H
\]
with
\[
P_N=\begin{pmatrix}\Delta&0\\B_{21}&I\end{pmatrix},
\qquad
P_0^{-1}=\begin{pmatrix}I&\Delta^{-1}B_{12}\\0&I\end{pmatrix},
\]
so that
\[
P_NE_0P_0^{-1}=M.
\]

Hence
\[
\Sigma^r\cap U \cong S_U\times F,
\]
where \(S_U\) is the rank-\(r\) matrix Schur chart. Therefore
\[
\mathcal O(\Sigma^r\cap U)
\cong
\mathcal O(F)
\big[\Delta_{ij},(B_{12})_{i\beta},(B_{21})_{\alpha j}\big]_{\det\Delta}.
\]

The \(\delta=r(d_N+d_0-r)\) variables are exactly the entries of \(\Delta,B_{12},B_{21}\). The entries of \(B_{22}\) are not free; they are Schur-determined. No coupling with fibre variables remains after the retraction.

**(C) Anchor \((2,2,2), r=1\)**

Let
\[
A_1=\begin{pmatrix}a&b\\c&d\end{pmatrix},
\quad
A_2=\begin{pmatrix}e&f\\g&h\end{pmatrix}.
\]
Set
\[
u=m_{11}=ea+fc,\quad
v=m_{12}=eb+fd,\quad
w=m_{21}=ga+hc,\quad
z=m_{22}=gb+hd.
\]

On \(u\ne0\), rank \(1\) means
\[
uz-vw=0,
\]
so \(z=vw/u\). The three free base generators are
\[
u=m_{11},\qquad v=m_{12},\qquad w=m_{21},
\]
localized at \(u\).

For \(E_0=\begin{pmatrix}1&0\\0&0\end{pmatrix}\), the retracted fibre coordinates are
\[
A_1^F=
\begin{pmatrix}
a & b-av/u\\
c & d-cv/u
\end{pmatrix},
\quad
A_2^F=
\begin{pmatrix}
e/u & f/u\\
g-we/u & h-wf/u
\end{pmatrix}.
\]
They satisfy \(A_2^F A_1^F=E_0\). Conversely,
\[
A_1=A_1^F
\begin{pmatrix}1&v/u\\0&1\end{pmatrix},
\qquad
A_2=
\begin{pmatrix}u&0\\w&1\end{pmatrix}A_2^F.
\]

Thus
\[
\mathcal O(\Sigma^1\cap U)
\cong
\mathcal O(F)[u,v,w]_{u}.
\]

Dimensions:
\[
\dim \operatorname{Rep}=8,\qquad
\delta=3,\qquad
\dim F=4,\qquad
\dim \Sigma^1=7.
\]
So numerically
\[
\dim \Sigma^1=\delta+\dim F=3+4.
\]

Verdict at the anchor: **free-polynomial localized presentation**, not tensor-coupled.

**(D) H-sweep**

The raw sweep
\[
H\times F\to \Sigma^r
\]
does not itself give the coordinate-ring presentation; its fibres contain \(\operatorname{Stab}_H(E)\)-cosets.

But on the Schur chart there is a regular section of the rank-\(r\) orbit map, as above. That section gives a genuine global product structure on the chart:
\[
\Sigma^r\cap U\cong S_U\times F.
\]
So the chart is not merely a non-free fibration.

**(E) Main Possible Failure Point**

This verdict depends on using the **retracted fibre subalgebra** coming from the Schur section. If “\(\mathcal O(F)\subset \mathcal O(\Sigma^r\cap U)\)” is instead meant via some naive original tuple-coordinate inclusion, that inclusion is not canonical and the statement is ill-posed. The free presentation is real, but it is section-dependent.