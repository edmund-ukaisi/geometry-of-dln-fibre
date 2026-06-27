**Direct Answer**

Confidence: high. Derived, not conjectural.

The raw nested Schur peel does **not** produce a product of independent loss axes. In normal coordinates it produces a smooth-normal **sum** form: several residual blocks vanish, and \(F\) is the squared norm of a map linear in those residuals to first order.

But after one final radial blow-up of **all** normal residual coordinates together, it becomes the desired single-axis monomial atom:
\[
F(\Phi(u,\cdots))=u^2 U,\qquad |\det D\Phi|=|u|^{\minAdm(M)-1}\cdot(\text{spectator monomial}),
\]
with \(U\ge c_0>0\) on a positive-measure sector. Thus the Lean product-monomial atom can use one loss axis \((k,h)=(1,\minAdm-1)\).

The mistake to avoid is modeling the nested chain as
\[
F\sim \prod_i r_i^2.
\]
It is instead locally
\[
F\sim r_1^2+\cdots+r_d^2,\qquad d=\minAdm(M),
\]
then radialized by \(r_1=u,\ r_i=u w_i\).

**Example: \(M=(4,4,2,2)\)**

Here \(\minAdm=4\), path \((t_1,t_2)=(4,2)\), and the only positive normal block is the final \(2\times2\) leaf.

Let \(A\in\mathbb R^{4\times4}\), \(B\in\mathbb R^{4\times2}\) be free, and set
\[
C=u\Gamma,\qquad 
\Gamma=\begin{pmatrix}1&s\\ t&v\end{pmatrix}.
\]
Then exactly
\[
ABC=u\,AB\Gamma,\qquad
F=u^2\|AB\Gamma\|^2.
\]
The Jacobian from \((u,s,t,v)\mapsto C\) is \(|u|^3\). Thus
\[
|\det D\Phi|=|u|^3,
\]
so the atom threshold is
\[
\frac{3+1}{2}=2=\frac{\minAdm}{2}.
\]
On a sector where, for example, suitable entries of \(A\), \(B\), and \(\Gamma\) are nonzero, \(U=\|AB\Gamma\|^2\) is bounded below.

**Example: \(M=(3,3,3,3)\)**

Here \(\minAdm=6\), path \((t_1,t_2)=(2,1)\), with normal block sizes \(1,2,3\).

Use blocks
\[
K=\begin{pmatrix}a&a\alpha\\ \gamma a&\gamma a\alpha+\delta\end{pmatrix},
\quad
m=\binom{m_1}{m_2},\quad
\lambda=(\lambda_1,\lambda_2),
\]
and define
\[
A=
\binom{I_2}{\lambda}K(I_2\ m)+uE_{33}.
\]
Let
\[
w=(1,n_1,n_2),\quad p=\binom{1}{\ell},\quad
Y=\begin{pmatrix}0&0&0\\0&\eta_1&\eta_2\end{pmatrix},
\]
\[
D=p\,b\,w+uY.
\]
Choose a free row \(r\in\mathbb R^{1\times3}\), and set
\[
B=\binom{D-mr}{r},
\]
so that \((I_2\ m)B=D\). Finally choose free rows \(h_1,h_2\in\mathbb R^{1\times3}\), \(\zeta\in\mathbb R^{1\times3}\), and set
\[
C=\begin{pmatrix}
u\zeta-n_1h_1-n_2h_2\\
h_1\\
h_2
\end{pmatrix},
\]
so \(wC=u\zeta\).

Then exactly
\[
ABC=uH,
\]
where
\[
H=\binom{I_2}{\lambda}K\bigl(pb\zeta+YC\bigr)+E_{33}BC.
\]
Hence
\[
F=u^2\|H\|^2.
\]
The Jacobian is
\[
|\det D\Phi|=|u|^5\,|a|^4\,|\delta|^2\,|b|^3.
\]
The \(u\)-axis has \((k,h)=(1,5)\), so the atom threshold is
\[
\frac{5+1}{2}=3=\frac{\minAdm}{2}.
\]
On a sector with \(a,\delta,b,\zeta_1\) bounded away from zero, \(U=\|H\|^2\) is bounded below.

**General Class**

The single binding axis \((1,\minAdm-1)\) is achievable for **all positive width vectors \(M\)**, provided the axis is understood as the final radial coordinate of the full normal bundle to a minimal rank-chain stratum.

For a minimizing admissible path \(T=(t_1,\dots,t_L=0)\), the normal block sizes are
\[
d_j=(t_{j-1}-t_j)(M_j-t_j),
\]
with \(t_0=M_0\), and
\[
\sum_j d_j=\minAdm(M).
\]
Schur coordinates make the product vanish exactly when all these residual blocks vanish. Scaling all residual coordinates by one common radial variable \(u\) gives
\[
F=u^2U,\qquad |\det|=|u|^{\minAdm(M)-1}\cdot(\text{spectator monomial}).
\]

What is false is the stricter claim that each nested pivot gives a separate product loss axis. For genuine multi-pivot cases like \((3,3,3,3)\), the unradialized form is sum/smooth-normal, not product-normal-crossing. The product-monomial Lean atom becomes valid only after the common radial blow-up. Global convergence below \(\minAdm/2\) is not proved by this lower-bound sector alone; it needs the matching upper-bound cover/resolution.