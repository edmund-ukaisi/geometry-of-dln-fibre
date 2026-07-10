**Q1.** For `M=(2,3,2,2)`,
\[
\minAdm(1,2,2)=2,\qquad \minAdm(2,2,2)=3,
\]
so
\[
\minAdm(2,3,2,2)=\min(6,4,3)=3,\qquad \tfrac12\minAdm(M)=\tfrac32.
\]

Write the shared tail as \(A\), top row \(x=(x_1,x_2)\), and corank block \(Y\). Up to bounded analytic units and triangular changes absorbing \(C'\),
\[
f=\mathrm{freed}\sim \|xA\|^2+\|(\gamma Y)A\|^2.
\]

The only binding chart is the rank-one chart of \(A\). Put
\[
A\sim \begin{pmatrix}1&0\\0&z\end{pmatrix},\qquad
Y=(y\;u),\quad y,u\in\mathbb R^2.
\]
Then
\[
f\sim x_1^2+(\gamma\cdot y)^2
+z^2\bigl(x_2^2+(\gamma\cdot u)^2\bigr).
\]
On \(\gamma\neq0\), set \(p=\gamma\cdot y,\ v=\gamma\cdot u\):
\[
f\sim x_1^2+p^2+z^2(x_2^2+v^2).
\]

Blow up the codimension-three center \((x_1,p,z)=0\). In the \(z\)-chart,
\[
x_1=zX,\quad p=zP,\quad
f=z^2(X^2+P^2+x_2^2+v^2),
\]
with Jacobian order \(k=2\) and loss order \(N=2\), giving
\[
\frac{k+1}{N}=\frac32.
\]
Blowing up the residual quadratic center \((X,P,x_2,v)=0\) gives \(k=3,N=2\), hence candidate \(2\). The \(x_1\)- and \(p\)-charts of the first blow-up also have \(k=2,N=2\).

Rank-two \(A\)-charts give quadratic control of \(x\) and \(\gamma Y\), hence candidate \(\ge2\). Rank-zero \(A\)-charts first have \(A=\rho\widehat A\), Jacobian order \(3\), loss order \(2\), candidate \(2\), and their exceptional rank-one subcharts reduce to the calculation above. The \(\gamma=0\) subcharts are no worse: resolving the scalar product \(\gamma\cdot y\) contributes the usual \(1/2\), combined with the two quadratic coordinates gives \(1+1/2=3/2\).

Thus the deepest corner has local RLCT
\[
\lambda_{\mathrm{corner}}=\frac32.
\]
This equals \(\frac12\operatorname{codim}\{YA=0\}=\frac12\cdot3\), and equals, not falls below, \(\frac12\minAdm(M)=\frac32\).

**Q2.** Literal blow-up along the raw loci \(\{\operatorname{rank}(YA)\le r\}\) is not a smooth-center resolution. Already for \(2\times2\), \(\{YA=0\}\) has the singular incidence pieces \(A=0\), \(Y=0\), and \(\operatorname{rank}A=\operatorname{rank}Y=1,\ \mathrm{im}(A)\subset\ker(Y)\).

So product rank alone is not enough local coordinate data. It is, however, a well-founded induction index after replacing the raw rank strata by their resolved incidence/rank-flag transforms: each chart splits off the nonzero product-rank block and leaves a smaller corank tail. The index strictly decreases in the unresolved tail.

**Q3.** For this \(2\times2\) deepest corner, the elementary rank-one/rank-zero blow-ups above suffice. In higher width or longer products, one must import Aoyagi’s product-rank-flag machinery: resolved incidence centers, chartwise block splitting, Jacobian bookkeeping, and the induction proving that the remaining tail has strictly smaller product rank.