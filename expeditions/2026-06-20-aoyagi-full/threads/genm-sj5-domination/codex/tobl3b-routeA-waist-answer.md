CLOSES-WITH-CAVEAT: the binding shell closes by one rectangular-SVD corner; only nonbinding shells require lowering oversized Jacobian powers before applying qPeel.

B. For \((3,2,3)\), \(k_\star=1\). On a chart with an invertible \(1\times1\) block,
\[
A_1=\begin{pmatrix}P&Q\\R&S\end{pmatrix}
=L\begin{pmatrix}P&0\\0&W\end{pmatrix}R_0,
\qquad W=S-RP^{-1}Q\in\mathbb R^{1\times2}.
\]
Writing \(A_0L=[C\ D]\), with \(C,D\in\mathbb R^3\),
\[
\|A_0A_1\|_F^2\asymp \|C\|^2+\|DW\|_F^2
=\|C\|^2+\|D\|^2\|W\|^2.
\]
The coordinate Jacobians are bounded above and below.

Put \(u=\|W\|\). Since \(W\in\mathbb R^2\), \(dW=u\,du\,d\omega\), so \(h_1=1\). The deep block is \(X_1=D\in\mathbb R^3\), hence \(m_1=2\), and
\[
h_1=1\le2=m_1.
\]
The clean block \(C\in\mathbb R^3\) contributes an ordinary Morse charge \(3\); in radial notation \(h_0=m_0=2\). Thus
\[
(h_0+1)+(h_1+1)=3+2=5.
\]
Weighted splitting between \(\|C\|^2\) and \(u^2\|D\|^2\), followed by qPeel, gives finiteness for \(c<5/2\), including at \(D=0\).

The unsplit global SVD has raw powers \((3,1)\), whose first gate \(3\le2\) fails by \(1\). That is not the binding-shell ledger: replacing \(u_1^3\le u_1^2\) gives effective powers \((2,1)\), gates \(2\le2\), \(1\le2\), and charge \(3+2=5\).

C. For \((2,1,2)\), both \(k=0,1\) bind.

- At \(k=1\), \(A_1\) has full row rank and the loss is comparable to \(\|C\|^2\), \(C\in\mathbb R^2\). Hence \(h_0=m_0=1\), charge \(2\), threshold \(1\).
- At \(k=0\), \(\|A_0A_1\|^2=\|A_0\|^2\|A_1\|^2\). Radializing \(A_1\in\mathbb R^2\) gives \(h_1=1\), while \(X_1=A_0\in\mathbb R^2\) gives \(m_1=1\). The gate is \(1\le1\), and the charge is \(2\).

For \((3,1,3)\), \(k=0,1\) again tie. At \(k=0\), \(h_1=2\), \(X_1\in\mathbb R^3\), \(m_1=2\): equality in the gate and charge \(3\). At \(k=1\), there is only a clean \(3\)-dimensional Morse block.

Correction: \(\minAdm(4,2,4)=7\), not \(8\):
\[
8,\quad 3+4=7,\quad 8.
\]
Its binding shell is \(k=1\): clean charge \(4\), plus \(W\in\mathbb R^3\) with \(h=2\) and \(D\in\mathbb R^4\), \(m=3\). Thus \(2\le3\) and \(4+3=7\), giving threshold \(7/2\).

D. Put
\[
f(k)=(s-k)(z-k)+xk,\qquad r=s-k,\quad q=z-k.
\]
On the rank-\(k\) shell the top \(k\) singular directions give a clean \(xk\)-dimensional Morse block. SVD of \(W\in\mathbb R^{r\times q}\) gives radial variables \(u_1\ge\cdots\ge u_r\) and blocks \(X_i\in\mathbb R^x\), so \(m_i=x-1\), with
\[
\|DW\|^2=\sum_{i=1}^r u_i^2\|X_i\|^2,
\qquad
h_i=q-r+2(r-i).
\]
At a binding \(k\),
\[
h_1\le x-1
\iff q+r-2\le x-1
\iff x\ge q+r-1.
\]
This is exactly \(f(k+1)-f(k)\ge0\). Hence every binding-shell gate holds, and
\[
xk+\sum_{i=1}^r(h_i+1)=xk+rq=f(k)=\minAdm(x,s,z).
\]

For arbitrary shells use
\[
\widetilde h_i=\min(h_i,x-1).
\]
Since \(u_i^{h_i}\le u_i^{\widetilde h_i}\) on \([0,1]\), this is a valid majorant, and all effective gates hold. Moreover
\[
xk+\sum_{i=1}^r(\widetilde h_i+1)
=\min_{j\ge k}f(j)\ge\min_jf(j)=\minAdm(x,s,z).
\]
Thus the finite singular-value shell cover closes every waist. Raw gates can fail on nonbinding shells precisely when \(x<q+r-1\); the effective gates never fail.

E. The exact-rank-\(k\) stratum is smooth. On the pivot chart,
\[
\operatorname{rank}(A_1)=k+\operatorname{rank}(W),
\]
so the normal slice to \(\{\operatorname{rank}A_1\le k\}\) at rank \(k\) is simply \(W=0\), of dimension \(rq\).

Its codimension is delivered by one multi-radial SVD corner:
\[
dW\lesssim
\prod_{i=1}^r u_i^{\,q-r+2(r-i)}\,du\,d\Omega,
\qquad
\sum_{i=1}^r(h_i+1)=rq.
\]
No recursive determinantal peel is analytically necessary. If polynomial blow-up charts are required instead of SVD integration, this becomes a rank-flag recursion of depth at most \(r\); it terminates, and the same truncated-gate identity prevents a new waist wall.

F. The genuinely new lemma is the uniform rectangular-SVD shell domination:
\[
\|DW\|^2=\sum_i u_i^2\|X_i\|^2,
\]
together with the Weyl-Jacobian majorant, rotated-box control for \(X=DU\), exponent truncation \(h_i\mapsto\min(h_i,x-1)\), and the identity
\[
\sum_i\min\!\bigl(x,q+r-2i+1\bigr)
=\min_l\bigl((r-l)(q-l)+xl\bigr).
\]
That is the bridge from determinantal shells to the banked qPeel lemma.