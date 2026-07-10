**1. Schur Shear**

After permuting pivot rows/columns to the front,

\[
P=\begin{pmatrix}B&E\\ C&D\end{pmatrix},\qquad B\in\mathbb R^{q\times q},\quad \det B\ne 0,
\]

and

\[
Z=D-CB^{-1}E.
\]

Factor

\[
P=
\begin{pmatrix}I&0\\ CB^{-1}&I\end{pmatrix}
\begin{pmatrix}B&E\\ 0&Z\end{pmatrix}.
\]

For

\[
A_0=[X\mid W],
\]

set

\[
\widetilde X=X+WCB^{-1}.
\]

This is a shear in the \(A_0\)-variables with Jacobian \(1\). Relabelling \(\widetilde X\) as \(X\),

\[
A_0P=[X\mid W]\begin{pmatrix}B&E\\0&Z\end{pmatrix}
      =[XB,\; XE+WZ].
\]

Therefore

\[
\|A_0P\|_F^2
=
\|XB\|_F^2+\|XE+WZ\|_F^2.
\]

Equivalently, with \(R=[B\ E]\),

\[
\|A_0P\|_F^2
=
\|XR+[0\;\;WZ]\|_F^2.
\]

So: \(W\) appears only through \(WZ\), but before completing the square there is a cross-term

\[
2\langle XE,WZ\rangle.
\]

There is no surviving \(WC\)-type term; the Schur shear has removed it.

**2. Morse Peel In \(X\)**

Let

\[
S=RR^\top=BB^\top+EE^\top.
\]

Since \(B\) is invertible, \(S\) is positive definite. For row-wise vectorisation of \(X\),

\[
\Phi=I_{m_0}\otimes S,
\qquad
d=m_0q,
\]

so

\[
\det\Phi=(\det S)^{m_0}.
\]

The exact determinant factor from the whole-space \(X\)-integral is

\[
(\det\Phi)^{-1/2}
=
(\det S)^{-m_0/2}
=
\det([B\ E][B\ E]^\top)^{-m_0/2}.
\]

In pivot determinant form,

\[
(\det S)^{-m_0/2}
=
|\det B|^{-m_0}
\det\!\left(I+B^{-1}EE^\top B^{-\top}\right)^{-m_0/2}.
\]

Now put \(U=WZ\). Completing the square gives

\[
\|XB\|_F^2+\|XE+U\|_F^2
=
\|(X+UE^\top S^{-1})S^{1/2}\|_F^2
+
\operatorname{tr}(UHU^\top),
\]

where

\[
H=I-E^\top S^{-1}E.
\]

Thus the residual core is

\[
w=\operatorname{tr}\bigl((WZ)H(WZ)^\top\bigr)
  =
\|(WZ)H^{1/2}\|_F^2.
\]

It is **not exactly** \(\|WZ\|_F^2\) unless \(E=0\). It is a positive definite output-metric version of \(\|WZ\|^2\). For fixed \(B,E\), it is comparable to \(\|WZ\|^2\), but the comparability constant need not be uniform as \(B\) approaches singularity.

**3. Factor Count**

Ignoring the harmless positive definite output metric, the residual core has the form

\[
WZ=W\,Y_1\cdots Y_{L-1},
\]

where the reduced tail has widths

\[
\operatorname{redTail}=(m_1-q,\ldots,m_L-q).
\]

But the residual chain is not just `redTail`. It is

\[
N=(m_0,\;m_1-q,\;\ldots,\;m_L-q).
\]

Its factors are

\[
W,\;Y_1,\ldots,Y_{L-1},
\]

so it has

\[
1+(L-1)=L
\]

factors.

The original chain

\[
M=(m_0,\ldots,m_L)
\]

also has \(L\) factors. Therefore the residual is a **same-arity** sub-problem, not the fewer-factor `redTail` problem.

So the arity-only IH on `redTail` does **not** cover this residual front integral. The \(A_0\)-peel reduces to a same-arity chain \((m_0,\operatorname{redTail})\), not to the smaller-arity `redTail` alone.

**4. Well-Founded Measure**

A width measure fixes the structural recursion. Let

\[
\Sigma(M)=\sum_{i=0}^L m_i.
\]

For the same-arity residual chain

\[
N=(m_0,m_1-q,\ldots,m_L-q),
\]

we have

\[
\Sigma(N)
=
m_0+\sum_{i=1}^L(m_i-q)
=
\Sigma(M)-Lq.
\]

Since \(q\ge 1\), this is strictly smaller:

\[
\Sigma(N)<\Sigma(M).
\]

Equivalently, the tail-width sum

\[
\tau(M)=\sum_{i=1}^L m_i
\]

satisfies

\[
\tau(N)=\tau(M)-Lq<\tau(M).
\]

Thus: arity induction alone does not close; induction on total width, or lexicographic induction on

\[
(\text{number of factors},\Sigma)
\]

does close structurally. The exponent-budget inequality needed to apply the same theorem to \(N\) is a separate admissibility lemma; the block algebra itself gives the strict width decrease above.