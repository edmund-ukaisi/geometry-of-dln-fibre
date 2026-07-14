Verdict: the full-block strategy is sound, but lemma (2) is numerically false as stated for the entire LHS. It omits the finite volumes of the outer \(z\)- and \(A_{\rm cor}\)-domains. After inserting those factors, the assembled finiteness implication is sound.

### Q1

**FACT.** Let \(r=u+b\), \(s=u+a\). Then \(Q\in\mathbb R^{r\times n}\), \(B\in\mathbb R^{s\times r}\), and for each row \(w\) of \(B\),
\[
\|wQ\|^2=w(QQ^{\mathsf T})w^{\mathsf T}\ge \varepsilon^2\|w\|^2.
\]
Summing over the \(s\) rows gives
\[
\|BQ\|_F^2\ge \varepsilon^2\|B\|_F^2.
\]

**INFERENCE.** Lemma (1) is correct. There is no dimension or transpose error; \(QQ^{\mathsf T}\), not \(Q^{\mathsf T}Q\), is the relevant Gram matrix for right multiplication of row vectors.

### Q2

Let \(T=m_0+ab\).

**FACT.** Lemma (4) gives
\[
\mathrm{RHS}(c')<\infty\Longrightarrow 2c'<T.
\]
Lemma (5) gives \(T\le N\). Hence
\[
\{c':\mathrm{RHS}(c')<\infty\}
 \subseteq \{2c'<T\}
 \subseteq \{2c'<N\}.
\]

**INFERENCE.** The direction is correct: the demonstrated LHS-finite region \(c'<N/2\) is indeed a superset of the possible RHS-finite region.

However, the global form of lemma (2) is false. The correct estimate is
\[
\mathrm{LHS}(c')
\le
\varepsilon^{-2c'}I_N(c')
\int_{Z_{\rm box}}
 \mu(A_{\rm cor,box}\cap\operatorname{shell}(z))\,dz,
\]
and therefore
\[
\mathrm{LHS}(c')
\le
\varepsilon^{-2c'}I_N(c')\,
\mu(Z_{\rm box})\,\mu(A_{\rm cor,box}).
\]
Those factors are finite, so they do not affect finiteness.

Concrete counterexample to the stated numeric bound: take \(u=n=1\), \(a=b=0\), \(Q=1\), \(\varepsilon=1\), \(c'=1/4\), and let \(z\in[-1,1]\) be a dummy outer variable. Then
\[
I_N=\int_{-1}^1 |p|^{-1/2}\,dp=4,
\qquad
\mathrm{LHS}=2I_N=8,
\]
whereas lemma (2) claims \(8\le4\).

Thus the proof as literally written uses a false inequality, but the theorem is repaired immediately by retaining the finite outer-volume factor.

### Q3

**INFERENCE.** The full-block route genuinely evades the corank-dropping trap.

The variables \(C,D\) are actual integration variables, not artificially appended dimensions. On the shell,
\[
\|BQ\|_F^{-2c'}\le \varepsilon^{-2c'}\|B\|_F^{-2c'}.
\]
Enlarging the invertible-\(P\) domain to the full block box is also an upper estimate because the integrand is nonnegative. The resulting singularity is an \(N\)-dimensional full-block singularity, with threshold \(N/2\).

There is no pointwise inequality reversal or under-estimate. The only defect in (2) is the omitted outer-volume multiplier.

### Q4

- \(c'=0\): the integrand is \(1\), using the standard \(x^0=1\) convention. The LHS is finite because all domains have finite volume.
- \(c'=N/2\): the pure-box integral diverges. But \(T\le N\) implies lemma (4) forces \(\mathrm{RHS}=\infty\), so the theorem’s premise is impossible.
- More generally, the implication is logically vacuous for \(2c'\ge T\).
- \(a=0\) or \(b=0\): harmless. Zero-dimensional matrix boxes have volume \(1\), and \(ab=0\). Lemma (4) reduces to the \(v\)-threshold \(2c'\ge m_0\).
- Since \(u\ge1\), \(N=(u+a)(u+b)>0\).
- \(\varepsilon>0\) is load-bearing. If \(\varepsilon=0\), coercivity disappears and the route can fail completely—for example \(Q=0\) makes \(\|BQ\|^{-2c'}\) singular everywhere for \(c'>0\).
- An empty shell makes the LHS zero and causes no problem.

Lemma (4) also uses that the outer \(z\)-box has positive measure; ordinary boxes, including zero-dimensional ones, satisfy this.

### Q5

**FACT.** From
\[
QQ^{\mathsf T}\succeq\varepsilon^2I,\qquad \varepsilon>0,
\]
\(QQ^{\mathsf T}\) is positive definite. Consequently
\[
\operatorname{rank}Q=u+b,
\qquad n\ge u+b.
\]

**INFERENCE.** No separate full-row-rank or dimension hypothesis is needed. If \(n<u+b\), the shell is necessarily empty.
