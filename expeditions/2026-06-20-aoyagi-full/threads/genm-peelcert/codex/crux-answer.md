**Q1.** No global exact factorization of the stated chart integral into a 1D radial integral times the reduced-chain box integral.

The exact useful CoV is: split \(A_1=\binom{X}{Y}\) with \(X\in\mathbb R^{t\times M_2}\), \(Y\in\mathbb R^{b\times M_2}\), and set
\[
B=P X+B_{12}Y,\qquad Y=Y .
\]
For fixed \(P,B_{12}\), the Jacobian is \(|\det P|^{-M_2}\). Then
\[
B_0=B A_2\cdots A_L,\qquad Q_b=Y A_2\cdots A_L,
\]
and, after \(C'=CP^{-1}\),
\[
\mathrm{freed}= \|B A_{\ge2}\|^2+\|C'B A_{\ge2}+\Gamma Y A_{\ge2}\|^2 .
\]

On a local polar/blow-up chart in the variables \((B,Y)\), dimension \(M_1M_2=(t+b)M_2\),
\[
B=u\widehat B,\qquad Y=u\widehat Y,
\]
so
\[
dB\,dY=u^{M_1M_2-1}\,du\,d\mu,\qquad \mathrm{freed}=u^2(\cdots).
\]
Thus the radial exponent is
\[
\alpha=M_1M_2-1-2c'.
\]

If one also integrates \(\Gamma\) over all \(\mathbb R^{ab}\) and stays on the full-row-rank locus of \(Q_b\), the powers still combine to this same \(\alpha\):
\[
\det(Q_bQ_b^T)^{-a/2}\|B_0\|^{ab-2c'}
\sim u^{-ab}u^{ab-2c'}=u^{-2c'}.
\]

The obstruction to exact product factorization is the remaining angular factor
\[
\det(\widehat Q_b\widehat Q_b^T)^{-a/2},
\]
plus non-product box/cutoff domains. On a chart where a fixed \(b\times b\) minor of \(\widehat Q_b\) is bounded below, this determinant is a smooth positive unit, so the singular part is the reduced-chain zeta integral with
\[
c''=c'-ab/2.
\]
That is an exact local normal form up to smooth positive weights, not an exact equality of box integrals.

**Q2.** No, not in general. On the full-rank minor chart the Gram factor is a unit and harmless. Near rank loss it leaves a real residual singularity.

Concretely, near a rank \(b-1\) point, analytic row/column coordinates put the normal variables in \(z\in\mathbb R^{q-b+1}\) with
\[
\det(Q_bQ_b^T)\sim |z|^2.
\]
Hence
\[
\det(Q_bQ_b^T)^{-a/2}dQ_b \sim |z|^{-a}\,dz
= r^{q-b-a}\,dr\,d\theta .
\]
This is a nonnegative monomial only if \(a\le q-b\); it is merely integrable if \(a<q-b+1\). Otherwise it diverges. Thus the all-\(\mathbb R^{ab}\) \(\Gamma\)-integration is unsafe near degenerate \(Q_b\); one must either restrict to full-rank charts or keep bounded \(\Gamma\) coupled with \(Q_b\).

**Q3.** For the actual tail-variable radial blow-up above, convergence of the radial factor requires
\[
M_1M_2-1-2c'>-1
\quad\Longleftrightarrow\quad
c'<M_1M_2/2.
\]
Since \(\mathrm{minAdm}(M)\le M_1M_2\), this radial factor cannot bind before \(\mathrm{minAdm}(M)/2\). It may bind simultaneously when equality holds, but otherwise the reduced-chain or Gram-degeneracy analysis is the binding issue.