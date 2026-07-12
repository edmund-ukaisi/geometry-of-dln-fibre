**Q1.** Yes. Finite integrals on every fixed sector do not imply finiteness on their union:

\[
\int_{\cup_n E_{1/n}}f=\lim_n\int_{E_{1/n}}f
\]

may equal \(\infty\), while the bounds grow like \(\varepsilon^{-ab/2}\). The rank-drop locus being null does not control its shrinking neighbourhoods. One must either integrate the displayed majorant off-sector or abandon that majorant for a joint estimate retaining the residual.

**Q2.** The off-sector is a quantitative, joint power-counting problem. A global estimate \(\sigma^2\asymp\operatorname{dist}^2\) is sufficient but not necessary; stratified coordinates, tubular-volume bounds, or a nested resolution also suffice. The IH alone does not: integrability of \(g\) does not imply integrability of an unbounded correlated weight \(hg\). A different peel can invoke the IH only after a new CoV converts the Gram weight into admissible resolved data—precisely additional machinery.

**Q3.** Here \(\operatorname{carrierThreshold}(3,3,2,2)=2\), and the reduced exponent is

\[
q=c'-\tfrac12<\tfrac32.
\]

Take

\[
B=\begin{pmatrix}1&0\\0&0\\0&1\end{pmatrix},
\qquad C_t=\operatorname{diag}(1,t).
\]

Then \(Z(t)=BC_t\) drops from rank \(2\) to rank \(1\) at \(t=0\), \(Q_b(t)=(0,t)\), and the reduced loss is \(1\). Hence the restricted integrand is

\[
(t^2)^{-1/2}\cdot1^{-q}=|t|^{-1},
\qquad
\int_0^\delta t^{-1}\,dt=\infty.
\]

Thus the sector estimate alone has no convergent limit. This curve is measure-zero, so it does not prove ambient divergence.

Indeed, the correct generic rank-one tube calculation, writing \(B=(X;y)\), gives

\[
\int dy\,\|yC_t\|^{-1}\asymp\log(1/t),\qquad
\int dX\,\|XC_t\|^{-2q}\asymp t^{2-2q}.
\]

Consequently the normal integral is

\[
\int_0^\delta t^{2-2q}\log(1/t)\,dt
=\int_0^\delta t^{3-2c'}\log(1/t)\,dt,
\]

which converges exactly for \(c'<2\) and diverges at \(c'=2\). This establishes generic-tube finiteness only by supplying the missing quantitative CoV/rate; deeper intersections still require charts.

F1–F6 are essentially correct. One nuance: \(\{\operatorname{rank}Q_b<b\}\) is not generally identical to the rank-drop locus of the whole tail product.

**Q4.** **NET: off-sector needs a rate / a further CoV.**