\[
\boxed{\lambda_{\mathrm{full}}=\frac72=3.5.}
\]

Choose an invertible column change \(R\) such that
\[
Q_pR=[I_2\;0],\qquad Q_bR=(u_1,u_2,s).
\]
Fixed invertible changes preserve integrability thresholds. For each row \(t=(a,b,d)\) of \(T\),
\[
t\begin{pmatrix}1&0&0\\0&1&0\\u_1&u_2&s\end{pmatrix}
=(a+du_1,\ b+du_2,\ ds).
\]
After the unit-Jacobian shear \(x=(a+du_1,b+du_2)\), \(y=d\), the three rows give
\[
L\asymp |x|^2+s^2|y|^2,
\qquad x\in\mathbb R^6,\quad y\in\mathbb R^3.
\]

Moreover, the two large singular values stay uniformly bounded below, while the determinant is proportional to \(s\). Hence
\[
\sigma_{\min}(hsQ)\asymp |s|,
\qquad g=\sigma_{\min}(hsQ)^2\asymp s^2.
\]

The inner integral satisfies
\[
J(A)\asymp
\begin{cases}
1, & c<3,\\[2mm]
\log(1/g), & c=3,\\[2mm]
g^{-(c-3)}, & 3<c<\frac92,\\[2mm]
\infty, & c\ge \frac92.
\end{cases}
\]
Thus
\[
\boxed{\beta(c)=\max(c-3,0)}
\]
with a logarithmic correction at \(c=3\).

For \(3<c<9/2\), the outer transverse integral is
\[
\int J(A)\,dA\asymp
\int |s|^{-2(c-3)}\,ds,
\]
which converges exactly when \(c<7/2\). It diverges logarithmically at \(c=7/2\). Therefore \(I(c)<\infty\) precisely for \(c<3.5\). For comparison, the shell threshold is \(9/2\).

**VERDICT: Claim F is correct for this anchor.** The rank-drop locus is present, but it lowers the shell threshold \(4.5\) only to \(3.5\), exactly matching the comparator. Claim S’s likely error is omitting the two strong directions contributed by the \(C,D\) row (or bounding before integrating them); all three rows jointly provide the six-dimensional strong block.