**Verdict:** yes. Under exactly the setup you gave, the equality is unconditional:

\[
\dim_k \mathfrak m_{a,\mathrm{loc}}/\mathfrak m_{a,\mathrm{loc}}^2
=
\dim_k \ker\left(J:k^n\to k^m\right).
\]

No smoothness, radicality, reducedness, algebraic closedness, perfectness, minimality, Grobner basis, or regular-sequence hypothesis is needed.

Here is the first-principles calculation.

Let

\[
\mathfrak p_a=(x_1-a_1,\dots,x_n-a_n)\subset R.
\]

Since \(g_i(a)=0\), we have \(I\subset \mathfrak p_a\), and

\[
\mathfrak m_a=\mathfrak p_a/I\subset A.
\]

Then

\[
\mathfrak m_a/\mathfrak m_a^2
\cong
\mathfrak p_a/(\mathfrak p_a^2+I).
\]

Also \(\mathfrak p_a/\mathfrak p_a^2\) has \(k\)-basis given by the classes of \(x_j-a_j\). For \(f\in \mathfrak p_a\),

\[
f \equiv \sum_j \frac{\partial f}{\partial x_j}(a)(x_j-a_j)
\pmod{\mathfrak p_a^2}.
\]

This is just the degree-one part after translating \(x_j=a_j+y_j\), so it works in arbitrary characteristic.

The image of \(I\) in \(\mathfrak p_a/\mathfrak p_a^2\) is the \(k\)-span of the linear parts of the generators \(g_i\). Indeed, if \(f=\sum_i h_i g_i\), then modulo \(\mathfrak p_a^2\),

\[
h_i g_i \equiv h_i(a) g_i,
\]

because \(h_i-h_i(a)\in \mathfrak p_a\) and \(g_i\in \mathfrak p_a\). Hence the image is spanned by the row vectors

\[
\left(\frac{\partial g_i}{\partial x_1}(a),\dots,\frac{\partial g_i}{\partial x_n}(a)\right).
\]

Therefore

\[
\mathfrak m_a/\mathfrak m_a^2
\cong
k^n/\operatorname{rowspan}(J)
\cong
\operatorname{coker}(J^T:k^m\to k^n).
\]

So

\[
\dim_k \mathfrak m_a/\mathfrak m_a^2
=
n-\operatorname{rank}J
=
\dim_k\ker(J:k^n\to k^m).
\]

This is the theorem.

On the hypotheses:

- **Smoothness/regularity:** not needed. At a singular point the equality still holds; the tangent dimension is just larger than the local Krull dimension.
- **Radical/reduced:** not needed. Example: \(A=k[x]/(x^2)\) at \(0\) has \(\dim \mathfrak m/\mathfrak m^2=1\), and the Jacobian is zero, so \(\dim\ker J=1\).
- **Algebraically closed/perfect:** not needed. The point is \(k\)-rational, so the residue field is exactly \(k\).
- **Minimal/Grobner/regular-sequence generators:** not needed. Any finite generating family gives the same row span in \(\mathfrak p_a/\mathfrak p_a^2\). Extra or redundant generators only add rows lying in the same span.
- **More/fewer equations than variables:** no issue. Rank-nullity gives \(\dim\ker J=n-\operatorname{rank}J\) for any \(m\times n\) matrix.

For the local/global issue, let \(S=A\setminus \mathfrak m_a\). Then

\[
S^{-1}(\mathfrak m_a/\mathfrak m_a^2)
\cong
\mathfrak m_a A_{\mathfrak m_a}/(\mathfrak m_a A_{\mathfrak m_a})^2.
\]

Moreover \(S^{-1}(\mathfrak m_a/\mathfrak m_a^2)\cong \mathfrak m_a/\mathfrak m_a^2\), because \(\mathfrak m_a/\mathfrak m_a^2\) is an \(A/\mathfrak m_a=k\)-vector space and every \(s\notin\mathfrak m_a\) acts by the nonzero scalar \(s(a)\in k^\times\). Thus the global and local cotangent spaces have the same \(k\)-dimension.

Finally, yes: the conormal-sequence derivation is standard. Tensoring

\[
I/I^2\to \Omega_{R/k}\otimes_R A\to \Omega_{A/k}\to 0
\]

with \(k=A/\mathfrak m_a\) gives

\[
k^m \xrightarrow{J^T} k^n \to k\otimes_A\Omega_{A/k}\to 0,
\]

up to the evident quotient if the generators are redundant. Since \(a\) is \(k\)-rational, the augmentation \(A\to k\) is a \(k\)-algebra retraction of \(k\to A\), and one has canonically

\[
\mathfrak m_a/\mathfrak m_a^2 \cong k\otimes_A\Omega_{A/k}.
\]

That identification uses rationality/augmentation, not smoothness. Without a rational residue field, \(\kappa(a)\otimes_A\Omega_{A/k}\) can contain extra residue-field differential directions \(\Omega_{\kappa(a)/k}\), so the statement must be adjusted.