Q1 — PASS.

The loss is literally additive in [RouteMSJCorankQ.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCorankQ.lean:52):

\[
L(u)=\sum_i U_i u_i^2.
\]

For fixed \(U_i>0\), \(L(u)\asymp \sum_i u_i^2\). Polar scaling gives

\[
\int_0^\varepsilon r^{\sum_i h_i+q-1-2c'}\,dr
=\int_0^\varepsilon r^{\sum_i(h_i+1)-1-2c'}\,dr,
\]

so the exact slice threshold is

\[
c'<\frac12\sum_i(h_i+1).
\]

It is not the minimum. A minimum arises from a multiplicatively separated/shared-divisor model, not this sum.

Q2 — PASS. `h_i ≤ m_i` is exactly the right gate.

Put

\[
a_i=h_i+1,\qquad d_i=m_i+1,\qquad S=\sum_j a_j,\qquad w_i=\frac{a_i}{S}.
\]

For \(q\ge1\), \(w_i>0\), \(\sum_iw_i=1\), and \(w_i\le1\). From \(c'<S/2\),

\[
2w_ic'=\frac{2a_ic'}S<a_i=h_i+1.
\]

Hence:

\[
h_i-2w_ic'>-1,
\]

so every \(u_i\)-monomial integral is finite. If \(h_i\le m_i\), then \(a_i\le d_i\), giving

\[
2w_ic'<a_i\le d_i=m_i+1,
\]

which is precisely the radial-Morse condition for

\[
\int_{[-T,T]^{d_i}}\|X_i\|^{-2w_ic'}\,dX_i<\infty.
\]

The gate need not be strict. When \(h_i=m_i\), the required exponent inequality remains strict because \(c'<S/2\).

It is also a genuine, non-vacuous gate. If \(a_i>d_i\), the separated deep factor diverges once

\[
c'\ge \frac{Sd_i}{2a_i}<\frac S2.
\]

More decisively, the original joint model itself then collapses. Radially, one block has measure

\[
u_i^{a_i-1}r_i^{d_i-1}\,du_i\,dr_i,\qquad t_i=u_ir_i.
\]

The induced small-\(t_i\) charge is \(\min(a_i,d_i)\), with an additional logarithm when \(a_i=d_i\). Thus the exact joint threshold is

\[
\frac12\sum_i\min(a_i,d_i).
\]

It equals \(S/2\) exactly when every \(a_i\le d_i\), equivalently every \(h_i\le m_i\). Any violation produces genuine divergence strictly below \(S/2\).

Minor scope caveat: for \(q=0\), the hypotheses \(0\le c'<0\) are inconsistent, so that specialization is vacuous. Intended \(q\ge1\) instances are non-vacuous.

Q3 — PASS.

The exceptional set needed to apply AM–GM is

\[
E=\bigcup_i\{X_i=0\}.
\]

Each \(X_i\) has dimension \(m_i+1\ge1\), so each component of \(E\) is null under the product Lebesgue measure. Applying the positive-unit lemma outside \(E\) is therefore sound.

Crucially, [qPeelIntegral](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCorankQ.lean:171) still integrates over the full Morse boxes. It deletes only exact zero points for the a.e. inequality, not their neighborhoods. If

\[
2w_ic'\ge m_i+1,
\]

the divergence comes from every punctured neighborhood \(0<\|X_i\|<\varepsilon\), not from the singleton \(X_i=0\). A null-set modification cannot conceal that divergence.

Q4 — PASS as an abstract clean-coordinate finiteness theorem, with two obligations.

There is no internal weight drop or measure mismatch:

- Lean’s `volume` on the dependent finite product is the product of the component volumes.
- Each component is ordinary Lebesgue measure on \(\mathbb R^{m_i+1}\).
- The threshold is \(S/2\), under the exact per-block gate above.

Lean does define \(0^\alpha=0\) for every nonzero real exponent, including negative exponents. Thus the integrand is pointwise understated on the exact zero-loss locus. Here that locus is joint-null, so it does not change the integral or its threshold; the punctured neighborhoods remain fully integrated. It would become a real defect if an upstream degeneration made the zero-loss locus positive-measure.

The load-bearing upstream obligation is to prove that the actual DLN chart really supplies these free, independent blocks:

- the loss is comparable in the correct direction to \(\sum_i u_i^2\|X_i\|^2\);
- the combined deep-data map has the asserted full product rank;
- its change of coordinates preserves or has bounded Jacobian relative to Lebesgue measure;
- the codimension is available per matched block, \(m_i+1\ge h_i+1\), not merely as an unallocated total \(D_q\).

Without that instantiation, one could artificially choose large `m_i` and apply a sound abstract theorem to the wrong geometry. Finally, this theorem proves only finiteness below the candidate threshold; claiming an exact RLCT also requires the corresponding divergence/lower-bound theorem.