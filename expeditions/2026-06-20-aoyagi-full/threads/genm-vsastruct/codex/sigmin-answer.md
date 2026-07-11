## Q1 — sharp inner exponent

**FACT.** Write \(c=c'\) and
\[
I_c(\sigma)=\int_{[-1,1]\times[-1,1]^6}
\bigl(|y|^2+\sigma^2z^2\bigr)^{-c}\,dy\,dz.
\]

For \(3<c<7/2\), scale \(y=\sigma u\):
\[
\sigma^{2c-6}I_c(\sigma)
\longrightarrow
\int_{-1}^1\int_{\mathbb R^6}
(|u|^2+z^2)^{-c}\,du\,dz.
\]
The stable-block integral is
\[
\int_{\mathbb R^6}(|u|^2+z^2)^{-c}\,du
=
\pi^3\frac{\Gamma(c-3)}{\Gamma(c)}|z|^{6-2c},
\]
using
\[
\frac{|S^5|}{2}B(3,c-3)
=\pi^3\frac{\Gamma(c-3)}{\Gamma(c)}.
\]
Hence
\[
I_c(\sigma)\sim
\frac{2\pi^3\Gamma(c-3)}
     {(7-2c)\Gamma(c)}
\,\sigma^{6-2c}.
\]

Thus, in the target range \(3<c<7/2\),
\[
\boxed{\beta=2c-6},
\]
not \(2c\).

The full piecewise behavior is
\[
I_c(\sigma)\sim
\begin{cases}
2\displaystyle\int_{[-1,1]^6}|y|^{-2c}\,dy,
   &c<3,\\[1ex]
2\pi^3\log(1/\sigma)+O(1),
   &c=3,\\[1ex]
C_c\,\sigma^{-(2c-6)},
   &3<c<7/2.
\end{cases}
\]
At \(c=7/2\), the fixed-\(\sigma\) seven-dimensional integral already diverges.

## Q2 — outer thresholds

**FACT.**

- Crude:
  \[
  \alpha=2c,\qquad \alpha<1
  \iff \boxed{c<\tfrac12}.
  \]

- Sharp, for \(c>3\):
  \[
  \alpha=2c-6,\qquad \alpha<1
  \iff \boxed{c<\tfrac72}.
  \]

For \(c<3\), the true inner value is uniformly bounded; at \(c=3\), it grows only logarithmically and remains tube-integrable.

Therefore the sharp estimate reaches every strict exponent \(c<7/2\). It does not include \(c=7/2\), where fixed-slice finiteness itself fails.

## Q3 — verdict and reusable estimate

**FACT.** The crude coercivity bound undershoots drastically. Near the target it loses precisely a factor \(\sigma^{-6}\):
\[
\frac{\sigma^{-2c}}{\sigma^{-(2c-6)}}=\sigma^{-6}.
\]
It treats all six stable directions as though they also collapsed.

The needed front-first/per-singular-value estimate has the form
\[
\int_{[-1,1]^7}
\left(\sum_{j=1}^7s_j^2u_j^2\right)^{-c}du
\;\lesssim_c\;
\left(\prod_{j=1}^6s_j^{-1}\right)s_7^{\,6-2c},
\qquad 3<c<\frac72.
\]
When \(s_1,\dots,s_6\ge\kappa\),
\[
I_c\lesssim_{c,\kappa}s_7^{-(2c-6)}.
\]
This is exactly the two-block-radial/front-first majorant: integrate the stable block first, leaving only the collapsing direction to carry the power \(2c-6\).

**FACT.** With five stable and two comparably collapsing directions,
\[
\int (|y|^2+\sigma^2|z|^2)^{-c}\,dy\,dz
\asymp \sigma^{5-2c},
\]
so
\[
\boxed{\beta=2c-5}.
\]
More anisotropically, for \(s_7\le s_6\),
\[
I_c\lesssim
\left(\prod_{j=1}^5s_j^{-1}\right)s_6^{-1}s_7^{\,6-2c}.
\]
If \(s_6\asymp s_7\asymp\sigma\), this becomes \(\sigma^{-(2c-5)}\).

**INFERENCE.** Provided the deeper stratum has a genuine two-dimensional tube with radial threshold \(\beta<2\),
\[
2c-5<2\iff c<\frac72.
\]
Thus the deeper rung is a corank recursion and does not worsen the threshold. The codimension-one/simple-collapse stratum already binds; higher-corank strata reproduce the same strict \(7/2\) endpoint under matching tube codimension.

**Verdict:** sharper anisotropic estimation is required. The banked fixed-\(\theta\) result gives slice finiteness for \(c'<7/2\); only the front-first/two-block-radial estimate preserves that exponent through the outer integration.