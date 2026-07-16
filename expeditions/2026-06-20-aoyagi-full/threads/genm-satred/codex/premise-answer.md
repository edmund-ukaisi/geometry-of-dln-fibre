### Q1

**VERDICT: sound as an algebraic reorganization; no Jacobian unless \(P^{-1}B_{12}\) becomes a new coordinate.**

**PROVEN.** Keeping the original variables,
\[
[P\mid B_{12}]
\binom{Q_p}{Q_b}
=PQ_p+B_{12}Q_b
=P(Q_p+P^{-1}B_{12}Q_b),
\]
so the energy and measure are unchanged: Jacobian \(=1\). Likewise, stacking \((P,C)\mapsto[P;C]\) has absolute Jacobian \(1\).

If one actually substitutes
\[
D=P^{-1}B_{12},\qquad B_{12}=PD,
\]
then
\[
dP\,dB_{12}=|\det P|^{\,b}\,dP\,dD.
\]
Conversely, \(dP\,dD=|\det P|^{-b}dP\,dB_{12}\). This factor is harmless only on a pivot chart with \(\sigma_{\min}(P)\ge\delta>0\). Merely assuming \(P\) is pointwise invertible while allowing \(P\to\{\det P=0\}\) is insufficient.

The shear
\[
(Q_p,Q_b)\mapsto(Q_p+DQ_b,Q_b)
\]
has Jacobian \(1\) and preserves \(\operatorname{rank}G\). But the wide product itself is not rank-preserving:
\[
\operatorname{rank}(FG)\neq\operatorname{rank}G
\]
in general. For example \(P=B=1,Q_p=1,Q_b=-1\) gives \(FG=0\) while \(\operatorname{rank}G=1\). What is true is that, for \(\operatorname{rank}G=r\), the linear map \(F\mapsto FG\) on unrestricted front directions has rank \(ur\). Tall \(F\) is injective, so there \(\operatorname{rank}(FG)=\operatorname{rank}G\).

### Q2

**VERDICT: the distinction is real, but automatic pivot-Gram absorption is only an inference.**

**PROVEN under fixed-rank-chart hypotheses.** If \(\operatorname{rank}Z_{\rm deep}=\rho\), its nonzero singular values are uniformly bounded away from zero, \(b\le\rho\), and the \(A_{\rm cor}\)-box meets the rank-deficient locus, then
\[
\int \det\!\big((A_{\rm cor}Z)(A_{\rm cor}Z)^T\big)^{-a/2}\,dA_{\rm cor}
\]
reduces to the standard \(b\times\rho\) matrix integral and is finite exactly when
\[
a<\rho-b+1.
\]
Equality gives logarithmic divergence. If the box stays away from rank loss, this condition is unnecessary; if \(Z\) itself degenerates, the estimate is not uniform and joint analysis is required.

The pivot determinant is integrated over a different parameter map \(z\mapsto\widetilde Q_p(z)\). Therefore the \(A_{\rm cor}\) threshold cannot simply be applied to it. However, it is not automatically integrable. If \(\widetilde Q_p\) locally ranges submersively over all \(u\times n\) matrices, the analogous standalone condition is
\[
a<n-u+1.
\]
For a structured reduced chain, the condition is instead the integrability threshold of the pulled-back determinant.

The pivot Gram is genuinely IH-absorbed only when:

- the IH explicitly handles the finite-\(N\) \(C\)-integral or the corresponding weighted reduced chain; or
- \(P\) remains uniformly invertible, so the complete tall energy is uniformly comparable to \(\|\widetilde Q_p\|_F^2\).

It is not enough to extract \(\det(\widetilde Q_p\widetilde Q_p^T)^{-a/2}\) pointwise and then invoke an unweighted IH.

A scalar countercheck makes this precise:
\[
\int_{-1}^1\!\int_{-1}^1e^{-N(1+c^2)z^2}\,dz\,dc
\sim 2\sqrt\pi\,\operatorname{arsinh}(1)\,N^{-1/2},
\]
with no logarithm, although the extracted pivot weight \(|z|^{-1}\) is nonintegrable. Thus “carry it to the IH” must mean carrying the full finite-\(N\) coupling, not treating the bare determinant as harmless.

So: **do not apply the corank strong-block lemma to a pivot Gram**, but a pivot Gram still needs either IH closure or its own convergence analysis.

### Q3

**Biggest risk:** a non-uniform Gaussian/Fubini step that replaces the finite front integral by a bare determinant near rank drop. This can create or erase exactly the boundary logarithms under discussion.

**Cheapest exact check:** prove on every claimed pivot-IH chart the uniform comparison
\[
m^2\|Q\|_F^2
\le \|PQ\|_F^2+\|CQ\|_F^2
\le (M^2+K^2)\|Q\|_F^2,
\]
with \(m>0\) and constants uniform on the chart. This immediately proves equality of RLCT and log multiplicity with the reduced chain. If such uniform constants fail, the proposed IH absorption is not justified.

Finally, **P3 remains an inference** from the supplied information: its proof must include rank-stratum normal Jacobians/codimensions and logarithmic multiplicities, not only the minimum exponent.