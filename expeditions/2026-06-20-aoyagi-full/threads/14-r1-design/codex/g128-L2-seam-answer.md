**Verdict: sound.**

**FACT.** The false bridge is `F ∘ χ = Σ Eᵢ² + G²`. The computed chart instead gives cross terms, so S1.5 cannot be fed directly from that literal identity.

**INFERENCE.** The sound green-tool bridge is the two-sided squeeze:
\[
c_1\Phi \le F \le c_2\Phi
\]
near the deepest point, with \(c_1,c_2>0\), followed by `rlctAt_mono` in both directions and positive-constant unit invariance.

Explicitly, since \(F,\Phi\ge 0\):

1. From \(c_1\Phi \le F\), we get
\[
\Phi \le c_1^{-1}F.
\]
Together with \(\Phi=0 \Rightarrow F=0\), `rlctAt_mono` gives
\[
\operatorname{rlctAt}(\Phi)\le \operatorname{rlctAt}(c_1^{-1}F)
=\operatorname{rlctAt}(F).
\]

2. From \(F\le c_2\Phi\), together with \(F=0\Rightarrow \Phi=0\), `rlctAt_mono` gives
\[
\operatorname{rlctAt}(F)\le \operatorname{rlctAt}(c_2\Phi)
=\operatorname{rlctAt}(\Phi).
\]

Hence
\[
\operatorname{rlctAt}(F)=\operatorname{rlctAt}(\Phi).
\]

The equalities after multiplying by \(c_1^{-1}\) and \(c_2\) are exactly positive unit invariance. No ideal-generator-invariance lemma is being used.

**Squeeze Validity**

**FACT.** In the example,
\[
F=g_{00}^2+g_{01}^2+g_{10}^2+g_{11}^2,
\qquad
\Phi=g_{00}^2+g_{01}^2+g_{10}^2+G^2,
\]
and
\[
F-\Phi=g_{11}^2-G^2=(g_{11}-G)(g_{11}+G).
\]

**FACT.** The structural computation says \(g_{11}-G\in (g_{00},g_{01},g_{10})\), the regular ideal.

**INFERENCE.** Therefore the cross-error is controlled by the regular block. Locally one can write
\[
g_{11}=G+\sum_i g_i h_i,
\]
with \(g_i\in\{g_{00},g_{01},g_{10}\}\) and bounded \(h_i\). Then
\[
F=\sum_i g_i^2+\left(G+\sum_i g_i h_i\right)^2.
\]
For sufficiently small neighborhood, the bounded perturbation \(\sum_i g_i h_i\) cannot make \(F\) vanish faster than
\[
\sum_i g_i^2+G^2.
\]
Equivalently, the quadratic form in variables \((g_{00},g_{01},g_{10},G)\),
\[
|g|^2+(G+h\cdot g)^2,
\]
is uniformly comparable to \(|g|^2+G^2\) when \(h\) is bounded. Thus there are local constants \(c_1,c_2>0\) with
\[
c_1\Phi\le F\le c_2\Phi.
\]

So there is no direction where \(F\) vanishes faster than \(\Phi\), or conversely, as long as the coefficients \(h_i\) remain locally bounded. The numerics are consistent with this structural reason, but the proof is the bounded-linear-perturbation estimate.

**Measure-Jacobian Concern**

**FACT.** The squeeze comparison is between \(F\) and \(\Phi\) at the same point.

**INFERENCE.** Therefore this route uses no change of variables and no measure-preserving homeomorphism step. The Jacobian unit from \(\chi\) never enters. The only units needed are the positive constants \(c_1^{-1}\) and \(c_2\), stripped by unit invariance. So the “two units” concern is moot for this bridge.

**Final Chain**

**FACT/INFERENCE combined.**

\[
\operatorname{rlctAt}(F)
=
\operatorname{rlctAt}(\Phi)
=
\operatorname{rlctAt}\left(g_{00}^2+g_{01}^2+g_{10}^2+G^2\right).
\]

Then S1.5 applies to \(\Phi\), because its regular block has three nondegenerate regular squares with pivots disjoint from the core variables of \(G\). Hence
\[
\operatorname{rlctAt}(\Phi)
=
\frac{3}{2}+\operatorname{rlctAt}(G^2).
\]

For the reduced \((1,1,1)\) core, \(\operatorname{rlctAt}(G^2)=1/2\), so
\[
\operatorname{rlctAt}(F)=\frac32+\frac12=2.
\]

So yes: the sound green-tool bridge for a114e07e’s seam is the squeeze plus `rlctAt_mono` both ways plus unit invariance, then S1.5 on \(\Phi\). It avoids both the false literal-form claim and the absent ideal-generator-invariance lemma.