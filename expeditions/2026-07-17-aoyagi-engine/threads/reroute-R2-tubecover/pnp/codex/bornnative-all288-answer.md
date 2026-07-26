## 1. INVARIANCE

**Provable fact.** Let \(\sigma\) fix the origin, be a coordinate permutation, and satisfy \(L\circ\sigma=L\). For
\[
F^\sigma=\sigma^{-1}\circ F\circ\sigma,
\]
we have
\[
L(F^\sigma(x))=L(F(\sigma x)),\qquad
|\det DF^\sigma(x)|=|\det DF(\sigma x)|.
\]
The domain change \(y=\sigma x\) has unit Jacobian, so the local zeta integrals—and hence the true RLCT—are identical. Preserving only the zero set of \(L\) would not suffice; one needs equality, or at least multiplication/comparison by positive analytic units.

This cleanly covers the **fully conjugated** chart
\[
\sigma_{p_1}^{-1}\circ g_{\rm leaf}(20,p_2,p_3)\circ\sigma_{p_1}.
\]

It does **not** automatically cover \(g_{\rm native}\). Full conjugation also conjugates both inner blow-ups:
\[
\sigma^{-1}bb(C_i,p_i)\sigma.
\]
For \(p_1\neq20\), even \(C_1=A_0\text{-slots}\setminus\{20\}\) is generally sent to the complement of \(p_1\), not back to \(C_1\). Thus shear-only conjugation is not a domain reparametrization of the canonical chart unless additional fan-equivariance identities are proved. That is the gap.

## 2. OVER-VANISHING

Write the pulled-back generators as \(h_\alpha=x^a q_\alpha\), where \(x^a\) is their monomial GCD, and put \(c=\kappa+\mathbf1\).

If some \(q_\alpha(0)\neq0\), then \(x^a\) itself occurs and
\[
D=\min_{i:a_i>0}\frac{c_i}{a_i},\qquad \operatorname{rlct}=D/2.
\]

If every \(q_\alpha(0)=0\), the strict-transform ideal still vanishes at the exceptional-stratum origin. Its full residual Newton support then matters. Precisely,
\[
D=\min_{\substack{w\ge0\\ w\cdot m\ge1\ \forall m}}c\cdot w.
\]
The chart is safe exactly when \(D\ge8\).

For the fixed-shear \(\Delta\)-dominants, the wrongly aligned clearing left such an unresolved vanishing center without enough Jacobian discrepancy. The exact LP found \(D=2\) for \(p_1=5,6,7\) and \(D=5\) for \(p_1=4\), giving RLCT \(1,1,1,2.5\). Thus “empty survivor” is neither safe nor unsafe by itself; the discriminant is whether a normalized valuation with \(c\cdot w<8\) exists.

## 3. WHERE-IT-WOULD-BREAK

With a survivor, failure means
\[
\frac{\kappa_i+1}{a_i}<8
\]
for some coordinate in the GCD support. In the stated squarefree situation, a survivor involving a coordinate with \(\kappa_i=3\) gives \(D\le4\), hence RLCT \(\le2\). Without a survivor, a combined low-cost weight \(w\) can produce the same failure.

**Most plausible family:** the old dangerous block
\[
p_1\in\{4,5,6,7\},
\]
restricted to inner pivots for which the \(p_3\)-coordinate retains Jacobian exponent \(3\); \((p_2,p_3)=(0,1)\) is the first representative to test where applicable. This combines the known \(\Delta\)-block sensitivity with the non-equivariant inner fan.

The cheapest exact test is:

1. For those leaves, compute only the monomial GCD, residual constants, and \(\kappa\).
2. If a survivor touches a ratio \(<8\), stop: RED.
3. Only for empty-survivor cases, solve that leaf’s small exact Newton LP and test \(D<8\).

## 4. VERDICT PRIOR

**Plausible inference, not proof:** failure is more likely than universal success. Native conjugation repairs the shear alignment, but the fixed inner fan is not simultaneously conjugated; its asymmetric \(C_1,C_2\), low-discrepancy coordinates, and possible empty survivors leave no structural invariance protecting all 288 leaves.

The settling fact is the exact value
\[
\min_{\text{288 leaves}}D.
\]
Equivalently, one leaf with \(D<8\) disproves the claim; exact certificates \(D\ge8\) for every leaf prove it.