**Q1 — PROVEN.** Resolving individual factor-rank strata does **not** principalize the product ideal. The smallest failure is \(n=2,\ k=2\).

Near a balanced point, with \(W\) invertible, analytic row/column changes give
\[
P\sim\begin{pmatrix}1&0\\0&x\end{pmatrix},
\qquad
Z\sim\begin{pmatrix}y+bc&b\\ c&1\end{pmatrix}.
\]
Hence
\[
I(PZW)=I(PZ)=(x,y,b).
\]
Here \(x=0\) and \(y=0\) are the individual rank-drop divisors of \(P\) and \(Z\); \(b=0\) is the alignment condition. Blowing up the lower factor-rank loci is locally an isomorphism, while blowing up either Cartier divisor does nothing. Thus \((x,y,b)\) remains nonprincipal. A genuinely joint center survives.

The case \(n=1\) is already the monomial \(pzw\), so \(n=2,k=2\) is minimal.

**Q2 — PROVEN, with a distinction.** The relevant map to the composite rank locus is non-transverse. For multiplication
\[
\mu(P,Z)=PZ,
\]
the derivative has
\[
\operatorname{coker}(d\mu)\cong
\operatorname{Hom}(\ker Z,\operatorname{coker}P).
\]
It therefore fails to be surjective whenever both factors have positive corank. Equivalently, transversality would give codimension \(k^{2}\), contradicting the balanced codimension \(C_k<k^{2}\).

In the minimal chart, the pullback of the codimension-four center \(PZ=0\) is the smooth codimension-three center
\[
B=(x,y,b)=0.
\]
Blowing up \(B\) has Jacobian exponent \(2\), hence log discrepancy \(3=C_2\), not \(4\).

A direct blow-up of an actual codimension-\(m^2\) smooth center still has log discrepancy \(m^2\). What fails is identifying its non-submersive pullback with such a blow-up or assigning that \(m^2\) charge to the balanced component. In larger cases the replacement is not automatically \(C_m\); its multiplicity and subsequent divisors require joint computation.

**Q3 — PROVEN negatively for factor-only induction; INFERENCE for uniformity.** The residual is not a smaller instance closed by the same factor-rank recursion. Already for \(n=2\), the residual \((x,y,b)\) is nonprincipal, whereas the strictly smaller \(n=1\) product is principal. The extra alignment coordinate is new data.

This does not imply an unrelated construction is needed for every \(n\). A single uniform resolution indexed by ranks **and alignment/intersection data** could cover all sizes. Its charts will involve rectangular block-composition ideals and joint centers, not merely the original square factor-rank problem.

**Q4 — PROVEN as a necessity statement.** The single-factor discrepancy bookkeeping cannot establish \(c^*\). Moreover, neither line of F3 is justified on the balanced locus:

- \(m^2\) assumes the false transversality.
- Replacing \(m^2\) by \(C_m\) still assumes that the joint center splits from an independent reduced chain, which also fails.

The minimal new result is a **uniform joint-composition-ideal log-resolution theorem**: for all rectangular dimension vectors arising in the recursion, construct smooth joint rank/alignment blow-up centers such that

\[
I(PZW)\mathcal O_{\widetilde X}
 =\mathcal O_{\widetilde X}\!\left(-\sum_E N_EE\right)
\]
has SNC support, compute
\[
K_{\widetilde X/X}=\sum_E(A_E-1)E,
\]
and prove directly
\[
\min_E\frac{A_E}{2N_E}
   =\frac12\minAdm(n,n,n,n).
\]

That is essentially the required product-corank/quiver-incidence resolution theorem. A native proof remains possible, but only by proving this joint theorem; it is not factor-only “detail at scale.”

**WALL-REQUIRES-JOINT-RESOLUTION**