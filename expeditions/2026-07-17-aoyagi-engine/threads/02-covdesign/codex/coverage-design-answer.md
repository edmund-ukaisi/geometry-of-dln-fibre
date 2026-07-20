**Q1.** [proof-sketch you can defend] A sufficient chart family must satisfy: (i) **[load-bearing new]** a finite, terminating blow-up tree over some neighbourhood \(V\ni0\), where every proposed center is smooth and every parent blow-up is covered by its listed children; hence the terminal charts cover the entire resolved preimage of \(V\); (ii) **[load-bearing new]** on every terminal chart,
\[
F\circ\pi=a(u)\prod_i |u_i|^{\nu_i},\qquad
|\det D\pi|=b(u)\prod_i |u_i|^{\kappa_i},
\]
with \(a\) bounded away from \(0\), \(b\) bounded above, and every divisor with \(\nu_i>0\)—exceptional or strict-transform—present in the list; (iii) **[bookkeeping, given]** each listed ratio \((\kappa_i+1)/\nu_i\) is \(M\!\operatorname{val}(t)/2\ge\minAdm(M)/2\); and (iv) **[bookkeeping]** \(\kappa_i-c'\nu_i>-1\), so the pulled-back product integral converges. [assumed] This uses the standard change-of-variables theorem for proper analytic modifications. [proof-sketch you can defend] Local convergence near \(0\) implies convergence on \(B\): for small \(\rho\) with \(\rho B\subset V\),
\[
I_B(c')=\rho^{\,2Lc'-N}I_{\rho B}(c').
\]

**Q2.** [proof-sketch you can defend] If \(r\) is the maximal initial constant-run length of the exact monomials \(b_{J+1},\dots,b_{M^{(S)}}\), then \(r<M^{(S)}-J\) or \(r=M^{(S)}-J\); this proves only that Cases 1 and 2 exhaust symbolic states. [heuristic/inference] The description given does **not** prove that 1(1)/1(2) exhaust geometric charts. What is needed is a local covering lemma: if the actual center has ideal \((g_1,\dots,g_d)\), then its blow-up is covered by the standard charts
\[
U_i:\quad g_j=g_i z_j ,
\]
and a support-preserving calculation must identify every \(U_i\) with exactly one stated child, including mixed exceptional factors. “Divisible by \(u\)” must mean divisibility in the local coordinate ring, not a pointwise condition. [proof-sketch you can defend] Outside the center the blow-up is an isomorphism, while over it the \(U_i\) cover the projective exceptional fibre; induction over the finite tree then gives global coverage. Properness supplies compact preimages and finite subcovers, but does not establish the child formulas or their exhaustiveness.

**Q3.** [proof-sketch you can defend] The appropriate proof is a per-blow-up ledger induction nested inside the well-founded \((S,J)\)-induction: retain the exact monomial support of every generator; pass old divisors to their strict transforms; add every irreducible component of the new exceptional divisor; and prove that the standard affine charts cover before continuing. The candidate family is precisely every prime divisor \(D\) in the terminal support of \(F\circ\pi\): all exceptional divisors created at any stage, their strict transforms, and any surviving strict-transform divisor of the original zero locus. Every exceptional prime of a composite blow-up is the strict transform of one created at a definite stage, so there are no other divisors on that model. Coverage places its generic point in a terminal chart, where the given admissible-profile computation yields
\[
\frac{\operatorname{ord}_D(\operatorname{Jac}\pi)+1}
     {\operatorname{ord}_D(F)}
=\frac{M\!\operatorname{val}(t)}2
\ge\frac{\minAdm(M)}2 .
\]
[proof-sketch you can defend] Arbitrary divisors obtainable by further blowing up an already normal-crossing chart need not be checked for integrability; blowing up a coordinate stratum produces a ratio that is a weighted average of the existing ratios, with a nonnegative transverse contribution.

**Q4.** [heuristic/inference] The sharpest likely failure is that 1(1)/1(2) replaces the actual **weighted generator ideal** by a common-factor or unweighted block, so its alleged children are not all standard charts of the true blow-up. The smallest test is \(M=(2,2,1)\), on the corank-two \(J=0\) branch passed from the \(2\times2\) layer to the final column, with exact residual generators
\[
(d_1x,\ d_2y),\qquad b=(d_1,d_2),
\]
hence partial-run Case 1 with \(J_1=1\). [proof-sketch you can defend] Here \(\minAdm(2,2,1)=2\), while conflating the supports gives \((dx,dy)\); the two local losses have thresholds \(1\) and \(1/2\), respectively, by direct integration. Thus any transition that forgets the separate supports \(\{d_1\}\) and \(\{d_2\}\) either misses a chart or invents a spurious low-ratio divisor.