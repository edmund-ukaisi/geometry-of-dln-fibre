### Q1

[FACT] **Verdict:** If Aoyagi’s theorem applies to this exact real germ, it forbids every undershooting divisor; without invoking it, deeper coupled valuations remain a genuine possible failure mode that Watanabe’s upper bound does not exclude.

- [FACT] Equality means \(\inf_v A(v)/\operatorname{ord}_v(F)=\tfrac12\minAdm\), so no valuation can have smaller ratio.
- [FACT] Watanabe supplies only \(\mathrm{rlct}\le\tfrac12\minAdm\); codimension alone gives no lower bound.
- [FACT] The failure mechanism is a non-pivot locus where every residual generator vanishes: further blow-up adds residual multiplicity faster than discrepancy, potentially lowering the ratio.
- [INFERENCE] Ruling this out for the DLN tree is precisely the load-bearing content of Aoyagi’s \((S,J)\) lower-bound induction, not of the QIP codimension calculation.

### Q2

[INFERENCE] **Verdict:** A fixed finite instance admits an exact chartwise computation, but independent per-divisor minima are insufficient; a uniform general-\(d\) proof needs the \((S,J)\) induction or an equivalent structural invariant.

- [FACT] On an explicit chart, \(\operatorname{ord}_E(F)=2\min_{ij}\operatorname{ord}_E((\prod C)_{ij})\), so each displayed divisor is easy to test.
- [FACT] A terminal unit is a joint condition at the intersection of divisors, not merely a generic condition along each divisor.
- [FACT] For example, \(I=(x,y)\) has order \(0\) generically along both coordinate divisors, yet no generator is a unit at their intersection.
- [FACT] A CAS can verify every leaf of a fixed tree by factoring the claimed monomial and checking that some residual entry has nonzero constant term.
- [INFERENCE] Induction is needed to enumerate all DLN leaves and prove that a realizing pivot survives every recursive shear; this is global combinatorics, not a new analytic theorem.

### Q3

[INFERENCE] **Verdict:** The most practical independent certificate is a sharp monomial Gröbner degeneration; it is exact if found, but sharpness and computational feasibility are not guaranteed for deep-mixed instances.

- [FACT] Compute \(J=\operatorname{in}_w(I_{\mathbb C})\); if its Newton-polyhedron LP gives \(\operatorname{lct}_{\mathbb C}(J)=\minAdm\), semicontinuity yields \(\operatorname{lct}_{\mathbb C}(I)\ge\minAdm\).
- [FACT] Then \(\mathrm{rlct}_{\mathbb R}(\sum f_i^2)\ge\tfrac12\operatorname{lct}_{\mathbb C}(I)\); the known coupled divisor supplies the reverse inequality.
- [FACT] This is compatible with the larger original toric minimum because degeneration changes the ideal and may lower its lct.
- [INFERENCE] Gröbner basis plus an exact rational LP is plausible for the smallest cases; deep \(20\!-\!40\)-variable examples may explode or yield only a non-sharp bound.
- [FACT] Generalized Bernstein–Sato computation is definitive if it terminates, but is usually substantially less feasible; integral closure alone does not supply discrepancies.