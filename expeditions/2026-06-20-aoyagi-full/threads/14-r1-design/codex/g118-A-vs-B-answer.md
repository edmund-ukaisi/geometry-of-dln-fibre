**Verdict:** the general zero-core recursion step is **BOTH-IN-SEQUENCE**:

1. **Blow up** a coordinate/rank-stratum center of codimension  
   \[
   c=Mval(t).
   \]
   In a pivot chart
   \[
   y_a=u,\qquad y_j=u v_j\quad (j\ne a),
   \]
   with untouched coordinates \(z\), the Jacobian is exactly
   \[
   dy_1\cdots dy_c\,dz
   = \pm u^{c-1}\,du\,dv\,dz,
   \]
   hence for RLCT densities:
   \[
   |Jac|=|u|^{Mval(t)-1}.
   \]
   The pullback contributes
   \[
   F\circ\pi = u^2\cdot F_{\mathrm{res}},
   \]
   so the new exceptional divisor has
   \[
   k=1,\qquad h=Mval(t)-1,\qquad \frac{h+1}{2k}=\frac{Mval(t)}2.
   \]

2. **Then** use the det-1 Schur/product clear inside that chart, after the blow-up has exposed a unit minor. This Schur step has Jacobian \(1\), so it adds no monomial weight. Its role is normalization/reduction of the residual chain, not the source of the RLCT discrepancy.

So: **A alone is false for the zero-core recursion**. **B alone is structurally incomplete** if it omits the Schur normalization. The correct Lean contract is blow-up discrepancy plus unit-Jacobian Schur reduction.

**Terminal Leaves**

For the zero-core resolution, the terminal leaf is **not generally a smooth block**.

The correct terminal form is:

\[
F\circ\pi
=
\text{unit}\cdot
\prod_i |u_i|^{2k_i}
\]

or, in branches where regular quadratic variables remain,

\[
F\circ\pi
=
\text{unit}\cdot
\prod_i |u_i|^{2k_i}
\cdot
(z_1^2+\cdots+z_d^2).
\]

So the terminal type is **pure monomial** or **monomial \(\times\) smooth block**. The all-dims-1 leaf is the pure monomial
\[
(c_1\cdots c_L)^2,
\]
not a smooth single-matrix block.

The leaf threshold is therefore the `monomialThreshold(d,k,h)` style quantity, using accumulated \(k_i,h_i\), with divisor ratios

\[
\frac{h_i+1}{2k_i}.
\]

**Headline**

Yes: the zero-core headline is **inf/min over monomialThreshold leaves**. The det-1 Schur appears inside each blow-up chart only as a measure-preserving chain-reduction step.

For the original rank-\(r\) fibre:

\[
\operatorname{RLCT}(F)
=
\frac{nReg}{2}
+
\lambda_{\mathrm{core}},
\]

where the first term is Aoyagi’s det-1 product-reduction for \(B\ne 0\), and

\[
\lambda_{\mathrm{core}}
=
\frac12\min_{\mathrm{Adm}} Mval
\]

comes from the blow-up resolution of the \(B'=0\) zero-core.

**Blunt Assessment**

FACT: the det-1 Schur/product-reduction is valid when the required leading minor is a unit. At the deepest zero-core origin, the relevant product is zero, so that hypothesis fails.

FACT: the \((2,2,2)\) ladder’s nontrivial RLCT \(3/2\) requires blow-up Jacobians. A clean det-1 recursion would miss those discrepancies.

INFERENCE: the earlier certificate saying the recursion “bottoms out at a smooth block leaf” via unimodular det-1 \(Q\) was **imprecise/incomplete for the zero-core resolution**. If read as the zero-core Lean contract, it is **wrong**.

The correction is:

- det-1 product-reduction handles the \(B\ne0\) regular peel and gives the additive \(nReg/2\);
- zero-core resolution uses blow-up nodes with Jacobian \(|u|^{Mval(t)-1}\);
- det-1 Schur clears only after the blow-up has created a unit minor;
- terminal leaves are normal-crossing monomial or monomial times smooth block;
- the core RLCT is computed by `monomialThreshold`, not by a clean smooth-leaf additive chain.