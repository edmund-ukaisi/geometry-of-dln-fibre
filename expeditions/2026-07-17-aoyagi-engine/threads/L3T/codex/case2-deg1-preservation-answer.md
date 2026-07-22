**VERDICT — [KNOW]: NOT-DERIVABLE/FALSE.**

Take \(D=2\), coordinates \(p,i\), center \(\{p,i\}\), pivot \(p\), and
\[
\operatorname{sh}(u_p,u_i)=(u_p,u_i+u_p).
\]
This is a polynomial bijection, fixes \(0\), and preserves the pivot coordinate. For one output \(j_0\), set
\[
\operatorname{foldResid}_p(j_0,w)=w_p+w_i
\]
(and set other outputs to zero). This satisfies (H), using constant coefficients \(c_p=c_i=1\).

Then \(\operatorname{quotMap}(u)=(1,u_i+u_p)\), so:

- \(\delta=1\): the child residual is \(1+u_i+u_p\), which is nonzero at \(0\). Hence it cannot be Deg1-supported on any \(C'\).
- \(\delta=0\): the child residual is
  \[
  u_p(1+u_i+u_p)=u_p+u_pu_i+u_p^2.
  \]
  No \(C'\subseteq\{p,i\}\) works: support \(\{i\}\) fails on \(u_i=0\); support \(\{p\}\) would require the quotient \(1+u_i+u_p\) to ignore \(p\); support \(\{p,i\}\) permits only constant coefficients, hence only a linear function; empty support gives zero.

(The \(\delta=0\) failure uses \(D\ge2\) and an allowed nontrivial shear.)

**Minimal clean repair — [KNOW].** Put \(T=\mathrm{center}\setminus\{p\}\) and
\[
G_j(u)=\operatorname{foldResid}_p(j,\operatorname{quotMap}(u)).
\]
Assume directly
\[
\operatorname{Deg1SupportedOn}(G,T,\mathbb R^D).
\]
Then choose \(C'=T\). For \(\delta=1\) this is immediate. For \(\delta=0\), if
\[
G_j(u)=\sum_{i\in T}a_i(u)u_i,
\]
then
\[
u_pG_j(u)=\sum_{i\in T}(u_pa_i(u))u_i,
\]
and \(u_pa_i\) still ignores \(T\), since \(p\notin T\).

Merely requiring \(\operatorname{foldResid}_p(j,e_p)=0\), a vanishing pivot coefficient, or parent Deg1-support on \(T\) is insufficient for arbitrary permitted shears.

**Shear issue — [INFER from the definitions].** The hypothesis above already incorporates the shear. A parent-only support condition implies it only when the shear is \(T\)-block-preserving: outside-\(T\) outputs ignore \(T\), while each
\[
(\operatorname{sh}u)_i=\sum_{k\in T}A_{ik}(u_{T^c})u_k,\qquad i\in T.
\]
Nontrivial block-linear shears are allowed. Arbitrary shears are not: for example \((\operatorname{sh}u)_i=u_i+u_p^2\) turns the valid parent residual \(w_i\) into \(u_i+u_p^2\), which has no Deg1 support.