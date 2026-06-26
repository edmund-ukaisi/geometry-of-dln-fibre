Let \(\delta=r(d_0+d_N-r)\) and \(C_{\mathrm{sh}}=Q-\delta\), the top codimension of the shifted zero-product problem.

**(1) Rank**
**PROVEN.** For \(A\in \mathrm{Fib}\), let \(U_i=(A_i\cdots A_1)(k^r)\subset k^{d_i}\). Then \(A_i:U_{i-1}\to U_i\) is an isomorphism, and the quotient maps
\[
\bar A_i:k^{d_{i-1}}/U_{i-1}\to k^{d_i}/U_i
\]
satisfy \(\bar A_N\cdots \bar A_1=0\). The differential rank splits as
\[
\operatorname{rank}J(A)
=
\delta+
\dim\sum_i
\operatorname{im}(\bar A_N\cdots \bar A_{i+1})
\otimes
\operatorname{Ann}\ker(\bar A_{i-1}\cdots \bar A_1).
\]
The \(\delta\)-part is the fixed rank-\(r\) endpoint block; the second summand is exactly the shifted zero-product Jacobian rank.

**PROVEN, given the established Kostant-component description.** On the dense orbit of every top shifted zero-product component, the second term is \(C_{\mathrm{sh}}\). Hence on the generic top stratum
\[
\operatorname{rank}J(A)=\delta+C_{\mathrm{sh}}=Q.
\]
So the fibre is generically smooth along every top component.

**PROVEN.** The precise rank-drop locus is
\[
\{A\in \mathrm{Fib}:\operatorname{rank}J(A)<Q\}
=
\{A:\dim \mathcal I(\bar A)<C_{\mathrm{sh}}\},
\]
where \(\mathcal I(\bar A)\) is the displayed sum. Equivalently it is the closed determinantal locus cut by all \(Q\times Q\) minors of \(J\). This is not the same as “non-top locus”: on smaller components the rank may be \(>Q\).

**(2) Global Minor Verdict**
**PROVEN verdict: per-component in general.** There is no single fixed coordinate \(Q\times Q\) Jacobian minor that works across all top components in general.

The structural reason is column support. The shifted zero-product part of \(dF_A=\sum_i L_i\dot A_iR_i\) is carried by the arrows/intervals responsible for the zero product in that Kostant component. Different top components use different active intervals, so their possible pivot columns are incompatible.

**PROVEN obstruction in the given small case.** For \(d=(2,2,2,2,2)\), \(r=0\), top components are indexed generically by pairs \(p<q\): \(A_p,A_q\) have rank \(1\), the other arrows are invertible, and the transported image/kernel incidence makes the product zero. On the component \((p,q)=(1,2)\),
\[
d(A_4A_3A_2A_1)
=
A_4A_3(A_2\dot A_1+\dot A_2A_1),
\]
so all columns from \(A_3,A_4\) vanish. A nonzero \(3\times3\) minor must use only columns from \(A_1,A_2\). On the component \((3,4)\), the opposite is true: columns from \(A_1,A_2\) vanish, so the minor must use only \(A_3,A_4\). One fixed 3-column set cannot do both.

**PROVEN local canonical form.** On a component-adapted block chart, choose rows consisting of:

- the \(\delta\) endpoint equations: entries with target row in the rank-\(r\) image block or source column in the rank-\(r\) source block;
- \(C_{\mathrm{sh}}\) quotient equations forming a Ferrers/staircase basis for the shifted zero-product differential.

Choose columns from endpoint variables in \(A_1,A_N\) for the \(\delta\)-block, and component-specific quotient pivot variables for the shifted block. The Jacobian minor is block triangular with unit diagonal on that chart.

**HEURISTIC / classification note.** A single fixed minor can exist only in special common-pivot cases where the generic Jacobian matroids of all top components share one basis. The general theory should not assume this.

**(3) Which Equations When \(Q<d_Nd_0\)**
**PROVEN.** Uniformly include the \(\delta\) non-quotient equations: in block form, all product entries except the bottom-right shifted block. For the remaining \(C_{\mathrm{sh}}\) equations, choose a basis of
\[
\mathcal I(\bar A)=\sum_i \operatorname{im}\bar L_i\otimes \operatorname{Ann}\ker\bar R_i.
\]
Equivalently, omit equations spanning the moving dependency space
\[
\mathcal D(\bar A)=
\{\Lambda:\Lambda(\operatorname{im}\bar L_i)\subseteq \ker\bar R_i\ \forall i\}.
\]
This choice is uniform only after fixing the endpoint flag/pivot chart; it is not globally uniform on the whole generic locus.

For \(d=(2,2,2,2,2)\), \(r=0\), the generic Jacobian image is a hyperplane in the four output entries. In adapted coordinates one may normalize the relation to \(dF_{12}=0\), so \(F_{11},F_{21},F_{22}\) carry full rank. In arbitrary fixed coordinates the relation is \(\ell(\dot P\,v)=0\); choose any three entries omitting one whose coefficient in \(\ell\otimes v\) is nonzero. That omitted entry changes by chart.