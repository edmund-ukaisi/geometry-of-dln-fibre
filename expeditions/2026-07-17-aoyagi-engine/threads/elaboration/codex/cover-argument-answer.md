1. The terminal pivot charts form an open cover of \(Q\): each blow-up’s \(c\) standard charts cover its projective exceptional directions, so all leaves cover inductively. Properness gives \(g(Q)=V\). Exceptional divisors lie in \(Q\), are covered, and map to the centres; the centres are not omitted set-theoretically. “A.e.” means that the exceptional/critical locus and its lower-dimensional image may be ignored in change of variables, since \(g\) is one-to-one off them.

Open charts overlap, so
\[
\int_V\neq\sum_U\int_U
\]
for unweighted chart integrals. The standard resolution treatment is
\[
\int_V=\int_Q=\sum_U\int_U\rho_U
\]
using a partition of unity. Equivalently, one may restrict pivot charts to largest-coordinate sectors and assign ties measurably; sector boundaries are null and the pieces are a.e. disjoint. Both readings work, but the Watanabe/Aoyagi boxed-rule lineage uses the proper-map/open-atlas formulation; Aoyagi writes an integral over \(Q\), not an unweighted chart sum.

CONFIDENCE: high — this is the standard blow-up atlas and manifold integration construction.

2. On a relevant chart,
\[
|F\circ g|^{-c}|{\det Dg}|\,\phi\circ g
 =a(u)\prod_j|u_j|^{h_j-2ck_j},
\]
with \(a\) positive and bounded near the point. Its integral converges exactly when
\[
h_j-2ck_j>-1
\]
for every \(j\) with \(k_j>0\). Thus it converges globally iff \(c\) lies below every relevant chart threshold, giving
\[
\lambda=\min_U\lambda_U.
\]
One divergent local piece forces global divergence; all pieces convergent give global convergence by a finite localization.

The pole order is
\[
\theta=\max_{\substack{u\in g^{-1}(w^\ast)\\\lambda_u=\lambda}}
\#\{j:(h_j+1)/(2k_j)=\lambda\}.
\]
It is a maximum, not a sum: adding localized zeta integrals preserves the largest pole order, and positivity prevents cancellation.

The boxed minimum must exclude \(k_j=0\), or declare its ratio \(+\infty\). The pure Jacobian claim is consistent with \(h_j=M_j-1\ge0\); the PDF’s “non-positive integers” wording is a sign typo if read literally.

CONFIDENCE: high — this follows directly from one-variable monomial integrability and localization.

3. Page 6 cites Hironaka for the proper resolution and then asserts the change-of-variables identity and boxed min/max rule as standard theory; it does not prove the cover, partition-of-unity localization, or pole-order aggregation. Pages 14–22 do provide the local recursive algebra: centres, representative pivot charts, monomial/Jacobian bookkeeping, terminal ideal, and candidate ratios. Pages 22–26 then minimize those candidates and count the binding coordinates, conditional on the recursion being an exhaustive resolution.

What is not established is that the representative Case 1/Case 2 calculations generate every necessary pivot chart, that every branch terminates, and that the resulting terminal domains constitute a proper covering atlas. In particular, a displayed normalization such as a chosen \(d_{J+1,J+1}\)-pivot implicitly stands for all symmetric matrix-entry pivots, but the relabelling and coverage argument is not written.

CONFIDENCE: high — the text jumps from representative “consider instances” calculations to global candidates without an atlas or localization lemma.

SHARPEST GAP: constructing and proving coverage/termination of the exhaustive terminal-chart atlas from the representative recursive pivot cases.