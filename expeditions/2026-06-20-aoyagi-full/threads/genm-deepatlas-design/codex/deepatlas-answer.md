The product-layer crux has a clean solution: normalize the pivot columns before completing them. This gives a unitriangular completion and an identically unit Jacobian. The resulting construction is a finite stratified atlas of \(S_s\), but it is not yet an analytic resolution of the pulled-back loss near intersections of rank strata.

## Q1. Explicit chart family and finite index

[FACT] At a recursive node, let the current effective last layer be

\[
M\in \mathbb R^{n\times d}.
\]

Fix \(r\le \min(n,d)\), row and column subsets \(I,J\) of cardinality \(r\), and reorder them first. Write

\[
M=
\begin{pmatrix}
\Delta & U\\
V & W
\end{pmatrix},
\qquad
E=W-V\Delta^{-1}U,
\]

where \(\Delta\in \mathrm{GL}_r(\mathbb R)\) and

\[
E\in\mathbb R^{(n-r)\times(d-r)}.
\]

The map

\[
(\Delta,U,V,E)\longmapsto
\begin{pmatrix}
\Delta&U\\
V&V\Delta^{-1}U+E
\end{pmatrix}
\]

has absolute Jacobian \(1\). Moreover,

\[
\operatorname{rank}M=r+\operatorname{rank}E.
\]

Thus the exact-rank-\(r\) core of this chart is \(E=0\), of codimension

\[
(n-r)(d-r).
\]

[FACT] The correct finite index set is recursive:

\[
\mathcal I_p(v_0,\ldots,v_p;s)
=
\bigsqcup_{r=0}^{\min(v_{p-1},v_p)}
\binom{[v_{p-1}]}r
\times
\binom{[v_p]}r
\times
\begin{cases}
\{\ast\},&r\le s,\\[2mm]
\mathcal I_{p-1}(v_0,\ldots,v_{p-2},r;s),&r>s.
\end{cases}
\]

At a nonterminal node, the shorter chain has widths

\[
(v_0,\ldots,v_{p-2},r).
\]

No choice of complement beyond the pivot row complement is needed.

[FACT] A path has effective ranks \(r_j\) and effective output widths

\[
w_p=v_p,\qquad w_{j+1}=r_{j+1}.
\]

Its core has normal blocks

\[
E_j\in
\mathbb R^{(v_j-r_j)\times(w_{j+1}-r_j)}
\]

and hence codimension

\[
C_{\text{path}}
=
\sum_j (v_j-r_j)(w_{j+1}-r_j).
\]

Minimizing these sums gives the stated CR recursion.

[FACT] All rank paths and pivots cover \(S_s\) exactly, not merely generically: take the actual rank of the current effective layer, choose a nonzero maximal minor, and recurse when that rank exceeds \(s\).

[INFERENCE] The clean atlas is therefore the full CR recursion tree, not merely the minimizing branches. Minimizers suffice to compute codimension, but lower-rank branches cannot be discarded in an integrability argument merely because their centers have measure zero.

A related correction: size-\(s\) pivot charts cover the rank-exactly-\(s\) part of \(\{\operatorname{rank}\le s\}\), not its lower-rank points. Exact coverage requires all ranks \(0,\ldots,s\).

## Q2. Exact product-layer change of variables

Let

\[
M=L_{p-1}\in\mathbb R^{n\times d},
\qquad
L=L_{p-2}\in\mathbb R^{m\times n},
\]

where \(n=v_{p-1}\), \(d=v_p\), and \(m=v_{p-2}\). Work after the fixed pivot row and column permutations; these contribute only signs to the Jacobian.

### The proposed raw-pivot completion

[FACT] Let

\[
A=\begin{pmatrix}\Delta\\V\end{pmatrix}\in\mathbb R^{n\times r},
\qquad
K=\begin{pmatrix}0\\I_{n-r}\end{pmatrix},
\]

and complete \(A\) by

\[
G_A=[A\mid K]
=
\begin{pmatrix}
\Delta&0\\
V&I_{n-r}
\end{pmatrix}.
\]

Then

\[
\det G_A=\det\Delta
\]

and

\[
M
=
G_A
\begin{pmatrix}
I_r&\Delta^{-1}U\\
0&E
\end{pmatrix}.
\]

Define

\[
LG_A=(H_A,F),
\qquad
H_A=LA\in\mathbb R^{m\times r},
\quad
F=LK\in\mathbb R^{m\times(n-r)}.
\]

Consequently,

\[
LM=
\bigl(H_A,\ H_A\Delta^{-1}U+FE\bigr).
\]

On \(E=0\),

\[
LM=H_A[I_r,\Delta^{-1}U],
\]

and the right factor has full row rank. Hence, for every preceding head \(B\),

\[
\operatorname{rank}(BLM)=\operatorname{rank}(BH_A).
\]

[FACT] For fixed chart data, \(L\mapsto LG_A\) has Jacobian

\[
|\det G_A|^m=|\det\Delta|^m.
\]

Thus the inverse coordinate map

\[
(\Delta,U,V,E,H_A,F)\longmapsto(M,L)
\]

has absolute Jacobian

\[
|\det\Delta|^{-m}.
\]

This remains the joint Jacobian even though \(G_A\) depends on \((\Delta,V)\), because the full derivative is block triangular.

The proposed “constant chart-dependent” Jacobian is therefore fiberwise constant in \(L\), but not constant over the whole chart.

### Cleaner unit-Jacobian normalization

[FACT] Normalize the pivot columns:

\[
A_0=A\Delta^{-1}
=
\begin{pmatrix}
I_r\\
V\Delta^{-1}
\end{pmatrix},
\]

and take

\[
G_0=[A_0\mid K]
=
\begin{pmatrix}
I_r&0\\
V\Delta^{-1}&I_{n-r}
\end{pmatrix}.
\]

Then

\[
\det G_0=1,
\qquad
M=
G_0
\begin{pmatrix}
\Delta&U\\
0&E
\end{pmatrix}.
\]

Set

\[
LG_0=(H,F),
\qquad H=LA\Delta^{-1}.
\]

Now

\[
LM=(H\Delta,\ HU+FE).
\]

On \(E=0\),

\[
LM=H[\Delta,U],
\]

and \([\Delta,U]\) is full row rank. Therefore

\[
\operatorname{rank}(BLM)=\operatorname{rank}(BH).
\]

[FACT] The joint coordinate map

\[
(\Delta,U,V,E,H,F)\longleftrightarrow(M,L)
\]

has absolute Jacobian identically \(1\): the Schur map has Jacobian \(1\), \(G_0\) has determinant \(1\), and the cross-derivatives again form off-diagonal blocks.

[INFERENCE] This normalized completion is the cleanest Lean-facing formulation. If having exactly \(LA\) as the reduced layer is important, use the raw version and accept the monomial \(|\det\Delta|^{-m}\). For a unit-Jacobian atlas, use \(LA\Delta^{-1}\).

## Q3. Induction on chain length and the determinant charge

[FACT] The natural inductive statement is:

> For every width sequence \((v_0,\ldots,v_p)\) and target \(s\), there is a finite family of rational smooth charts with unit absolute Jacobian, normal blocks \(E_j\), and cores \(\{E_j=0\}\), whose core images cover \(S_s\). Each core has codimension equal to the sum of its Schur-block dimensions.

The base \(p=1\) consists of the single-matrix Schur charts for all exact ranks \(r\le s\).

For the inductive step, choose \(r,I,J\) for \(L_{p-1}\).

- If \(r\le s\), impose \(E=0\) and stop; the preceding layers are free.
- If \(r>s\), use the unit-Jacobian transformation above. The new free last layer is \(H\in\mathbb R^{v_{p-2}\times r}\), while \(F\) is a spectator. Apply the shorter-chain atlas to
  \[
  (L_0,\ldots,L_{p-3},H)
  \]
  with widths \((v_0,\ldots,v_{p-2},r)\).

This proves the geometric atlas by bounded induction.

[FACT] The determinant charge does not decouple algebraically. On \(E=0\), write

\[
Z=Z_{\mathrm{red}}D,
\qquad D=[\Delta,U]
\]

in normalized coordinates. If \(N=A_{\mathrm{cor}}Z_{\mathrm{red}}\), then

\[
Q_bQ_b^{T}
=
N(DD^{T})N^{T}.
\]

Here \(DD^T\) is positive definite. On any compact subchart on which

\[
\lambda I\le DD^T\le \Lambda I,
\]

and \(Q_b\) has \(b\) rows,

\[
\lambda^b\det(NN^T)
\le
\det(Q_bQ_b^T)
\le
\Lambda^b\det(NN^T).
\]

Thus the charge has the same local corank exponent as the reduced charge, up to a bounded positive factor.

[FACT] Off the core,

\[
Z
=
Z_{\mathrm{head}}(H\Delta,\ HU+FE),
\]

so the \(FE\) term enters the charge as well as the loss.

[INFERENCE] The purely geometric induction may ignore the charge. An induction proving the integral exponent must thread it, preferably by making the shorter-chain assertion uniform under an arbitrary positive-definite right metric \(R=DD^T\). Treating it as a harmless scalar weight is unjustified near its own corank locus.

## Q4. Non-comparable scales and index completeness

[FACT] If “sum of squared-scale terms” means a genuine uniform estimate

\[
c\sum_j\|E_j\|^2
\le
\mathrm{loss}
\le
C\sum_j\|E_j\|^2,
\]

then non-comparable scales cannot lower the exponent. Let \(c_j=\dim E_j\) and take

\[
E_j\sim t^{\alpha_j},\qquad \alpha_j>0.
\]

Normalize \(\min_j\alpha_j=1\). The loss has order \(t^2\), while the volume cost is

\[
t^{\sum_j c_j\alpha_j}.
\]

Since

\[
\sum_jc_j\alpha_j\ge\sum_jc_j=C_{\mathrm{path}},
\]

the minimum is attained by comparable scaling. The radial threshold is \(q<C_{\mathrm{path}}/2\).

[FACT] This quadratic comparability does not follow from the Schur atlas. Already for widths \((2,2,2)\), \(s=0\), and the \(r=1\) chart,

\[
Z=(H\Delta,\ HU+FE),
\]

with \(H,F\in\mathbb R^{2\times1}\) and \(E\in\mathbb R\). Since \(\Delta\ne0\),

\[
Z=0
\iff
H=0\quad\text{and}\quad FE=0.
\]

Thus the zero locus in this one chart is the union

\[
\{H=0,E=0\}
\;\cup\;
\{H=0,F=0\},
\]

not only the first core. Near the intersection, the loss has the model

\[
\|H\|^2+\|FE\|^2,
\]

rather than \(\|H\|^2+|E|^2\).

In this example the weighted calculation is still safe: if \(H,F,E\) have weights \(a,b,c\), the volume cost is \(2a+2b+c\) and the loss order is \(2\min(a,b+c)\). Normalizing \(\min(a,b+c)=1\) gives minimum cost \(3=\mathrm{CR}(2,2,2;0)\). But this is a separate analytic calculation, not a consequence of codimension.

[FACT] As posed, the loss is not specified sufficiently to conclude that CR is always the infimum. The zero set and its codimension alone are insufficient. For example,

\[
\ell(x,y)=x^2+y^4
\]

has zero set of codimension \(2\), but the scaling \(x\sim t^2,\ y\sim t\) gives volume exponent \(3\) against loss order \(4\), hence threshold \(3/4<2/2\).

[INFERENCE] For the intended composite loss, non-comparable scaling likely corresponds to moving toward another rank path, as the \(FE\) example illustrates. However, proving that no fractional weighting beats all discrete CR paths requires an analytic valuation or sector-decomposition lemma. It is not established by the finite pivot index alone.

[FACT] The rank/pivot indices are set-theoretically complete: every point of \(S_s\) lies on a core, and the associated open chart domains form a finite open neighborhood of \(S_s\). This does not imply analytic completeness. Singular centers of measure zero can control local integrability, so “up to a null set” is not enough unless the nearby sectors are also controlled.

What would settle the multi-scale question is a one-peel analytic recursion proving directly, from

\[
Z=Z_{\mathrm{head}}(H\Delta,\ HU+FE),
\]

that the local zeta exponent satisfies the same minimization over \(r\) as CR, uniformly as \(F\) loses rank and pivot minors approach lower-rank charts.

## Q5. Lean feasibility

[INFERENCE] The algebraic telescoping is bounded induction, not new resolution machinery. The additional ingredients are:

- the normalized unitriangular completion;
- a recursive finite path/pivot index;
- the joint block-triangular Jacobian calculation;
- spectator-coordinate bookkeeping;
- the sum-of-block-dimensions/CR arithmetic bridge.

This should remain of the same broad order as the existing single-block atlas, although dependent dimensions and pivot reindexing will be the main Lean engineering cost.

[INFERENCE] The analytic claim is substantially larger. One must control overlapping branches such as \(H=0,\ FE=0\), pivot-collapse seams, non-comparable sectors, and the singular determinant charge. A generic finite-cover gluing lemma cannot replace that analysis.

[SPECULATION] If the one-peel analytic recursion is available as a theorem, the multilayer part should add roughly another atlas-sized tranche of formalisation. Without it, the project has crossed from “iterate Schur CoV” into a genuine stratified-integration or resolution argument, whose size is not responsibly predictable from the existing 690 LoC.

The single most likely wall is the assumption that branchwise Schur cores already monomialize the loss near intersections of rank strata. The one de-risking check is to prove the full one-peel local-zeta recursion—including the \(FE\) seam and determinant charge—before formalising the recursive atlas.