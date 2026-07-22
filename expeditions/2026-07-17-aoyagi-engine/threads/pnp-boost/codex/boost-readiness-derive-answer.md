## VERDICT: needs-extra-structure

Property (P) holds for Aoyagi’s actual generator matrix, but it does not follow from (Q). The missing datum is the rowwise coupling between the residual block and the \(b\)-chain.

Let \(H=\prod_{s>S}C^{(s)}\). At \(J=0\),

\[
G_{ij}=b_i\sum_k D_{ik}H_{kj}.
\]

For the pending pivot \(u_p\),

\[
b_i=
\begin{cases}
\beta_i, & i\le J_1,\\
u_p\beta_i, & i>J_1,
\end{cases}
\]

where every \(\beta_i\) is independent of \(u_p\) and of the residual coordinates. Hence

\[
G_{ij}=
\begin{cases}
\displaystyle\sum_k D_{ik}\,(\beta_iH_{kj}),&i\le J_1,\\[2mm]
\displaystyle u_p\sum_k(\beta_iD_{ik}H_{kj}),&i>J_1.
\end{cases}
\]

In the first case \(D_{ik}\) is in the partial block; in the second case \(D_{ik}\) lies outside it. Thus every monomial has exactly one \(C_{\rm small}\)-factor.

### The \((2,2,2,2)\) instance

Write \(a=u_{1,1}\), \(v=u_{1,2}\),

\[
D=\begin{pmatrix}x_{11}&x_{12}\\x_{21}&x_{22}\end{pmatrix},
\qquad
Z=C^{(3)}=\begin{pmatrix}z_{11}&z_{12}\\z_{21}&z_{22}\end{pmatrix}.
\]

Then

\[
G=a
\begin{pmatrix}
x_{11}z_{11}+x_{12}z_{21} &
x_{11}z_{12}+x_{12}z_{22}\\
v(x_{21}z_{11}+x_{22}z_{21}) &
v(x_{21}z_{12}+x_{22}z_{22})
\end{pmatrix}.
\]

Here

\[
C_{\rm small}=\{v,x_{11},x_{12}\}.
\]

The first row gets its unique small factor from \(x_{1k}\); the second gets it from \(v\).

### The \((3,3,2,2)\) instance

Put \(w=u_{1,3}\) and \(L_{ij}=\sum_{k=1}^2x_{ik}z_{kj}\). Initially,

\[
G=a
\begin{pmatrix}
L_{11}&L_{12}\\
vL_{21}&vL_{22}\\
vwL_{31}&vwL_{32}
\end{pmatrix}.
\]

For the first boost, \(C_{\rm small}^{(v)}=\{v,x_{11},x_{12}\}\): row \(1\) uses a partial-block coordinate, while rows \(2,3\) use \(v\).

On the \(v\)-chart, \(x_{1k}=v\widehat x_{1k}\), so

\[
G\circ B_v
=av
\begin{pmatrix}
\widehat L_{11}&\widehat L_{12}\\
L_{21}&L_{22}\\
wL_{31}&wL_{32}
\end{pmatrix}.
\]

This is the node for the second boost. Now

\[
C_{\rm small}^{(w)}
=\{w,\widehat x_{11},\widehat x_{12},x_{21},x_{22}\}.
\]

Rows \(1,2\) get their factor from the partial block; row \(3\) gets it from \(w\).

## Why (Q) does not imply (P)

Take, in the \(2\times2\) example,

\[
R_{11}=x_{21}z_{11},\qquad R_{ij}=0\ \text{otherwise}.
\]

This satisfies (Q): it is \(C_{\rm full}\)-linear with continuous coefficient \(z_{11}\), and has degree at most one in each layer. But its nonzero monomial contains no factor from

\[
C_{\rm small}=\{v,x_{11},x_{12}\}.
\]

Conversely,

\[
R_{11}=v\,x_{11}z_{11}
\]

also satisfies (Q) and the per-layer grade, but contains two \(C_{\rm small}\)-factors. Thus (Q) controls neither missing factors on the complementary block nor extra pivot factors on the partial block.

The sharp additional condition, writing \(A=\) partial block and \(B=C_{\rm full}\setminus A\), is

\[
R_{ij}
=
\sum_{c\in A}\alpha_{ij,c}\,c
+
u_p\sum_{c\in B}\beta_{ij,c}\,c,
\]

where all \(\alpha_{ij,c}\) and \(\beta_{ij,c}\) ignore every coordinate in \(C_{\rm small}\). This is precisely the coefficient-level boost-readiness invariant.

For Aoyagi’s \(G\), it follows from three provenance facts:

1. \(G=\operatorname{diag}(b)DH\);
2. output row \(i\) uses only row \(i\) of \(D\);
3. the thresholded \(b\)-chain is \(u_p\)-free above the jump and exactly \(u_p\) times an \(u_p\)-free monomial below it.

These are genuine features of Aoyagi’s construction. The need to add them to Lean is caused by the lossy encoding (Q), which forgets the rowwise \(b\)-ledger. Continuity, grading, and coordinate-axis disjointness cannot recover divisibility by \(u_p\).

## Running-min shrink

The \(3\to2\) shrink changes nothing for the two \(S=2,J=0\) boosts: both occur before rollover, while the active residual is \(3\times2\). The second boost has \(J_1=2\), so its lower region is precisely row \(3\).

After rollover, only two active rows remain. The row-\(3\) jump witnessing the \(u_{1,3}\) boost is then absent; a post-shrink \(2\times2\) node should not be described as that same boost. Any later boost must be justified from the new active \(b\)-chain.