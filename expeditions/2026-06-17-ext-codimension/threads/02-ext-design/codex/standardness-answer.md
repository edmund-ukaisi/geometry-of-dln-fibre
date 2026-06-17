**A. Interval Resolution, Hom, Ext**

Convention: vertices are `0,1,...,N`, arrows `t -> t+1`, and `M_{ij}` has `k` on vertices `i <= t <= j`, identity maps inside the interval, zero elsewhere. Indecomposable projective:

\[
P_p=M_{p,N}.
\]

Set \(P_{N+1}=0\). Then the standard projective resolution is

\[
0\to P_{j+1}\to P_i\to M_{ij}\to 0,
\]

where \(P_{j+1}\hookrightarrow P_i\) is the tail inclusion. For \(j=N\), this says \(M_{iN}=P_i\).

For intervals \(M_{ij},M_{uv}\),

\[
\dim_k \operatorname{Hom}(M_{ij},M_{uv})
=
\mathbf 1[\,u\le i\le v\le j\,].
\]

Applying \(\operatorname{Hom}(-,M_{uv})\) to the resolution gives

\[
\dim_k \operatorname{Ext}^1(M_{ij},M_{uv})
=
\mathbf 1[\,i<u\le j+1\le v\,].
\]

Equivalently,

\[
\dim_k \operatorname{Ext}^1(M_{ij},M_{uv})
=
\mathbf 1[\,i+1\le u\le j+1\le v\,],
\]

with the convention that this is false when \(j=N\), since \(j+1=N+1\) is not a vertex.

**B. Euler/Ringel Form**

For dimension vectors \(a,b\in \mathbb Z^{N+1}\), with the same arrow convention,

\[
\langle a,b\rangle
=
\sum_{t=0}^N a_t b_t
-
\sum_{t=0}^{N-1} a_t b_{t+1}.
\]

For finite-dimensional \(kQ\)-modules \(X,Y\),

\[
\dim_k\operatorname{Hom}(X,Y)
-
\dim_k\operatorname{Ext}^1(X,Y)
=
\langle \dim X,\dim Y\rangle.
\]

This is the hereditary Euler identity. Since \(Q\) is finite and acyclic, \(kQ\) is finite-dimensional hereditary, so \(\operatorname{gl.dim} kQ\le 1\). The module category is Hom-finite for finite-dimensional modules.

**C. Voigt’s Lemma and Codimension**

Voigt’s lemma, in this setting:

\[
T_M\operatorname{Rep}(Q,d)/T_M(G_d\cdot M)
\cong
\operatorname{Ext}^1_{kQ}(M,M).
\]

For \(Q\) without relations, the precise chain is:

1. Fix vector spaces \(V_i\cong k^{d_i}\). Then

\[
\operatorname{Rep}(Q,d)=\prod_{t=0}^{N-1}\operatorname{Hom}_k(V_t,V_{t+1})
\]

is an affine space, hence smooth, with

\[
T_M\operatorname{Rep}(Q,d)=
C^1(M,M)=
\prod_{t=0}^{N-1}\operatorname{Hom}_k(M_t,M_{t+1}).
\]

2. The group

\[
G_d=\prod_{i=0}^N \operatorname{GL}(V_i)
\]

acts by

\[
(g\cdot M)_t=g_{t+1}M_tg_t^{-1}.
\]

3. Its tangent Lie algebra is

\[
C^0(M,M)=\prod_{i=0}^N\operatorname{End}_k(M_i).
\]

The differential of the action map at \(M\) is

\[
\delta_M:C^0(M,M)\to C^1(M,M),
\qquad
(\xi_i)_i\mapsto
(\xi_{t+1}M_t-M_t\xi_t)_t.
\]

4. The image

\[
B^1(M,M):=\operatorname{im}\delta_M
\]

is \(T_M(G_d\cdot M)\), the tangent space to the orbit.

5. Since \(kQ\) has no relations, all ambient \(1\)-cochains are cocycles:

\[
Z^1(M,M)=C^1(M,M).
\]

The standard deformation complex gives

\[
\operatorname{Ext}^1_{kQ}(M,M)
\cong
Z^1(M,M)/B^1(M,M)
=
C^1(M,M)/\operatorname{im}\delta_M.
\]

6. Therefore

\[
\operatorname{codim}_{\operatorname{Rep}(Q,d)}(G_d\cdot M)
=
\dim C^1(M,M)-\dim \operatorname{im}\delta_M
=
\dim \operatorname{Ext}^1(M,M).
\]

Subtleties: standard variety statements usually assume \(k\) algebraically closed. In arbitrary characteristic this remains clean here because \(\operatorname{Rep}(Q,d)\) is affine space and the stabiliser is \(\operatorname{Aut}_Q(M)\), an open subset of \(\operatorname{End}_Q(M)\), hence smooth. For bound quivers or singular module varieties, tangent-quotient dimension and geometric codimension can diverge; the equality above uses the smooth unbound quiver representation variety.

**D. Standardness and Tripwires**

This is the standard development.

- The interval modules and \(P_i/P_{j+1}\) resolution are the type-A/Gabriel classification in explicit equioriented form; this appears in standard quiver representation treatments such as Gabriel-Roiter, Assem-Simson-Skowronski, and Crawley-Boevey’s quiver notes.

- The bilinear form

\[
\langle a,b\rangle
=
\sum_i a_i b_i-\sum_{\alpha:i\to j}a_i b_j
\]

is the Ringel/Euler form; the identity

\[
\dim\operatorname{Hom}-\dim\operatorname{Ext}^1=\langle-,-\rangle
\]

is the standard hereditary identity, found in Ringel, Assem-Simson-Skowronski, Gabriel-Roiter, and Crawley-Boevey.

- Voigt’s lemma is the standard geometric representation theory statement identifying the normal space to the orbit with \(\operatorname{Ext}^1(M,M)\); it is routinely used in the geometry of module varieties and quiver representation varieties.

Formalisation tripwires:

- Left/right module convention flips \(P_i\) from a tail interval to a head interval.
- Hom is not mere interval containment; under this convention it is \(\mathbf 1[u\le i\le v\le j]\).
- Ext has the shifted endpoint \(j+1\): \(\mathbf 1[i<u\le j+1\le v]\).
- The Euler arrow term is \(a_t b_{t+1}\) for arrows \(t\to t+1\); reversing orientation changes the formula.
- Codimension equals Ext only because the quiver representation variety is smooth affine space.
- For algebraic geometry over non-algebraically closed \(k\), one should specify whether codimension is taken after base change to \(\bar k\).
- Mathlib API names should be checked directly; the mathematics above should not be read as claiming existing Mathlib declarations.