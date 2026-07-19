Interpretation: \(R>0\), and “cover” refers to actual ambient-coordinate images, not merely profile classes.

1. **Full pivot family: yes. Proper subfamily: generally no.** [PROVED]

For pivot \(i\), its image is
\[
C_i=\{x\in[-R,R]^d:\ |x_k|\le |x_i|\ \forall k\}.
\]
Indeed, \(x_i=u_i\) and \(u_k=x_k/x_i\). Every nonzero \(x\) belongs to \(C_i\) for an index attaining \(\max_k|x_k|\); zero belongs to every chart. Hence
\[
\bigcup_{i=1}^d C_i=[-R,R]^d
\]
exactly, and every image is bounded by \(R\).

For a proper index set \(I\), choose \(j\notin I\). Then
\[
x=\varepsilon e_j,\qquad 0<\varepsilon\le R,
\]
belongs to no \(C_i\), \(i\in I\). Thus the subfamily contains no neighbourhood of zero.

Consequently, the two representative charts fail whenever \(d_{\rm center}>2\). For Case 1 this means
\[
J_1(M^{S+1}-J)>1.
\]
If \(d_{\rm center}=2\), the two charts happen to be the full family.

2. **A gauge preserves the transformed cover, but not automatically the same fixed box or target.** [PROVED]/[COMPUTED]

For any family \(f_i\),
\[
\bigcup_i(\psi\circ f_i)(D_i)
=\psi\!\left(\bigcup_i f_i(D_i)\right).
\]
Thus a polynomial-bijective triangular \(\psi\) creates no internal gap: a neighbourhood of \(T\) becomes a neighbourhood of \(\psi(T)\).

However, covering the unchanged target \(T\) requires target/region compatibility—e.g. \(\psi(T)=T\) and appropriate bounds. Bijectivity and \(\det D\psi=1\) alone do not preserve the cube. For example, with \(R=1\),
\[
\psi(x,y,z)=(x,y,z-xy),
\]
the point \(p=(3/4,3/4,3/4)\) is not in \(\psi([-1,1]^3)\), since
\[
\psi^{-1}(p)=(3/4,3/4,21/16).
\]
Whether this affects the stated product-zero locus cannot be decided without its transformation law under \(\psi\).

3. **Yes, provided the covers are compatible node-by-node.** [PROVED]

If children \(b_i:X_i\to X_v\) satisfy
\[
X_v\subseteq\bigcup_i b_i(X_i),
\]
and descendants cover every \(X_i\), then for the accumulated parent map \(F_v\),
\[
F_v(X_v)\subseteq\bigcup_i F_v(b_i(X_i)),
\]
and induction gives the leaf cover. Injectivity is unnecessary. Folding cannot repair a failed local cover, however: descendants remain inside their parent-chart images.

4. **Stranding alone does not uncover points.** [PROVED]

A \(t̃>0\) leaf is still a leaf chart. If stranded strata remain in such leaves, their points remain covered; only the claim that every point reaches a \(t̃=0\) monomialized profile fails. A gap arises only if \(t̃>0\) leaves are discarded, or if representative-chart omission already destroyed geometric coverage.

5. **Bottom line.**

The load-bearing precondition is:

> At every internal node, the emitted **geometric** children—not merely their profile classes—must cover the node’s entire relevant coordinate neighbourhood.

The full \(d_{\rm center}\)-pivot family satisfies this. Two representatives do not suffice when \(d_{\rm center}>2\): every omitted pivot \(j\) leaves the directions \(\varepsilon e_j\) uncovered arbitrarily close to the center. Profile equivalence does not identify these actual image points. The failure occurs immediately in the parent-to-children cover step and persists through all descendants, unless the missing charts are restored via explicit symmetry-translated copies.