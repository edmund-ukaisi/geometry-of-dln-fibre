## Verdict: [DEPENDS]

The unweighted seam hypergraph is not invariant under the resolution atlas. The same DLN germ can have:

- a balanced path in atomic Schur coordinates; and
- a genuine triangle after projectivizing a transverse block.

The latter chart carries a nontrivial Jacobian weight that restores the RLCT. Thus neither “always balanced” nor the unweighted formula \((q+\tau^*)/2\) is atlas-independent.

Two corrections first:

- [FACT] A triangle has \(\tau-\tau^*=2-\frac32=\frac12\), but its RLCT deficit is
  \[
  \frac{\tau-\tau^*}{2}=\frac14,
  \]
  not \(\frac12\).
- [FACT] “balanced hypergraph” is stronger than \(\tau=\tau^*\) for one unit-weight instance. Balancedness means no odd Berge submatrix and gives equality for all relevant weights/subhypergraphs.

### Q1: depth order does not imply balancedness

[FACT] Ordering vertices by depth and requiring every coupling to go from shallower to deeper imposes no combinatorial restriction: for every edge \(S\), designate \(\min S\) as current and the remaining vertices as deeper.

For \(a<b<c\), the triangle is oriented
\[
a\to b,\qquad a\to c,\qquad b\to c,
\]
which is a DAG.

Therefore the stated recursion permits every ordered clutter unless one additionally proves a consecutive-support theorem. In particular:

- it is not automatically interval: \(\{a,c\}\) skips \(b\);
- it is not laminar: even \(\{a,b\}\) and \(\{b,c\}\) cross;
- type-\(A\) acyclicity alone does not imply balancedness.

### Q2: exact smallest triangle ambiguity

Take four \(2\times2\) factors, with the fourth initially \(I_2\):
\[
L_3=A,\quad L_2=B,\quad L_1=C,\quad L_0=I_2,
\]
at
\[
A_0=\begin{pmatrix}0&0\\0&1\end{pmatrix},\quad
B_0=\begin{pmatrix}0&1\\0&0\end{pmatrix},\quad
C_0=\begin{pmatrix}1&0\\0&0\end{pmatrix}.
\]

Because \(A_{22},B_{12},C_{11}\) are units, Schur/Gaussian coordinates reduce the germ, up to bounded invertible left/right factors, to
\[
A=\operatorname{diag}(x,1),\quad
B=\begin{pmatrix}s&\beta\\u&t\end{pmatrix},\quad
C=\operatorname{diag}(1,z),
\qquad \beta\ne0.
\]
Hence
\[
ABC=
\begin{pmatrix}
xs&x\beta z\\
u&tz
\end{pmatrix},
\]
and
\[
K\asymp u^2+(xs)^2+(xz)^2+(tz)^2.
\]

[FACT] The atomic seam incidence is the path
\[
s-x-z-t,
\]
so
\[
\tau=\tau^*=2.
\]

The sandwich direction is exactly \(u\): indeed the full differential has image
\[
\operatorname{Im}D(ABC)=\mathbf R E_{21}.
\]
Thus \(u\) splits off as Morse, while \(s,t\) survive independently.

Now blow up the residual middle plane:
\[
s=y,\qquad t=y\theta,
\]
on a chart where \(\theta\) is a unit. Then
\[
K\asymp u^2+(xy)^2+(xz)^2+(yz)^2.
\]
This is the exact triangle
\[
\{x,y\},\quad\{x,z\},\quad\{y,z\},
\]
with
\[
\tau=2,\qquad \tau^*=\frac32.
\]

No Morse direction kills it: its three coefficients lie in \(E_{11},E_{12},E_{22}\), complementary to the linear image \(E_{21}\).

However,
\[
\left|\frac{\partial(s,t)}{\partial(y,\theta)}\right|=|y|.
\]
The triangle-producing map does not have nonvanishing Jacobian. Its correct fractional-cover objective has weights
\[
w_x=1,\qquad w_y=2,\qquad w_z=1.
\]
Consequently
\[
\min\{a+2b+c:a+b,a+c,b+c\ge1\}=2,
\]
since \((a+b)+(b+c)\ge2\). Thus the actual RLCT is
\[
\frac{1+2}{2}=\frac32,
\]
the same as for the original path—not \(\frac54\).

Width \(2\) is minimal: width \(1\) has only one output component, so three pair terms occur inside one squared polynomial rather than as three independent Morse-normal squares.

The appended identity is absorbable, so this is not a genuinely new fourth peel. It proves that the requested answer depends on whether a radialized block is one vertex or its atomic Schur coordinates are separate. The supplied description does not specify that choice.

### Q3: exact worst unweighted gap

Let \(n=|V(H)|\). Under only the depth-order condition, arbitrary hypergraphs are possible combinatorially.

[FACT] The exact largest possible additive gap is
\[
\boxed{\Delta_n
=n+1-\min_{2\le k\le n}\left(k+\frac nk\right)}.
\]
It is attained by the complete \(k\)-uniform hypergraph:
\[
\tau=n-k+1,\qquad \tau^*=\frac nk.
\]
The maximizing \(k\) is one of \(\lfloor\sqrt n\rfloor,\lceil\sqrt n\rceil\), so
\[
\Delta_n=n+1-2\sqrt n+O(1).
\]

Proof: if \(\alpha\) is the largest edge-free vertex set, then \(\tau=n-\alpha\). The \(\alpha+1\) smallest fractional-cover coordinates have total at most \((\alpha+1)\tau^*/n\), but must contain an edge, hence total at least \(1\). Therefore \(\tau^*\ge n/(\alpha+1)\).

If DLN incidence is proved to be graph-only, the worst gap instead is
\[
\frac n2-1,
\]
attained by \(K_n\).

Writing
\[
M=\mathrm{minAdm}-ab,\qquad
C_{\rm chart}=q+\tau,\qquad
s=C_{\rm chart}-M,
\]
the desired gate is exactly equivalent to
\[
\tau-\tau^*\le s.
\]
No such slack bound follows from the supplied recursion or from “codimension grows quadratically.” The relation between \(n\), block discrepancies and \(s\) is missing.

Moreover, the \(2\times2\) example shows that the natural compensation may be a Jacobian/discrepancy weight rather than codimension slack.

### Q4 and the native closer

The equioriented \(A_n\) quiver has no directed cycles, but seam incidence cycles are undirected overlap cycles. A transitive orientation of \(K_3\) is already an acyclic quiver orientation, so quiver acyclicity does not transfer to balancedness.

The right native closer is therefore:

\[
\boxed{\text{(b), but as a weighted discrepancy/Jacobian inequality, not merely unweighted gap}\le\text{slack}.}
\]

Route (a) does not follow from depth order, and route (c) fails after radializing residual kernel blocks. If the full telescoping atlas supplies and controls those discrepancy weights, no Aoyagi input is needed. If it insists on the unweighted formula while treating the radial charge as a bounded factor, the native argument is incomplete and the residual lower bound genuinely still needs Aoyagi or an equivalent theorem.