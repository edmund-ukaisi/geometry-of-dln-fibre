**Verdict:** (A) and (B) hold for a correctly built chart, but “correctly built” means blowing up the whole active normal coordinate set, not necessarily the final leaf. A live-leaf-only implementation can undercount or become non-square when `T_{L-1}=0`.

For a fixed admissible `T`, set
\[
d_j=T_{j-1}-T_j,\qquad e_j=M_j-T_j.
\]
In adapted coordinates, the effective layer block has a Schur-complement normal block
\[
X_j\in \operatorname{Mat}_{d_j\times e_j}.
\]
The rank condition at that layer is exactly `X_j=0`, and
\[
|X_j|=d_j e_j=(T_{j-1}-T_j)(M_j-T_j).
\]
Thus the active normal coordinate set is
\[
X=\bigsqcup_j X_j,\qquad |X|=Mval(T).
\]
For an achiever `T*`, this cardinality is `minAdm(M)`. The center itself has codimension `minAdm`, not dimension `minAdm`; its dimension is `flatDim - minAdm`.

The angular coordinates are precisely
\[
\{ \text{active normal coordinates} \}\setminus \{\text{one chosen pivot}\}.
\]
In one projective blow-up chart,
\[
x_{\mathrm{pivot}}=u,\qquad x_\alpha=u h_\alpha\quad(\alpha\ne\mathrm{pivot}),
\]
so
\[
\#h=|X|-1=\minAdm(M)-1.
\]
That is the clean reason for the single “minus one”: one active center coordinate has become the radial pivot.

For (B), once the cascade gives an honest adapted coordinate system `(z,x)` with unit Jacobian, squareness and the determinant exponent are automatic:
\[
\#z+1+\#h=(flatDim-\minAdm)+1+(\minAdm-1)=flatDim,
\]
and the blow-up Jacobian in the active variables is
\[
\det \frac{\partial x}{\partial(u,h)}=\pm u^{\minAdm-1}.
\]
Unipotent shear blocks and Schur-complement charts contribute only a generically nonzero unit. Multiple interior drops, mixed widths, or several active blocks do not introduce another obstruction; they just enlarge the disjoint union of active blocks. A degenerate diagonal block would mean the proposed parametrization failed to be an adapted coordinate chart.

The leaf issue is real only for implementation. If `rho=T_{L-1}>0`, the final active block is
\[
X_L\in \operatorname{Mat}_{\rho\times M_L}.
\]
If `rho=0`, that block is empty, so the angular coordinates must live in earlier active blocks.

Example `M=(2,2,4)`: the unique achiever is `T=(0,0)`, `minAdm=4`, and the active center is all of `A_0`. A correct chart is
\[
A_0=u\begin{pmatrix}1&h_1\\ h_2&h_3\end{pmatrix},\qquad A_1\text{ arbitrary}.
\]
Then `#angular=3=minAdm-1` and the parameter Jacobian has factor `u^3`. A final-leaf chart has no place to put these coordinates.

Example `M=(2,2,2,4)`: the achiever is `T=(1,0,0)`, with active counts `1+2+0=3`. One local chart is
\[
A_0=\begin{pmatrix}p&pb\\ q&qb+u\end{pmatrix},\quad
A_1=\begin{pmatrix}uh_1-bs_1&uh_2-bs_2\\ s_1&s_2\end{pmatrix},\quad
A_2\text{ arbitrary}.
\]
Here `p≠0`, `#angular=2`, `flatDim=16`, and the Jacobian is generically `±p u^2`. The leaf is empty, but the chart is square and has the correct exponent.

So the invariant is: **angular variables are active normal coordinates minus one pivot**, wherever those active coordinates occur. Leaf versus interior is cosmetic for the theorem, but not cosmetic for a concrete parametrization.