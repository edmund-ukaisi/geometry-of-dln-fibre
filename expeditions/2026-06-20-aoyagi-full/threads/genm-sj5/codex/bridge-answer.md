Verdict: the uniform reduction to  
\[
I(p)=\int \det(Q_bQ_b^\top)^{-p/2}\,dA'
\]
is **invalid**. It fails generically at a narrow bottleneck. On each fixed-rank stratum there is an exact pseudo-determinant identity, but its residual contains a shrinking image domain and usually a nonconstant kernel-slice density. Those factors cannot be discarded.

Assume \(c'>0\) and use \(0^{-c'}=+\infty\).

## Q1. Full row rank

Let \(Q=Q_b\) have rank \(b\le n\), and choose an SVD
\[
Q=U D V_b^\top,\qquad
D=\operatorname{diag}(\sigma_1,\ldots,\sigma_b),\quad \sigma_i>0,
\]
extending \(V_b\) to \(V=(V_b,V_\perp)\in O(n)\). Write
\[
S_b=SV_b,\qquad S_\perp=SV_\perp,\qquad
a=w+\|S_\perp\|_F^2.
\]

Set \(Z=\Gamma U\). Orthogonal invariance gives
\[
\|S+\Gamma Q\|_F^2
=\|S_\perp\|_F^2+\|S_b+ZD\|_F^2.
\]

If \(\mathcal B\) is the original bounded \(\Gamma\)-box and
\[
\Omega=S_b+(\mathcal B U)D,
\]
then \(T=S_b+ZD\) has Jacobian
\[
d\Gamma=dZ
=(\sigma_1\cdots\sigma_b)^{-p}dT
=\det(QQ^\top)^{-p/2}dT.
\]

Therefore:

\[
\boxed{
J(w,S,Q)
=
\det(QQ^\top)^{-p/2}
\underbrace{\int_\Omega
(a+\|T\|_F^2)^{-c'}\,dT}_{R(w,S,Q)}.
}
\]

This proves the exponent \(-p/2\). Crucially, \(R\) depends on \(Q\) through the rotated, scaled, shifted image box \(\Omega\).

The familiar whole-space Morse value
\[
\pi^{pb/2}\frac{\Gamma(c'-pb/2)}{\Gamma(c')}
a^{pb/2-c'}
\]
arises only after replacing \(\Omega\) by \(\mathbb R^{p\times b}\), requiring \(a>0\) and \(c'>pb/2\). That replacement is not exact for the bounded box and can destroy finiteness.

If \(a=0\), the bounded residual is finite unless \(0\in\overline\Omega\); when \(0\in\overline\Omega\),
\[
J<\infty\iff c'<\frac{pb}{2}.
\]

For \((p,b,n)=(2,2,4)\),
\[
\boxed{
J=(\sigma_1\sigma_2)^{-2}
\int_{\Omega\subset\mathbb R^4}
\bigl(w+\|S_\perp\|_F^2+\|T\|^2\bigr)^{-c'}\,dT.
}
\]

## Q2. Rank-deficient \(Q\)

Let \(\operatorname{rank}Q=r<b\), with reduced SVD
\[
Q=U_rD V_r^\top,\qquad D=\operatorname{diag}(\sigma_1,\ldots,\sigma_r).
\]
Extend \(U_r\) to \(U=(U_r,U_0)\in O(b)\), and write
\[
\Gamma U=[Z\ K],\qquad
S_r=SV_r,\qquad S_\perp=SV_\perp.
\]

Define the rotated box
\[
\widetilde{\mathcal B}
=\{[Z\ K]:[Z\ K]U^\top\in\mathcal B\}
\]
and its kernel-slice volume
\[
m_{\mathcal B}(Z)
=
\lambda_{p(b-r)}
\{K:[Z\ K]\in\widetilde{\mathcal B}\}.
\]

Then \(m_{\mathcal B}\) is bounded and compactly supported, and the exact identity is

\[
\boxed{
J=
\det\nolimits^+(QQ^\top)^{-p/2}
\int_{\mathbb R^{p\times r}}
m_{\mathcal B}\!\left((T-S_r)D^{-1}\right)
\bigl(w+\|S_\perp\|_F^2+\|T\|_F^2\bigr)^{-c'}\,dT,
}
\]
where
\[
\det\nolimits^+(QQ^\top)=\prod_{i=1}^r\sigma_i^2.
\]

### Q2(a): Is bounded-box \(J\) finite?

Not automatically.

- If \(w+\|S_\perp\|^2>0\), then for every \(c'>0\),
  \[
  \boxed{J\le |\mathcal B|
  \bigl(w+\|S_\perp\|^2\bigr)^{-c'}<\infty.}
  \]

- If that core vanishes and the affine zero is not approachable from the box, \(J\) is finite.

- In all cases with \(r>0\),
  \[
  c'<\frac{pr}{2}
  \quad\Longrightarrow\quad J<\infty.
  \]

- If the affine zero set meets the interior of the box, this is sharp:
  \[
  J<\infty\iff c'<\frac{pr}{2}.
  \]

At boundary-only intersections, the kernel slices can shrink and improve the threshold. Hence rank alone does not determine the exact boundary case.

Also, the “kernel-volume factor” is generally a function \(m_{\mathcal B}(Z)\), not one constant. For example, rotating \([-1,1]^2\) through \(45^\circ\) gives
\[
m(z)=2(\sqrt2-|z|),\qquad |z|\le\sqrt2.
\]

### Q2(b): Does the full determinant reduction survive?

**NO.**

When \(r<b\),
\[
\det(QQ^\top)=0,
\]
so its inverse is \(+\infty\). If narrow widths force \(r<b\) generically, then \(I(p)=+\infty\) almost everywhere.

The pseudo-determinant is the correct fixed-rank Jacobian, but it cannot be separated from the residual. Indeed,
\[
\int m_{\mathcal B}\!\left((T-S_r)D^{-1}\right)dT
=
\det\nolimits^+(QQ^\top)^{p/2}|\mathcal B|.
\]
Thus the shrinking image and the pseudo-determinant can cancel exactly.

Even the standalone pseudo-determinant integral is therefore generally too crude and can diverge while \(J\) stays uniformly bounded.

### Narrow-width worked instance

Let
\[
Q=YA_2,\qquad Y\in\mathbb R^{2\times1},\quad A_2\in\mathbb R^{1\times4}.
\]
For nonzero factors,
\[
r=1,\qquad
\sigma=\|Y\|\,\|A_2\|,\qquad
\det(QQ^\top)=0,\qquad
\det\nolimits^+(QQ^\top)=\sigma^2.
\]

In the aligned case \(Y=e_1\), \(A_2=\sigma v^\top\), and \(\mathcal B=[-1,1]^{2\times2}\), put
\[
s=Sv,\qquad \rho^2=\|S(I-vv^\top)\|_F^2.
\]
Then exactly
\[
\boxed{
J=
4\sigma^{-2}
\int_{s+\sigma[-1,1]^2}
(w+\rho^2+\|T\|^2)^{-c'}\,dT.
}
\]

For \(S=w=0\), this is finite precisely when \(c'<1\). For \(w>0\),
\[
J\le16w^{-c'},
\qquad
J\longrightarrow16w^{-c'}\quad(\sigma\to0).
\]
The pseudo-determinant factor \(\sigma^{-2}\) is cancelled by the area \(O(\sigma^2)\) of the image box.

### Q2(c): Measure-level conclusion

From the displayed setup alone, finiteness below \(\minAdm/2\) is **not implied**.

For fixed \(x\):

- If \(w(x)>0\), then
  \[
  \int_{A'}J\,dA'
  \le |\mathcal B|w(x)^{-c'}\,|\text{\(A'\)-box}|<\infty,
  \]
  uniformly through every rank bottleneck.

- If \(w(x)=0\), \(\int_{A'}J\) may be infinite even when \(c'<\minAdm/2\).

The full joint \((x,A')\)-integral can nevertheless be finite because the pivot variables provide missing transverse dimensions. That requires a joint rank-stratified/bounded-box resolution; it is not proved by either the determinant or pseudo-determinant weight. If one invokes the known DLN RLCT equality, finiteness below \(\minAdm/2\) follows as a cited global fact, not from this reduction.

## Q3. Is \(w\) load-bearing?

**YES, in general. It cannot be dropped uniformly.**

For \(E=\|S+\Gamma Q\|^2\),
\[
(w+E)^{-c'}\le E^{-c'},
\qquad
(w+E)^{-c'}\le w^{-c'}.
\]
Both are valid pointwise upper bounds, but either may be nonintegrable.

The correct coupled majorant is
\[
\boxed{
(w+E)^{-c'}
\le
\min\{w^{-c'},E^{-c'}\}
=
\mathbf1_{\{E\le w\}}w^{-c'}
+\mathbf1_{\{w<E\}}E^{-c'}.
}
\]
Indeed it is equivalent to the original integrand up to \(2^{c'}\):
\[
2^{-c'}\min\{w^{-c'},E^{-c'}\}
\le(w+E)^{-c'}
\le\min\{w^{-c'},E^{-c'}\}.
\]

An exact rank-deficient model shows why both terms are needed. Take
\[
p=1,\quad b=2,\quad Q=(1,0)^\top,\quad
S=0,\quad w=x^2.
\]
Then
\[
\int_{[-1,1]^3}(x^2+\gamma_1^2)^{-c'}\,dx\,d\gamma_1\,d\gamma_2
<\infty
\iff c'<1.
\]
At \(c'=3/4\), the full integral is finite, but

- dropping \(w\) gives \(\int|\gamma_1|^{-3/2}=\infty\);
- dropping \(E\) gives \(\int|x|^{-3/2}=\infty\).

Thus:

- the bounded box rescues the infinite kernel-volume directions;
- \(w>0\) rescues zeros in the active \(pr\) transverse directions;
- \(E\) rescues loci where \(w=0\);
- the full \(w+E\), or an equivalent sector decomposition, must generally be retained.

In the concrete chart, \(P\) is invertible, so
\[
w=\|P\widetilde Q_p\|^2=0
\quad\Longrightarrow\quad
\widetilde Q_p=0
\quad\Longrightarrow\quad S=C\widetilde Q_p=0.
\]
Hence no shift remains to rescue the \(w=0\) locus. For example, in the narrow chain \((3,3,1,4)\), \(\minAdm=3\); at the \(t=1\) chart \(p=b=2,r=1\). For
\[
1\le c'<\frac32=\frac{\minAdm}{2},
\]
the \(w=0,S=0\) inner \(\Gamma\)-integral diverges, while every \(w>0\) makes it finite.

So the precise replacement is: keep the bounded image/fiber-density formula on fixed-rank strata and resolve \(w+\|S+\Gamma Q_b\|^2\) jointly. Do not replace it by a full Gram determinant integral.