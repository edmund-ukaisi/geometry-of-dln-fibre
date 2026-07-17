The proposed absolute-\(\sigma_{\min}\) split is insufficient. The true integral converges in this corner for \(c'<3\), but the BOUNDED estimate converges only for \(c'<2\).

Let \(X=\widetilde Q=\varepsilon V\), \(r=Q_b\), and assume \(\|r\|\asymp1\), with \(P,V\) fixed invertible.

### 1. Exact scaling

Here
\[
L=\varepsilon^2\|PV\|_F^2+\|\varepsilon CV+\Gamma r\|_F^2.
\]

Set \(\Gamma=\varepsilon H\). Since \(\Gamma\in\mathbb R^{2\times1}\), \(d\Gamma=\varepsilon^2\,dH\). Therefore, for \(c'>1\),
\[
\int_C\int_\Gamma L^{-c'}\,d\Gamma\,dC
\asymp
\varepsilon^{\,2-2c'}.
\]
Indeed, the limiting \(H\)-integral is finite because \(H\) has dimension \(2\) and \(2c'>2\).

The variable \(X\) lies in \(\mathbb R^{2\times2}\cong\mathbb R^4\). Thus
\[
dX=\varepsilon^3\,d\varepsilon\,d\theta.
\]

| Estimate | Inner exponent | Net radial integrand | Converges iff |
|---|---:|---:|---:|
| True \(C,\Gamma\) integral | \(2-2c'\) | \(\varepsilon^{5-2c'}d\varepsilon\) | \(c'<3\) |
| BOUNDED estimate | \(-2c'\) | \(\varepsilon^{3-2c'}d\varepsilon\) | \(c'<2\) |

At \(c'=3\) and \(c'=2\), respectively, the divergences are logarithmic.

Equivalently, a dyadic shell \(\{\varepsilon\lesssim\|X\|\lesssim2\varepsilon\}\) has measure \(\asymp\varepsilon^4\). Its true contribution is \(\asymp\varepsilon^{6-2c'}\), while the BOUNDED contribution is \(\asymp\varepsilon^{4-2c'}\).

Hence for every \(c'\in(2,3)\):

- the true local integral converges;
- the BOUNDED-branch majorant diverges.

This exactly matches the fact that front-collapse supplies only \(c'<\frac12\minAdm(2,3,2)=2\).

### 2. The dispatched branch fails on a positive-measure cone

No: the BOUNDED estimate does not converge on this region for \(c'\in(2,3)\).

For fixed \(P,B_{12},Q_b\), the change
\[
Q_p\longmapsto \widetilde Q
=Q_p+P^{-1}B_{12}Q_b
\]
is a translation with Jacobian \(1\). Taking \(P\) near a fixed well-conditioned matrix, \(B_{12}\) small, and \(Q_b\) near a fixed nonzero row ensures that a whole neighborhood of \(\widetilde Q=0\) lies inside the free \(Q_p\)-box.

An angular neighborhood of a fixed full-rank \(V\) is open in \(S^3\), hence has positive surface measure. Every sufficiently small point in that cone satisfies \(\sigma_{\min}(\widetilde Q)<\delta\), so the entire cone is routed to BOUNDED.

Thus nothing escapes the split set-theoretically, but a positive-measure cone escapes both successful estimates: PEEL is not dispatched there, and BOUNDED is non-integrable. The actual integral remains finite.

### 3. Mechanism that closes the corner

The minimal repair is a polar blow-up in the shifted free variable
\[
\widetilde Q=\rho\Theta,\qquad \Theta\in S^3,
\]
combined with PEEL—or equivalently the direct rescaling \(\Gamma=\rho H\).

After PEEL,
\[
\int_\Gamma L^{-c'}d\Gamma
\asymp
\|Q_b\|^{-2}\rho^{-2(c'-1)}
\Bigl(
 \|P\Theta\|_F^2+
 \|C\Theta(I-\operatorname{Proj}_{Q_b})\|_F^2
\Bigr)^{-(c'-1)}.
\]

On the sphere, the angular pivot coefficient satisfies
\[
\|P\Theta\|_F^2
\ge \sigma_{\min}(P)^2\|\Theta\|_F^2
=\sigma_{\min}(P)^2>0.
\]
This does not require \(\Theta\) to have full rank: \(P\) is injective and \(\Theta\neq0\). The literal \(w\) still equals \(\rho^2\|P\Theta\|^2\); it is the coefficient after removing \(\rho^2\) that is bounded below.

This is not contained in either branch as dispatched. It uses PEEL precisely on points classified as “ill-conditioned” by the absolute condition. A suitable repair is a radial PEEL subbranch or a scale-invariant split using \(\sigma_{\min}(\widetilde Q)/\|\widetilde Q\|_F\).

Two setup caveats:

- \(Q_b=O(1)\) must mean bounded away from zero; allowing \(Q_b\to0\) is another corner.
- The displayed PEEL equality is generally false for a finite \(\Gamma\)-box; it is exact over all \(\mathbb R^2\), and an upper bound for a finite box. The stated asymptotic holds when the finite box contains \(0\) in its interior. Also, uniformity in \(P\) requires a uniformly invertible \(P\)-subbox; mere invertibility inside \([-1,1]^4\) gives only a pointwise lower bound.