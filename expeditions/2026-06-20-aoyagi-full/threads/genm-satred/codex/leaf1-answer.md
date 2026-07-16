### Q1: FALSE FOR \(j\ge1\) — PROVEN

Restricting a nonnegative integral to `pivotShell(ε)` cannot upper-bound the shell contribution; moreover, the two sets are disjoint.

1. **(a)** Best unconditional repair: enlarge to the full `matBox`. Sound, but it sacrifices uniformity.
2. **(b)** Conditionally useful: requires an adaptive singular-direction/minor cover proving the selected subblock is floored. Ky–Fan alone does not control the fixed top-row block \(Q_p\).
3. **(c)** Invalid: the \(j\) small singular values may be below \(\varepsilon'\), including zero.

### Q2: NOT UNIFORM — PROVEN

The frame floor controls \(Z_f\), not
\[
G=[z_0;A_{\rm cor}]Z_f.
\]
The degeneration locus is
\[
\mathcal D=\{(z_0,A_{\rm cor}):\operatorname{rank}([z_0;A_{\rm cor}]Z_f)\text{ drops}\},
\]
especially \(z_0=A_{\rm cor}=0\). Along \(G_t=tG_1\),
\[
I(G_t)=t^{-2c''}I(G_1),
\]
so no bare uniform constant exists. A sequential reduction must retain a singular-value/Gram-minor-dependent factor for the induction, unless the variables are kept jointly integrated.

### Q3: BARE CONSTANT RECOVERABLE, BUT ONLY IN THE REDUCED-RANK RANGE

It is not intrinsically non-uniform merely because \(j\ge1\). The shell itself gives
\[
\sigma_m(G)\ge\varepsilon,\qquad m=\min(M_1,M_{\rm last})-j.
\]
Consequently,
\[
\|XG\|_F^2\ge\varepsilon^2\|XU_m\|_F^2,
\]
which yields a uniform front bound precisely when
\[
\boxed{\,2c''<um\,}.
\]

This is **proven sufficiency**. If route \(\alpha\) instead uses the larger threshold \(c''<u\rho/2\), it is unjustified whenever \(m<\rho\) and \(c''\ge um/2\); accessible limits with the \(j\) small singular values tending to zero then force blow-up.

The cheapest exact check is therefore: **verify \(2c''<um\)**.