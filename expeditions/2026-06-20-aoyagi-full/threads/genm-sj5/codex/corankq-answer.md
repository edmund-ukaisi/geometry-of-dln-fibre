The verdict is asymmetric:

- With all \(U_i\) uniformly bounded below, the corner charges add exactly.
- If a \(U_i\) is allowed to vanish, the old corank-\(q\) corner can genuinely RLCT-collapse.
- The full DLN integral retains \(7/2\) only because the vanishing-unit locus must be integrated with its transverse product-rank charge. Relabeling it “corank \(q+1\)” without proving that charge is insufficient.

There is also an error in the supplied numerical pairs. The correct table is

\[
(D_q,d_q)=(1,6),(4,3),(8,0),
\]

not \((8,6),(4,3),(1,0)\).

## Q1 — PROVEN: the uniformly coercive \(q\)-corner is additive

Assume \(a_i>-1\) and, near the corner,

\[
0<\kappa\le U_i(u)\le K<\infty .
\]

Set

\[
A:=\frac12\sum_{i=0}^{q-1}(a_i+1).
\]

On the chart where \(u_0\) is maximal, write \(u_i=r\tau_i\) for \(i\ge1\). Then

\[
du_0\cdots du_{q-1}
   =r^{q-1}\,dr\,d\tau,
\]

and

\[
\prod_i u_i^{a_i}
 =r^{\sum_i a_i}\prod_{i\ge1}\tau_i^{a_i}.
\]

Hence

\[
\sum_i u_i^2U_i
 =r^2\left(U_0+\sum_{i\ge1}\tau_i^2U_i\right),
\]

so the radial power is

\[
r^{\sum_i a_i+q-1-2c'}
 =r^{2A-1-2c'}.
\]

Thus

\[
\int_0^\varepsilon r^{2A-1-2c'}\,dr<\infty
\iff c'<A.
\]

Iteratively, after merging \(u_0,\ldots,u_k\), the exceptional exponent is

\[
H_k=\sum_{i=0}^k a_i+k.
\]

Adding \(u_{k+1}\) contributes \(a_{k+1}+1\), so

\[
H_{q-1}=\sum_i a_i+q-1
       =\sum_i(a_i+1)-1.
\]

The other \(q-1\) maximal-coordinate charts give the same threshold.

The Beta calculation gives the exact endpoint. With \(t_i=u_i^2\), followed by \(t_i=sp_i\),

\[
I(c')\asymp
\frac1{2^q}
B\!\left(\frac{a_0+1}{2},\ldots,\frac{a_{q-1}+1}{2}\right)
\int_0^\varepsilon s^{A-c'-1}\,ds.
\]

Therefore

\[
\boxed{\lambda_{\mathrm{corner}}
=\frac12\sum_i(a_i+1)}.
\]

At equality the divergence is logarithmic.

For \((3,3,3,4)\):

| collapsing values \(q\) | \(D_q\) | \(d_q=3(3-q)\) | \((D_q+d_q)/2\) |
|---:|---:|---:|---:|
| 1 | 1 | 6 | \(7/2\) |
| 2 | 4 | 3 | \(7/2\) |
| 3 | 8 | 0 | \(4\) |

For the corank-two corner, \(a=(3,2)\), so the charges are \(4+3=7=D_2+d_2\).

The equality \(\sum_i(a_i+1)=D_q+d_q\) is a separate Jacobian/charge identity; it does not follow merely from the corner lemma.

## Q2 — YES: vanishing units can cause a genuine collapse

For fixed nonnegative coefficients, let

\[
S=\{i:U_i>0\}.
\]

Variables with \(U_i=0\) disappear from the loss, so

\[
\boxed{\lambda_{\mathrm{slice}}
=\frac12\sum_{i\in S}(a_i+1)}.
\]

Consequently, for \(a=(3,2)\):

\[
U_0=0<U_1\quad\Longrightarrow\quad \lambda=\frac32,
\]

while

\[
U_1=0<U_0\quad\Longrightarrow\quad \lambda=2.
\]

These fixed-slice divergences are explicitly formalized in [RouteMSJCorner334.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCorner334.lean:240).

There is an even sharper joint-collapse witness. Let \(z\in\mathbb R^D\) and take

\[
U_0=U_1=|z|^2.
\]

Then

\[
F=|z|^2(u_0^2+u_1^2),
\]

and the integral factorizes. Its threshold is

\[
\lambda=\min\!\left(\frac D2,\frac72\right).
\]

For \(D=1\), this is exactly the crude collapse \(\lambda=1/2\).

If only one coefficient vanishes, for example

\[
F=u_0^2|z|^2+u_1^2,
\]

then disjoint-sum/Beta integration gives

\[
\boxed{\lambda
=\frac32+\min\!\left(2,\frac D2\right)}.
\]

Thus \(D=1\) gives \(\lambda=2<7/2\). The original \(7/2\) is recovered only when the vanishing locus supplies \(D\ge4\) transverse dimensions.

Therefore the answer is:

\[
\boxed{\text{Allowing }U_i\to0\text{ without transverse charge does collapse the RLCT.}}
\]

The DLN recursion avoids it only after redoing the joint integral. If \(\rho\) measures the new singular-value collapse, the stable-block integration satisfies

\[
g_q(\rho)\asymp
\begin{cases}
1,&2c'<d_q,\\
\log(1/\rho),&2c'=d_q,\\
\rho^{d_q-2c'},&2c'>d_q.
\end{cases}
\]

With the exact tube density

\[
d\mu_q\asymp \rho^{D_q-1}\,d\rho,
\]

the outer integral becomes

\[
\int_0^\varepsilon
\rho^{D_q+d_q-1-2c'}\,d\rho,
\]

and hence has threshold

\[
\frac{D_q+d_q}{2}.
\]

For the concrete chain these thresholds are \(7/2,7/2,4\). The deeper stratum is therefore non-worse, but not always strictly better: \(q=1\) and \(q=2\) are both binding at \(7/2\).

The recursion \(q\mapsto q+1\) is finite because \(q\le r\). It is sound only if each deeper tube exponent \(D_{q+1}\) is proved; an a.e. deletion of \(\{U_i=0\}\) does not control its surrounding tube.

## Q3

### (a) PROVEN

On a genuine corank-\(q\) cell with stable singular values bounded below by \(\kappa\), the \(U_i\) are uniformly coercive. The coupled-corner threshold is exactly

\[
\boxed{\frac12(D_q+d_q)}.
\]

Exactness also uses an upper bound on the units, available on the bounded cell. The two-block finiteness theorem appears in [RouteMSJSlice334.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJSlice334.lean:61).

### (b) DERIVED, with a correction

At \(\sigma_{r-q}=\kappa>0\), the coefficient remains at least \(\kappa^2\). Thus the integrand and the fixed-cell estimate extend continuously to the seam. Crossing the seam merely changes which estimate is used.

However, the numerical thresholds do not always equal each other:

\[
\lambda_1=\lambda_2=\frac72,\qquad \lambda_3=4.
\]

So “continuously matches” cannot mean equality of adjacent thresholds. It means the estimates overlap at the positive cutoff and the deeper threshold is no smaller. As \(\kappa\downarrow0\), the displayed \(\rho^{D_q+d_q-1-2c'}\) calculation is the actual seam-matching argument.

### (c) DERIVED

After assigning equality boundaries consistently, the finite rank-sector decomposition gives

\[
\int_{\mathrm{box}}F^{-c'}
 =\sum_q\int_{\mathrm{cell}_q}F^{-c'}.
\]

Once every cell—including its angular/deeper-rank faces—is covered by the corresponding tube estimate,

\[
c'<\min_q\frac{D_q+d_q}{2}
=\frac72
=\frac12\minAdm
\]

implies every summand is finite.

## Q4 — no concrete \(q\) fails, but the identification is not automatic

For the corrected concrete charges,

\[
D_q+d_q=(7,7,8),
\]

so no \(q=1,2,3\) gives a threshold below \(7/2\).

The product pushforward must not be replaced by Lebesgue measure in the singular values. For a real \(M\times N\) matrix, the SVD density contains

\[
\prod_i\sigma_i^{|M-N|}
\prod_{i<j}|\sigma_i^2-\sigma_j^2|.
\]

If \(q\) singular values scale together by \(\rho\), the total radial exponent is

\[
q|M-N|+q(q-1)+(q-1)
=q(|M-N|+q)-1
=D_q-1.
\]

Thus the non-Lebesgue pushforward supplies precisely the determinantal tube charge rather than causing an undershoot.

For a matrix product, however, algebraic codimension alone is insufficient: one still needs a stratified tubular or resolution statement showing that \(D_q\) is the actual measure exponent. Without that step, \(\sum(a_i+1)=D_q+d_q\) is an inference, not a consequence of the corner algebra. The repository itself still identifies uniform shared-unit control across the general recursive cover as a separate obligation in [cert.md](/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/genm-vslice/cert.md:254).

Final adjudication:

\[
\boxed{\text{ADD on each uniformly coercive cell; genuine COLLAPSE on a vanishing-unit slice;}}
\]

\[
\boxed{\text{the full DLN avoids it only through the proved transverse }D_{q+1}\text{ charge.}}
\]