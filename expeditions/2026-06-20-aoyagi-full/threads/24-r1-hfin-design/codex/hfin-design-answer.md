**1. Cover Completeness**

The clean frame is a finite chart-tree induction.

At each internal node `v`, with active set `A_v`, your `recStep` gives

\[
L_v \doteq \bigcup_{p\in A_v} L_{v,p}
\]

up to the null slice `{all active coordinates = 0}`. If the recursive tree is finite, induction on tree height gives that the union of composite leaf charts covers the original box up to a finite union of null sets. Since the maps are polynomial on bounded boxes, null sets stay null under the chart maps. Equivalently, the integral identity follows by repeated use of `recStep`.

For termination, do **not** use total degree. Blow-ups often preserve or increase total degree after factoring exceptional monomials. Use a resolution-complexity measure tied to the algorithm:

\[
\mu=(\mu_{\rm mat},\mu_{\rm vec},\mu_{\rm mon})
\]

lexicographically.

- `μ_mat`: sum of unresolved coupled matrix block areas `a b`. A pivot/Schur step on an `a x b` block replaces the coupled residual by an `(a-1) x (b-1)` block, so it drops by `a+b-1`.
- `μ_vec`: number/size of unresolved clean vector norm blocks. Radializing a clean `d`-vector replaces it by one radial coordinate with Jacobian exponent `d-1`.
- `μ_mon`: remaining incomparable monomial summands after the matrix/vector blocks have been radialized. This is a finite monomial-principalization problem; in the two-summand case below it terminates in exactly the displayed blow-ups.

So: structural induction is the right frame, but the decreasing measure is **not total degree**. It is “unresolved coupled block size plus unresolved monomial comparability.”

**2. The Corank-2 Delta Branch**

For `(3,3,4)`, the minimizing rank profile is `t_1=1`:

\[
Mval=(3-1)(3-1)+1\cdot 4=8,\qquad \lambda=8/2=4.
\]

After peeling rank `1` from `C^1`:

\[
F \sim \|T\|^2+\|\Delta S\|^2,
\]

with `T` a clean `1 x 4`, `Delta` free `2 x 2`, and `S` free `2 x 4`.

Clean `T` block: radial blow-up of `T in R^4` gives

\[
\|T\|^2=r^2 U_T,\qquad J=r^3,
\]

so

\[
T_T=\frac{3+1}{2\cdot 1}=2.
\]

Delta block: blow up the four entries of `Delta`, say `Delta=aB` with one entry of `B` equal to `1`. Then `J=a^3`. In that chart, one row-linear combination of `S` is a clean `4`-vector `u`, and

\[
\|\Delta S\|^2=a^2\|BS\|^2
      =a^2 s^2 U_D
\]

after radializing `u`, with `J_s=s^3` and `U_D >= 1`. Thus the monomial axes are

\[
a^2s^2,\qquad h_a=h_s=3,
\]

so

\[
T_{\Delta S}=\min\left\{\frac{3+1}{2},\frac{3+1}{2}\right\}=2.
\]

The coupled `Delta S` block does **not** lower the threshold below `2`. The wrong “per-row scalar” recursion fails because it loses this shared `Delta` radial variable.

**3. The Disjoint-Sum Crux**

The product chart with

\[
F=r^2U_T+a^2s^2U_D
\]

is **not yet a monomial leaf**. If one stops there, one incorrectly sees the separate thresholds `2` and `2` and may take a minimum. That would prove only `2`, which is wrong.

You must refine the sum by comparing `r` with `as`.

Initial density:

\[
r^3 a^3 s^3.
\]

Blow up `{r,a}`.

`r`-pivot chart: `a=r\alpha`.

\[
F=r^2(U_T+\alpha^2s^2U_D),\qquad
J=r^7\alpha^3s^3.
\]

Threshold:

\[
\frac{7+1}{2}=4.
\]

`a`-pivot chart: `r=a\beta`.

\[
F=a^2(\beta^2U_T+s^2U_D),\qquad
J=a^7\beta^3s^3.
\]

Now blow up `{β,s}`.

If `s=βγ`:

\[
F=a^2\beta^2(U_T+\gamma^2U_D),\qquad
J=a^7\beta^7\gamma^3,
\]

so the active thresholds are

\[
\frac{7+1}{2}=4,\qquad \frac{7+1}{2}=4.
\]

If `β=sγ`:

\[
F=a^2s^2(\gamma^2U_T+U_D),\qquad
J=a^7s^7\gamma^3,
\]

again giving threshold `4`.

So the combined leaf threshold is **the sum**, not the minimum. The extra blow-ups transfer the Jacobian weight of the other factor onto the dominant radial variable. That is exactly how `2+2=4` appears using only the monomial threshold computation.

Newton LP for the same model:

\[
\min 4w_r+4w_a+4w_s
\]

subject to

\[
2w_r\ge 1,\qquad 2w_a+2w_s\ge 1,\qquad w_i\ge0.
\]

The minimum is

\[
4\cdot \frac12+4\cdot\frac12=4.
\]

**4. Magnitude**

My read: the cover/termination part is bounded. The corank-`>=2` issue is serious, but it is not by itself a general determinantal-resolution mountain if you use Schur-pivot reduction plus monomial comparability blow-ups.

The single hardest sub-obligation is the general version of #3:

> Given several disjoint resolved summands with known monomial thresholds, construct a finite common refinement on which the sum becomes monomial times a nonvanishing unit, and prove that every final leaf has threshold equal to the additive value required by `Mval/2`.

That is the theorem that prevents the proof from collapsing from `4` to `2` in the `(3,3,4)` branch. Mathematically it is toroidal/monomial combinatorics, not deep determinantal geometry. Formalization effort: not trivial, but I would classify it as a bounded finite-recursion plus induction project, with the monomial-sum refinement lemma as the main cost.