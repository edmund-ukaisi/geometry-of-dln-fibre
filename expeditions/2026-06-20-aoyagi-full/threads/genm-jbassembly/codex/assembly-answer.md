**Q1 — The L-Recursion**

[DERIVED FACT] Put `t_{-1}=M_0` and
\[
q_i(T)=(t_{i-1}-t_i)(M_{i+1}-t_i),\qquad
Mval(M,T)=\sum_{i=0}^{L-1}q_i(T).
\]

[DERIVED FACT] The clean peel at boundary `i` is:
\[
Y_i=L_i
\begin{pmatrix}
P_i&0\\0&\Gamma_i
\end{pmatrix}
R_i,\qquad
R_iA_{i+1}=\binom{V_i}{W_i},
\]
with `Y_i` of size `t_{i-1} x M_{i+1}`, pivot `P_i` of size `t_i x t_i`, and
\[
\dim \Gamma_i=(t_{i-1}-t_i)(M_{i+1}-t_i)=q_i.
\]
Then
\[
Y_iA_{i+1}\cdots
=
L_i
\binom{P_iV_i}{\Gamma_iW_i}A_{i+2}\cdots .
\]

[DERIVED FACT] If `P_i,L_i,L_i^{-1}` are bounded units, then
\[
\|Y_iA_{i+1}\cdots\|^2
\asymp
\|V_iA_{i+2}\cdots\|^2+
\|\Gamma_iW_iA_{i+2}\cdots\|^2.
\]

[INFERENCE] The induction variable should be the remaining boundary index together with the incoming rank `t_{i-1}` and the chosen rank-flag suffix, not the collapsed matrix `H` as an unconstrained generic matrix. Algebraic depth reduction `A_0A_1=H` is exact, but treating `H` as free loses the `q_0` Schur block and its Jacobian/codimension bookkeeping.

[DERIVED FACT] On a complete good branch, the accumulated endpoint block is
\[
E_T=\bigoplus_i \Gamma_i,\qquad
\dim E_T=\sum_i q_i(T)=Mval(M,T).
\]
The terminal quadratic form has shape
\[
g_T((\Gamma_i)_i)=\sum_i\|\Gamma_iU_i\|^2,
\]
where the tail maps `U_i` are the resolved right factors.

[DERIVED FACT] If every `U_i` has a uniform left inverse, then
\[
g_T(E)\ge \min_i\sigma_{\min}(U_i)^2\sum_i\|\Gamma_i\|^2,
\]
so the banked endpoint applies in dimension `Σ q_i`.

[DERIVED FACT] Sum-not-min can also be seen by the one-step integral:
\[
\int_{\|x\|\le R}(\|x\|^2+h)^{-c}dx
\lesssim
\begin{cases}
1,&c<q/2,\\
h^{q/2-c},&c>q/2.
\end{cases}
\]
Thus peeling a `q`-dimensional block shifts the remaining exponent by `c-q/2`, giving threshold
\[
q/2+\lambda_{\mathrm{tail}},
\]
not `min(q/2,\lambda_tail)`. This is the coupled recursion.

---

**Q2 — The Pivot Handling**

[DERIVED FACT] In the scalar `t=1` slice,
\[
F=a^2\|vA_2\|^2+\|(Cv+\Gamma W)A_2\|^2.
\]
Dropping
\[
L=\begin{pmatrix}1&0\\ C/a&I\end{pmatrix}
\]
is valid only with a uniform bound on `L^{-1}`, hence only when `|a|>=δ>0`.

[INFERENCE] The pivot `a` should not be placed in the same endpoint block as `v,Γ`. On a rank-`t` chart, the pivot minor is a unit. The locus where it tends to zero is routed to a lower-rank chart/stratum. If one insists on a global chart crossing `a=0`, then the vertical-slice disjoint model fails.

[DERIVED FACT] For general pivot `P`,
\[
\|L[P V;\Gamma W]\|^2
\ge \|L^{-1}\|^{-2}
\bigl(\sigma_{\min}(P)^2\|VA_{\rm tail}\|^2+\|\Gamma WA_{\rm tail}\|^2\bigr).
\]
A lower bound on the pivot minor gives a lower bound on `σ_min(P)` because entries are boxed.

[DERIVED FACT, determinant-inverse flag] The Schur coordinate
\[
\Gamma=D-CP^{-1}B
\]
uses `det(P)^{-1}`. The triangular coordinate change `(P,B,C,D) -> (P,B,C,Γ)` has Jacobian `1` in the `D/Γ` block, but the formula is only controlled where `P^{-1}` is bounded. Any normalization changing variables by `P` would introduce determinant powers that must be counted.

[DERIVED FACT] The shifted domain for `Γ` is bounded on a chart with `P^{-1}` bounded and original variables boxed. Then the endpoint over `[-1,1]^n` extends to a fixed ball/cube by scaling. Without the pivot lower bound, the `Γ` domain can become unbounded, so the fixed-cube endpoint hypothesis is not available.

[INFERENCE] Width-general disjoint-block reduction is achievable only chartwise after rank stratification and bounded-unit control. It is not achieved by the raw global slice as stated.

---

**Q3 — The A_L-Rank-Drop Branch**

[DERIVED FACT] The endpoint condition for
\[
g=\sum_j\|X_jA_L\|^2
\]
requires the map `X_j -> X_jA_L` to be uniformly injective on the resolved joint block. If `A_L` has left-kernel directions, `g` vanishes on the joint sphere.

[INFERENCE] That locus must be routed as another rank-flag branch, not ignored. It is exactly the next determinantal stratum of the remaining tail.

[DERIVED FACT] If the incoming active rank is `s=t_{L-2}` and the final rank choice is `r=t_{L-1}`, the added boundary charge is
\[
q_{L-1}=(s-r)(M_L-r).
\]
For a complete zero-product branch one eventually reaches `r=0`; the total branch threshold is
\[
\frac12\sum_i q_i(T).
\]

[INFERENCE] Such a branch is not automatically “non-binding”; it is non-binding only if its `Mval` is larger than the minimum. If it were smaller, it would change `minAdm`. Termination is finite because the boundary index advances and the rank flags are finite nonincreasing integer choices.

---

**VERDICT**

[INFERENCE] A naive single-joint-block-to-the-endpoint proof is not sound width-general. The sound route is boundary-by-boundary peeling with an accumulated block or exponent-shift induction; the banked endpoint is a terminal chart lemma once all pivots and tail maps are uniformly nondegenerate. The most likely failure mode is loss of a uniform sphere lower bound, either from dropping an unbounded pivot unit as `a -> 0` or from applying the endpoint while the shared deep factor has rank drop.