VERDICT: **detail-at-scale** — conditional on the actual recursive atlas genuinely containing the stipulated full fan.

1. **Per-node shear.** **Fact:** Let \(\sigma(v)=v+\phi(v)\). Since \(\phi\) writes no coordinate it reads, \(\phi(v-\phi(v))=\phi(v)\); hence \(\sigma^{-1}(v)=v-\phi(v)\) exactly. If
\[
\phi_i(v)=\sum_m a_{im}v_{r_m}v_{s_m},
\]
then \(|\phi_i(v)|\le(\sum_m|a_{im}|)r^2\). Multiple products only enlarge the constant \(C\); they create no new obstruction. “Degree exactly \(2\)” alone is insufficient—the required fact is homogeneous quadraticity plus a coefficient bound. For one global \(f\), take the maximum \(C_*\) over all nodes and pivots.

2. **Full-fan completeness.** **Fact:** Argmax gives an exact cover, not merely an almost-everywhere cover. If the maximal center coordinate \(x_p\neq0\), use \(w_q=x_q/x_p\). If \(x_p=0\), then every center coordinate is zero; choose any pivot and set all source center coordinates to zero. Spectators pass through. A bijective shear cannot introduce an omitted direction. Thus corank does not matter. The claimed exceptional locus “some pivot coordinate is zero” is not an escape locus; only deleting pivot hyperplanes for injectivity may create a separate null-set issue.

3. **Depth.** **Fact, conditional on node shape:** finite depth causes only the recurrence
\[
R_{k+1}=f(\max\{R_k,1\}),
\]
which remains finite. Later centers need only be coordinate blocks in their current chart, not after transport back to root coordinates. **Inference not established by the finite SymPy cases:** every actual recursive node must retain the read/write partition, polynomial shear, nonempty coordinate-block center, and every-pivot continuation.

4. **Overall.** The abstract hcover is a clean library exercise: quadratic-shear inverse/bound, block-blow-up argmax cover, uniform finite-tree coefficient bound, and structural induction. It is not a new-math monument. The finite examples do not themselves certify its instantiation for the complete Aoyagi tree.

**Most likely break:** confusing the synthetic full fan with the actual leaf atlas. For every \(p\in S\), the resolution must contain a valid \(p\)-chart and continuation. A column-pinned or otherwise pruned recursion fails exactly by the exhibited \(\varepsilon e_2\) mechanism unless an explicit symmetry/transport theorem restores those charts.

**Exact check I would add:** at the first depth-two \(3\times3\) residual state, enumerate every off-canonical pivot and verify symbolically that its faithful shear, state update, and next center preserve the recursive residual identity. This tests full-fan realization, not merely the one-step map.