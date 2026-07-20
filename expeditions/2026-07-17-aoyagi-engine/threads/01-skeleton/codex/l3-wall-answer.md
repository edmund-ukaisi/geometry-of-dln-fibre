1. **VERDICT: CANNOT-DETERMINE-WITHOUT-X.**

2. **Strongest reason.** KNOWN FACT (reported): SchurCore front-peel fails beyond depth \(2\). KNOWN FACT: cert-d3 and the termination/no-undershoot checks do not construct the support-preserving \(t=1\) merge chart. INFERENCE: \(d=u\,d'\) and its monomial Jacobian are depth-independent, but the required \(\psi\) and terminal pullback for the coupled three-layer residual remain unverified. \(X\) is one complete \(t=1\) root-to-leaf substitution ledger with pullback, Jacobian-unit, and local-cover proofs.

3. **Is SchurCore needed?** INFERENCE: no. Recursive monomial \(\beta\)-charts avoid the one-shot front-peel, while the area formula avoids needing a triangular composite Jacobian or inverse determinant bounds. It does not, however, prove that the remaining residual is a unit/Morse core; that construction burden remains in \(\psi\) and subsequent blow-ups.

4. **Cheapest discriminating test.** Extend [h6_composed_chart_2222.py](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/t01-r2/expeditions/2026-07-17-aoyagi-engine/threads/03-hunt/scripts/h6_composed_chart_2222.py) to one fully emitted \(t=1\) leaf. Start with
\[
A_1=\alpha\!\begin{pmatrix}1&a\\ b&ab+\delta\end{pmatrix},\qquad
A_2=\begin{pmatrix}g_0-ar&g_1-as\\ r&s\end{pmatrix},
\]
take \(A_3\) generic, then apply the first prescribed case-1(1) chart \(d_j=u z_j\) and all remaining leaf substitutions. Using exact symbolic algebra, require simultaneously:
\[
\phi=\psi\circ\beta,\quad
\frac{\det D\beta}{\prod_k u_k^{\mathrm{divExp}_k-1}}=\pm1,\quad
\det D\psi(0)\ne0,
\]
and verify that \(\|A_1A_2A_3\|_F^2/\prod_k u_k^2\) is a unit or has the declared full-rank Morse Hessian. Any leftover coupled higher-order core, or failure of the merge/split sibling images to cover the blow-up center, is the wall.

5. **Main risk behind the optimism.** The proposed \(\psi\) may merely hide an unresolved angular/shared-divisor relation: its Jacobian can remain a unit while the residual is still neither a unit nor Morse.