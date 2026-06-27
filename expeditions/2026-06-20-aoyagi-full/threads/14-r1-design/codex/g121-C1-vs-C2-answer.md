**Verdict: C2.**

**FACT.** The chosen blow-up machinery is a coordinate-subspace blow-up: it applies to centers of the form
\[
\{y_1=\cdots=y_c=0\}
\]
in an already chosen coordinate system, with chart Jacobian
\[
u^{c-1}.
\]

**FACT.** At node 1 in the \((2,2,2)\) anchor, the center \(\{A_1=0\}\) is already coordinate. No Schur step is needed there.

**FACT.** At node \(\ge 2\), after the first blow-up chart with a unit pivot, the next rank-defect condition is not coordinate in the inherited variables. In the \((2,2,2)\) chart it is
\[
r-pq=0,
\]
a bilinear hypersurface in \((p,q,r)\), not one coordinate variable vanishing.

**FACT.** The det-1 Schur change
\[
w:=r-pq
\]
has unit Jacobian, because \(dr/dw=1\). It contributes no monomial weight. After this change, the center becomes the coordinate hypersurface
\[
\{w=0\}.
\]

**INFERENCE.** Therefore, for the Lean build as described, the det-1 Schur straightening is genuinely needed. The coordinate-subspace blow-up theorem cannot be applied directly to \(\{r-pq=0\}\) unless one first changes coordinates so that \(r-pq\) is itself a coordinate.

So the architecture is:

\[
\boxed{\text{det-1 GL/Schur straighten, then coordinate-subspace blow-up.}}
\]

That is **C2**, not C1.

**On “Pure Blow-Up”**

**FACT.** A general blow-up of a non-coordinate ideal, e.g. the ideal \((r-pq)\) or a determinantal/rank-defect ideal, is a different construction from coordinate-subspace blow-up.

**FACT.** The stated `pivotBlowup`-style machinery blows up coordinate subspaces, not arbitrary smooth hypersurfaces or arbitrary ideals.

**INFERENCE.** If Lean had a separate, fully developed theory of blow-ups along arbitrary smooth centers or determinantal ideals, then one could try to eliminate the explicit Schur step by treating the bilinear center directly. But that is not the chosen machinery. With the present coordinate-subspace machinery, the bilinear center must first be straightened.

**INFERENCE.** A sequence of coordinate-subspace blow-ups in the original unstraightened coordinates should not be expected to resolve the matrix-chain rank-defect geometry cleanly. The Schur operation is what keeps the recursive centers coordinate after a unit pivot has been chosen. Without it, the centers become Schur-complement equations such as \(r-pq=0\), then higher determinantal analogues, which are not coordinate subspaces in the ambient chart coordinates.

**Clean Recursion Node**

At each recursive node of the chart family:

1. **Unit-pivot / regular-block chart.**  
   Choose a nonzero pivot minor and normalize it to a unit on the chart.

2. **Det-1 Schur straightening.**  
   Use determinant-1 row and column operations to clear the pivot row/column block and replace the remaining block by its Schur complement.  
   Jacobian contribution:
   \[
   1.
   \]

3. **Smaller-chain reduction.**  
   The unresolved residual is again a zero-product matrix-chain core, but with smaller effective dimensions/ranks.

4. **Coordinate-subspace blow-up.**  
   Blow up the now-coordinate rank-defect center
   \[
   \{y_1=\cdots=y_c=0\}.
   \]
   In a chart where \(y_i=u\hat y_i\), the Jacobian is
   \[
   u^{c-1}.
   \]

5. **RLCT contribution.**  
   If the node has monomial exponent \(k_j\) in \(F\) and Jacobian exponent \(h_j\), its threshold contribution is
   \[
   \frac{h_j+1}{2k_j}.
   \]
   In the rank-vector notation of the build, the coordinate blow-up node has
   \[
   h_j = Mval(t)-1,
   \]
   so the blow-up Jacobian factor is
   \[
   u^{Mval(t)-1}.
   \]

Thus each nontrivial recursive node is exactly:

\[
\boxed{
\text{det-1 Schur straightening, unit Jacobian}
\quad\Longrightarrow\quad
\text{coordinate-subspace blow-up, Jacobian } u^{Mval(t)-1}.
}
\]

The monomial RLCT weights come from the blow-ups, not from the Schur changes.