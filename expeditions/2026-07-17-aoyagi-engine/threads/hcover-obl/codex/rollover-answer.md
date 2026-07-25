**VERDICT: NO-GO as stated.** The rollover compounding is harmless, but hypothesis (ii) is stronger than the established transitivity and is generally false.

1. **Equivariance**

   **Fact:** Compositions of coordinate permutations remain coordinate-permutation isometries; commutativity is not even required. Thus compounding cannot create a non-isometry.

   **Inference:** This alone does not prove equivariance on the residual blow-up chart. One must additionally show that the stabilizer preserves the residual block and that the chart/residual identification intertwines its action. Standard coordinate blow-ups have this property when all earlier pivots are fixed, but that lemma is not among the stated facts.

2. **Two index constraints**

   **Fact:** Fixing one \(d_{s-1}\)-position leaves \(S_{d_{s-1}-1}\); the \(d_s\)-gauge is independent. On the residual Cartesian block the action is
   \[
   S_{d_{s-1}-1}\times S_{d_s}.
   \]

   **Inference:** The two factors independently move the row and column, so they are transitive on candidate pivot pairs. Hence they can canonicalize the next pivot; there is no rollover interference.

   However, this product is not generally the full symmetric group on the block’s entries.

3. **Single most likely break**

   Confusing transitivity with full symmetric action. For example, on a \(2\times3\) residual block the available group is \(S_2\times S_3\), of order \(12\), not \(S_6\), of order \(720\). It cannot perform arbitrary entry permutations.

If hypothesis (ii) is weakened to the transitivity actually needed for choosing one pivot, and residual-chart equivariance is proved, then the rollover step is GO.