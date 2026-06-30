1. **GAP A: GENUINE OBSTRUCTION at general `H`.**  
   **Asserted from your structure:** the banked D1 engine requires the deepest core to be `lambdaCore(squareWidths m)`, while the available deepest equality gives `lambdaCore (fun s => H s - r)`.  
   **Inference:** unless `H - r` is square, or a theorem identifies the rectangular core with the square one, the engine asks for the wrong deepest-side value. So the general-`H` leaf cannot be closed through this engine as stated.

2. **GAP B: bounded proof gap, not the primary scope wall.**  
   **Asserted from your structure:** `(m,a,b)/hrank₂` is not yet proven but is described as de-risked via finite/structural ingredients.  
   **Inference:** this is work, but not a conceptual obstruction comparable to GAP A.

3. **Cheapest route if avoiding GAP A:**  
   **Inference:** the only plausible bounded route is a **first-peel-only radial/monotonicity argument**: use the general-`H`, general-`v` first-peel chart, compare the slice residual directly against the all-zero deepest rectangular core, and prove  
   `lambdaCore(H-r) ≤ RLCT(slice residual at v)`  
   without invoking the square middle-stratum sweep.  
   If that monotonicity lemma is not already banked in sufficient rectangular generality, then there is **no currently bounded route** from the stated bank alone; flag and stop.

4. **Recommended lemma chain, conditional route:**

   1. Fix arbitrary `v ∈ optimalSet H B'`.

   2. Apply the general first-peel chart package: `dln_hchart_residual` plus the Jacobian-minor existence input.

   3. Use the chart/slice equality to reduce `rlctAt H (dlnLoss H B') v` to regular contribution plus the RLCT of the slice residual.

   4. Use #44 deepest normal form at the front-pivoted deepest point to identify  
      `rlctAt deepest = nRegL2/2 + lambdaCore(H-r)`.

   5. Prove or invoke a rectangular first-peel monotonicity/radial-scaling lemma: the slice residual RLCT at arbitrary `v` is at least the all-zero rectangular core value `lambdaCore(H-r)`.

   6. Add the shared regular contribution.

   7. Conclude  
      `rlctAt deepest ≤ rlctAt v`.

   8. Generalize over `v`.

5. **RANK:** GAP A is the true blocker for the **general-`H`** leaf. GAP B blocks the current square-engine route at arbitrary `v`, but GAP A prevents that route from even matching the deepest value when `H-r` is rectangular.