1. **VERDICT — PARTIALLY.**  
Rigorously, the current exported producers only give the two RLCT transports, not a model identification of the residual slice with a DLN core: see [D1HChartResidualC2.lean](/home/ubuntu/workspace/genm-d1l2close2-wt/lean/DLNFibre/DLN/RLCT/Validate/D1HChartResidualC2.lean:101) and [D1SecondPeelChart.lean](/home/ubuntu/workspace/genm-d1l2close2-wt/lean/DLNFibre/DLN/RLCT/Validate/D1SecondPeelChart.lean:587). It is slightly too strong to say “no handle survives”: internally one still has the chart equation `Φ ∘ Ψsymm = id`, and the first peel can even expose the slice derivative ([D1ResidualDerivExpose.lean](/home/ubuntu/workspace/genm-d1l2close2-wt/lean/DLNFibre/DLN/RLCT/Validate/D1ResidualDerivExpose.lean:261)). But that only controls regular directions / first-order data. Your `x² + u⁴` example shows that this is not enough to determine the higher-order residual germ, hence not enough to recover the RLCT value. So the blocked conclusion is correct, but the precise reason is “insufficient germ data”, not literally “nothing algebraic survives”.

2. **LOWER-BOUND / Theorem-4 route — yes, but not through `q₂`.**  
A lower bound on the abstract degraded slice,
`ofReal(lambdaCore M') ≤ rlctAtOn (fun z => ∑ i, q₂ ((0), z) i^2) t0₂`,
is as blocked as equality: the present `q₂` interface does not control the remaining germ enough to prove any nontrivial value statement. The viable weaker route is different: target the one-sided explicit-core reduction
`(nRegL2 H r)/2 + rlctAtOn (dlnLoss (H-r) 0) corePoint_v ≤ rlctAt H (dlnLoss H B) v`,
with `corePoint_v` the explicit reduced-core point attached to `v`, and then use `deepest_le_of_homogeneous_core` on that explicit homogeneous core. That bypasses `degraded_slice_rlct_eq_lambdaCore` entirely.

3. **MINIMAL FIX if blocked — new producer.**  
The single load-bearing new object is a local model witness for the concrete degraded slice:
`R₂ = unit · (dlnLoss M' 0) ∘ φ` near `t0₂`, with `unit` bounded away from `0` and `φ` a local `C¹` diffeomorphism. Once you have that, `degraded_slice_rlct_eq_lambdaCore` is routine from `r1_resolution_general` plus RLCT invariance. A generic strengthening of `rlctAtOn_eq_of_contDiff_chart_rinv` to return more derivatives, or “agreement to sufficient finite order”, is not the right fix: finite-jet data do not pin the RLCT here. So the minimal fix is DLN-specific and is substantively a new explicit-residual producer, even if you scope it more narrowly than a full atlas.

4. **Bottom line.**  
Current two-IFT-peel `q₂` is not enough to prove the DLN-core value; either attach an explicit local DLN-core identification to the concrete residual, or switch to Aoyagi’s explicit full-loss→core reduction and use Theorem 4 directly.