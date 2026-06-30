1. **VERDICT:** **BOUNDED**, with the correction that the selected minor must be taken from the **slice residual vector** `h(t) := q(0,t)`, not from the scalar function `R`.

2. **Load-bearing reason:** since `R(t) = ‖h(t)‖²` and `h(t0)=0`, the extra Morse block in `R` is exactly first-order rank in `dh(t0)`:  
   `Hess R(t0) = 2 (dh(t0))ᵀ dh(t0)`.  
   So if the intended `hchart₂` is built by selecting `extra` independent components of `h`, the first-peel selected-minor IFT pattern applies again. No DeepestGaugeChart / rank-exact pivot machinery is forced.

3. **Sub-question 3:** the scalar gradient `∇R(t0)` **does vanish**. A selected-minor IFT on `R` itself is impossible, and an IFT on `∇R` is really a Hessian/Morse-splitting route. The bounded route uses a **Jacobian-rank condition on the residual vector** `q(0,-)`, not a Jacobian-rank condition on scalar `R`.

4. **Source vs inference:** the source confirms the two-peel assembly consumes `q₂` plus `hchart₂` and constructs the quasi-split data from `C¹` residuals; it does not itself construct `hchart₂`. See [D1IFTResidualProducer.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a13464f8909e17dd6/lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:25) and the first-peel pattern in [D1HChartResidual.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a13464f8909e17dd6/lean/DLNFibre/DLN/RLCT/Validate/D1HChartResidual.lean:330). My bounded verdict assumes `hchart₂` is produced from a selected minor of `d(q(0,-))`.

5. **Technical risk to watch:** proving the `extra`-rank selected minor for the **post-first-peel slice residual vector** in Lean, especially through the IFT inverse, bump-globalisation/germ equality, and the reindexing to the degraded core `M'`. That is likely heavy bookkeeping, but not the #120 gauge-slice wall.