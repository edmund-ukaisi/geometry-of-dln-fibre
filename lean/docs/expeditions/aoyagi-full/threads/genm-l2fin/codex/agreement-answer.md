1. **Route choice: neither under the current signature.**  
   **Certainty:** Route B is not sound for arbitrary `Pf/Qf`: `fromBlocks 0 ΔY 0 ΔT` has zero first column, but right multiplication by `Qf last` with nonzero `{21}` mixes the second column into `{11}` and `{21}`.  
   **Inference:** Route A is clean only if you already have an intrinsic telescope theorem absorbing the outside `corner`; `framedParamsPivot_last` alone does not give it.

2. **Extra hypotheses needed: YES.**  
   You need `hPtri/hQtri` or, better, a banked telescope/de-frame theorem with its hypotheses. Plain invertibility of `Pf/Qf` is not enough; invertibility lets you move frames, but does not prevent block mixing.

3. **Proof sequence after adding the frame/telescope facts:**

   1. Peel both L=2 products with `prod_eq_prodAux_mul_last (m:=1) H A rfl rfl`.
   2. Normalize prefixes using `prodAux_succ`, `prodAux_zero`, `one_mul`; follow the existing `prod_deepestM_eq_two_of_L2` pattern.
   3. Rewrite layer `0` equality by `framedParamsPivot_psiSplitRawL2Core_of_ne 0 h0ne`.
   4. Reduce both sides to `G0 * G1ψ` versus `G0 * G1q`.
   5. Rewrite `G1ψ` and `G1q` with `framedParamsPivot_last`.
   6. Cancel the common corner and common `X/Z` parts using `readX_psiSplitRawL2Core_eq`, `readZ_psiSplitRawL2Core_eq`.
   7. Rewrite the remaining difference as  
      `Pf last * reindex⁻¹ (fromBlocks 0 ΔY 0 ΔT) * Qf last`.
   8. Apply the frame/telescope hypothesis: either de-frame to raw blocks, or use `hPtri/hQtri` to prove the framed difference has zero `{11}` and `{21}` and a controlled `{12}`.
   9. Expand the outer product blocks with `reindex_mul_fromBlocks`.
   10. Close `{11}` and `{21}` by `simp` with `Matrix.toBlocks_fromBlocks₁₁/₂₁`.
   11. For `{12}`, reduce to the raw identity `A0 * ΔY + Y0 * ΔT = 0`, rewrite Δ via `readY_psiSplitRawL2Core_last_eq` and `coreRead_psiSplitRawL2Core_last`, then apply `e2_regPreserve`.
   12. Finish block coercions with `fromBlocks_toBlocks`, `Matrix.toBlocks_fromBlocks₁₂`, and extensionality if needed.

4. **Biggest cast risk:** the L=2 peel introduces `finCongr e.symm` reindex casts on the last factor. Sidestep it by reusing the prefix-induction shape from `prod_deepestM_eq_two_of_L2`; only after `prodAux_succ` has exposed the two factors, clean residual identities with `erw [finCongr_refl, reindex_refl_refl]`.