<task>
Lean 4 formalisation, DLN achiever chart. A team consensus (incl an xhigh Codex) just confirmed a build shape, but I found its PREMISE is false by direct Lean #eval, and need a decorrelated read on the right fix before building.

SETUP. A chart map phi : (Fin N → ℝ) → (Fin N → ℝ), phi = paramsEquivFlat ∘ chartParamsGen(decoder).
- INPUT coords are graded by `chartIdxEquiv : Fin N ≃ ChartIdx`, ChartIdx = Σ k:Fin L, Fin(schurDim k) ⊕ Fin(liftDim k). bLayer(input coord) = k.
- OUTPUT coords are graded by `paramsEquivFlat : Params ≃ Fin N → ℝ` via FlatIdx = Σ s:Fin L, (row, Fin(M_s.succ)). Output layer = s.
- The chart's layer-s output (a flattened chain-layer A_s) depends, I PROVED (sorry-free), only on INPUT layers ≤ s (one-sided, lower-triangular under the INPUT grading bLayer).

THE GOAL: express |det Dphi| as a product of per-layer block dets via Matrix.BlockTriangular.det, which needs ONE grading bLayer : Fin N → ℕ that grades BOTH the matrix's ROWS (output coords) and COLUMNS (input coords) of DFrame_M (the fused frame's fderiv, a Fin N → Fin N matrix).

THE PROPOSED FIX (team + Codex confirmed): build e : Fin N ≃ FlatIdx LAYER-COMPATIBLE with chartIdxEquiv — a per-layer fibre bijection ChartIdx-fibre s ≃ FlatIdx-fibre s — so the reshape (flatEquivOf e).symm makes Frame_M's output coord i have the SAME layer as input coord i. They asserted the per-layer cardinalities match: schurDim s + liftDim s = M(s.castSucc)·M(s.succ).

WHAT I FOUND (Lean #eval, (3,3,3,3), L=3, M=[3,3,3,3], tach=[3,2,1,0]):
  chart-slot per-layer counts (schurDim k + liftDim k): [12, 12, 3]
  Params per-layer counts (M(k.castSucc)·M(k.succ) = Wext k · Wext(k+1)): [9, 9, 9]
Totals both 27, but PER-LAYER they DIFFER. So NO per-layer fibre bijection ChartIdx-fibre s ≃ FlatIdx-fibre s exists (different fibre sizes). The "layer-compatible e" the team confirmed CANNOT be constructed. roleSquare_eq gives (t_s+r_s)(t_s+c_s) = t_{s-1}·M_s (a SHIFTED product), NOT schurDim k + liftDim k = M_k·M_{k+1}.

The deeper structure: the INPUT grading (chartIdxEquiv, which boundary's Schur-frame/lift slot a coord is) groups coords as [12,12,3]; the OUTPUT grading (which chain-layer A_s a Params coord belongs to) groups as [9,9,9]. My PROVEN locality is: output-layer-s reads input-layers ≤ s. But "input layer" = chartIdxEquiv boundary, "output layer" = Params layer — these are DIFFERENT [12,12,3] vs [9,9,9] partitions of the same Fin N.
</task>

<output_contract>
4 terse sections:
1. VERDICT: is the team's "layer-compatible per-fibre e" route (A) dead because the per-layer counts differ, or (B) salvageable because I'm conflating two things? Commit.
2. THE RIGHT GRADING: for Matrix.BlockTriangular.det of DFrame_M (rows=output Params coords, cols=input chartIdxEquiv coords), what single bLayer : Fin N → ℕ works? Note: the matrix's rows and columns are BOTH Fin N but indexed by DIFFERENT semantic objects (output Params slot vs input chart slot). Does BlockTriangular.det even apply to a matrix whose row-meaning ≠ col-meaning, or must I FIRST conjugate/reindex so rows and cols share an index? Give the cleanest formulation.
3. Given my PROVEN fact (output-Params-layer-s reads input-chart-layers ≤ s, where the two layer notions partition Fin N differently as [12,12,3] vs [9,9,9]): can this still yield a block-triangular det? The det telescopes as ∏ over what blocks — input-grouping, output-grouping, or a common refinement (the SCC condensation, like the (3,3,3,3) hand-built frameB with 13 blocks)? 
4. CHEAPEST next check to pin the right grading before I build (a Lean #eval or a structural argument).
</output_contract>

<grounding_rules>
You don't have the repo. Reason from the structure stated. The [12,12,3] vs [9,9,9] mismatch is a hard Lean #eval fact, not an inference — take it as given. The team's confirmation was on the (now-falsified) premise that the per-layer counts match. Flag inference vs fact. The crux: a single bLayer must grade a matrix whose rows and columns are differently-indexed; clarify whether that's even well-posed for BlockTriangular.det and what the fix is.
