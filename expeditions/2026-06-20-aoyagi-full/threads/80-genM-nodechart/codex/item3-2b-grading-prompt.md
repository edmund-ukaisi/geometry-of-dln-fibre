<task>
Lean 4 + Mathlib. Designing the opaque-width Jacobian-determinant proof (sub-tide 2b) for a deep-linear-net
achiever chart. I need a decorrelated check on the GRADING for a block-triangular determinant. Facts (verified
by reading code):

THE CHART (Route A, decided): phi = paramsEquivFlat ∘ chartParamsGen ∘ kLDU, where:
- kLDU: an LDU lens reparametrizing each per-boundary K-core's coords (|det DkLDU| = ∏_s monomial in the LDU
  diagonal pivots q_{s,i}; banked per-K-core via lduCoreDeriv_det).
- chartParamsGen u B: produces a tuple of L LAYER MATRICES (A_0, …, A_{L-1}), A_k : Matrix (Fin (Wext k)) (Fin
  (Wext (k+1))) ℝ. The chain recursion: A_k = chainA(N_k)(W_k)(C(k+1)); C(k+1) = Bmat(k+1)·chainQ(N_{k+1}) +
  u·Rmat(k+1); leaf C_L = u·Rfin_L. So layer A_k's OUTPUT entries depend on: the block coords of boundary k
  (N_k, W_k, and via C(k+1) the Bmat/Rmat/N of boundaries ≥ k+1). I.e. layer k reads boundaries ≥ k —
  a TRIANGULAR inter-layer dependency.
- paramsEquivFlat: a measure-preserving LINEAR reshape (|det|=1, the flattening of the layer tuple).

GOAL: |det D(chartParamsGen ∘ kLDU)| = ∏_j |u_j|^{leafH j} (a monomial). The total monomial is:
radial |u_p|^{minAdm−1} · ∏_s (LDU-pivot monomial) · ∏_s |det K_s|^{r_s+c_s} ... but det K_s is now itself
the LDU-pivot monomial (that's the whole point of kLDU).

THE (3,3,3,3) WORKED INSTANCE used a single FUSED map Frame3333 with a bespoke SCC-CONDENSATION grading
frameB : Fin 27 → ℕ (image {0..12}, literal index lists like [0,1,2,5,6,7,8] for the 7×7 K-coupling block,
hand-tuned column permutations). This does NOT transport to opaque widths (Fin-literal indices, Classical
chartIdxEquiv is not rfl-reducible).

MY PROPOSED GRADING (two-level): 
- OUTER: grade flat coords / output entries by CHAIN LAYER k (the triangular layer dependency gives
  block-triangularity over the layer grading b_layer : coord ↦ its layer). det = ∏_k det(layer-k diagonal block).
- INNER (per layer k): the layer-k diagonal block is the within-layer Schur-frame × LDU-core map, whose det is
  |det K_k|^{r_k+c_k} · (LDU monomial) — reusing the banked schurFrame_abs_det + lduCoreDeriv_det per boundary.

QUESTIONS I need adjudicated.
</task>

<output_contract>
Answer in 4 short sections:

1. IS THE TWO-LEVEL GRADING SOUND? Does the triangular inter-layer dependency (layer k reads boundaries ≥ k)
   actually give a BLOCK-TRIANGULAR Jacobian over the layer grading b_layer? Specifically: the off-diagonal
   blocks (∂ A_k entries / ∂ boundary-k' coords for k' ≠ k) — do they vanish in the RIGHT triangular direction
   (lower-or-upper), or is the dependency two-sided (does any A_k entry depend on a STRICTLY-LOWER boundary
   k' < k)? From the recursion A_k = chainA(N_k,W_k,C(k+1)) with C(k+1) reading boundaries ≥ k+1: confirm A_k
   reads ONLY boundaries ≥ k, so the layer grading IS triangular. Flag if I've mis-stated the direction.

2. THE WITHIN-LAYER DET: is the per-layer diagonal block's det genuinely |det K_k|^{r+c}·(LDU monomial), or does
   the chainA/chainQ structure (the N_k, W_k chaining) contribute extra det factors I'm missing? Note chainA is
   the kept-row C(k+1) − N_k·W_k over the lift W_k — does the chaining shear contribute det 1 (like
   chainChartFactor) or something else? The (3,3,3,3) Frame had det |z9|^3 and |z0|^5 factors BESIDES the
   K-coupling — where do THOSE come from in the layer picture (are they the radial u-scaling of Rmat/Rfin
   distributed across layers, and the chaining)? I must not drop a factor.

3. THE RADIAL: under kLDU (which does NOT touch the pivot) the radial u=x_p enters via u·Rmat / u·Rfin in the
   chain. Is the radial |u_p|^{minAdm−1} a SEPARATE prefactor (so phi = ... ∘ radial ∘ kLDU, a clean front
   factor), or is it ALSO distributed across the layer diagonal blocks (so each layer's det carries some
   u-power, summing to minAdm−1)? This decides whether I need a pivotBlowupOn front factor or whether the
   radial powers fall out of the per-layer dets. (At (3,3,3,3) the u^5 was fused into Frame, distributed.)

4. THE OPAQUE-WIDTH GRADING in Lean: BlockTriangular.det needs a grading b : Fin N → α (linear order α) with
   off-block entries vanishing. For the layer grading, b = (coord ↦ which layer it flattens into) via the
   OPAQUE paramsEquivFlat/chartIdxEquiv. Since these are Classical (not rfl), the off-block-vanishing must be
   proved by Equiv.apply_symm_apply cancellation, NOT fin_cases. Is there a cleaner route that AVOIDS a single
   N×N block-triangular matrix entirely — e.g. det of a linear map as a PRODUCT over a composition
   phi = ∘_k (layer-k insertion map), each layer-k map block-diagonal-with-identity-elsewhere, so
   det = ∏_k det(layer-k map) by det_comp (no global grading)? Rank: global-grading-BlockTriangular.det vs
   composition-of-per-layer-maps-det_comp. Which is less brittle under the opaque chartIdxEquiv casts?
</output_contract>

<grounding_rules>
Only my summary, not the code. Mark unstated-fact dependencies "ASSUMPTION: …". Distinguish "follows from your
summary" vs "verify X". No Lean >5 lines — I want the grading adjudication + the cleaner-route ranking.
</grounding_rules>
