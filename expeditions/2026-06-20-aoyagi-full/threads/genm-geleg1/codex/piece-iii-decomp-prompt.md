<task>
Lean 4 + Mathlib v4.29, DLN networks. Decompose the general-L "corner-elimination chart" Φ (piece iii
of the D1 ≥-leg), the analytic heart generalizing a ~1300-line L=2 construction. I need the CLEANEST
recursion + a concrete sub-lemma LADDER I can build & bank incrementally. Diagnosis only, no Lean code.

WHAT EXISTS (L=2, file D1L2PhiExpl.lean, ~1300 lines):
- `BlockParamsL2 H r` = pair of block matrices (A0 : (r⊕(H0-r))×(r⊕(H1-r)), A1 : (r⊕(H1-r))×(r⊕(H2-r))).
- `schurChartRaw : BlockParamsL2 → BlockParamsL2` — the rational reparametrization. Blocks
  A0=[[X,Y],[Z,W]], A1=[[S,T],[Uu,V]]; M11=XS+YUu, M12=XT+YV, M21=ZS+WUu; A0red=W−ZX⁻¹Y,
  A1red=V−Uu M11⁻¹ M12. Output: (fromBlocks X Y M21 A0red, fromBlocks M11 M12 Uu A1red). Same type.
- `schurChartRawInv` — explicit rational two-sided inverse on {det X≠0}∩{det M11≠0} (X⁻¹, M11⁻¹ the
  Mathlib nonsingular inverse; five block-algebra reconstruction lemmas prove Ψ∘Φ=id, Φ∘Ψ=id).
- ContDiff²-on-domain (via matrix inv/adjugate/det entrywise ContDiff), `schurChart_global` (the
  globalised C² chart Φ with invertible derivative at 0, fixing 0), `recoverProduct` (rebuild the
  reindexed product from chart output), `schurReadoutF_L2`, and `schur_loss_germ_L2_at_pivot`
  (output: ∃ Φ f', ContDiff ℝ 2 Φ ∧ HasFDerivAt Φ f' 0 ∧ Φ 0 = 0 ∧ lossFlatShift =ᶠ[𝓝 0] F∘Φ).

WHAT I HAVE (general L, pieces i+ii, banked green):
- piece (i): common prefix pivot ι : (s:Fin(L+1))→Fin r→Fin(H s), all injective, with every prefix
  minor (prodAux v s).submatrix (ι 0)(ι s) invertible (det≠0). NO per-layer pivots (Cauchy-Binet-free).
- piece (ii): `genChain` = the ℕ-indexed block chain (layer s = v_s reindexed by sumSplit(ι·) at both
  vertices); `reindex_prod_eq_genPartProd` : reindex(sumSplit(ι0))(genChainCol L)(prod H v)
  = partProd(genChain) L; `genPartProd_toBlocks₁₁` : (partProd genChain k).toBlocks₁₁
  = (prodAux v k).submatrix (ι 0)(ι ⟨k,hk⟩) — so piece(i)'s det≠0 ⟹ IsUnit of every partial pivot.
- Banked general-L Schur telescope (DeepestSchurRecursion): `partProd`, `blockSchur`,
  `schur_product_ldu_rec` (needs BOTH per-layer AND per-partial-product pivots invertible), and the
  asymmetric two-factor `schur_product_factor`/`schur_product_ldu`/`blockSchur_mul` (needs only the
  LEFT-factor pivot + the product pivot — NOT the right factor's own pivot).

CONSTRAINT (from a prior Codex + reviewer): the general-L chart must AVOID per-layer pivots (hLayer),
because piece (i) does NOT provide them (they'd need Cauchy-Binet, absent in v4.29). So the chart must
iterate the ASYMMETRIC two-factor step (each grouping (prefix P_s)·(layer v_s) needs only the prefix
pivots P_s, P_{s+1} — which I have). The math is confirmed wall-free; any wall is Lean bookkeeping
(dependent-opaque-width casts over Fin(H_s−r) block widths).

QUESTIONS:
1. RECURSION SHAPE. What is the cleanest general-L chart? Options: (a) a single map
   `BlockParamsGen H r → BlockParamsGen H r` defined by recursion on L, applying the L=2 `schurChartRaw`
   step to the LAST adjacent pair of the running fold; (b) compose L−1 two-factor steps as a fold;
   (c) a wholesale closed-form general-L reparametrization (all corners at once). Which minimizes the
   dependent-width cast pain AND lets the two-sided-inverse + ContDiff proofs go by induction reusing
   the L=2 lemmas? Note the L=2 chart stays in the SAME type BlockParamsL2 — does an analogous
   "same-type" general-L map exist, or must the type change per step (breaking a clean recursion)?
2. WHAT CAN BE REUSED vs REBUILT. Which of {schurChartRaw, schurChartRawInv, the 5 recon lemmas,
   ContDiff-on-domain, schurChart_global, recoverProduct, germ} generalize by INDUCTION reusing the L=2
   instance as the base/step, vs need a fresh general-L proof? Is there an inductive invariant that
   makes the two-sided inverse + ContDiff fall out layer-by-layer?
3. THE LADDER. Give a concrete ORDERED list of 5-10 sub-lemmas/defs to build & bank incrementally
   (each a green boundary), lowest-risk-first, that assembles to the `schur_loss_germ` general-L
   producer (∃ Φ f', ContDiff² ∧ HasFDerivAt f' 0 ∧ Φ 0 = 0 ∧ lossFlatShift =ᶠ F∘Φ). Flag which rung
   is the likely CEILING for one work session and where the cast-bookkeeping concentrates.
4. RISK. Any place the "iterate the asymmetric two-factor" plan secretly re-introduces a per-layer
   pivot need, or where the recursion's inductive hypothesis needs something piece (i) doesn't give.
</task>

<output_contract>
1. RECURSION VERDICT: pick (a)/(b)/(c) (or a better option), 3-5 sentences why, incl. the same-type question.
2. REUSE MAP: for each of the ~7 L=2 ingredients, one line: "induction-reuse" | "fresh" | "not needed".
3. LADDER: ordered numbered list (5-10 rungs), each: name + one-line content + risk (low/med/high) +
   whether it's a clean bank boundary. Mark the likely one-session ceiling.
4. RISK: <=5 bullets on hLayer-leakage / IH-gap / cast concentration.
Under ~500 words. Diagnosis only.
</output_contract>

<grounding_rules>
Distinguish mathematical facts (you can reason about the algebra) from INFERENCES about the Lean proof
effort / what the downstream interface needs (I have the interface; flag inferences as such).
</grounding_rules>
