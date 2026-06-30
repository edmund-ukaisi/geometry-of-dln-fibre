<task>
Lean 4 + Mathlib. I must construct, for the ∀M-L2 interior achiever chart, a factor list
`fs : List (ChartFactor N)` (N = routeMAmbient M, an opaque ℕ) with `composeFold fs = phiFlatLDU…kLDU`
(the LDU-lensed structured chart) such that the per-factor abs-dets multiply to a PURE MONOMIAL
`∏_j |u_j|^{leafH_j}`. `ChartFactor N` = {f : (Fin N→ℝ)→(Fin N→ℝ), D : pointwise fderiv CLM, hasD}.
`composeFold` = foldr (· ∘ ·); `composeFold_abs_det` telescopes the per-factor dets (banked).

I need to pick the CHEAPEST bounded construction route. Two candidate routes, both with banked machinery:

ROUTE A — per-role `bridgeCLE` layer-op fold (RouteMBridgeCLE/RouteMConjBlock/RouteMRoleCLE):
  fs = [conjBlockFactor (paramsBlockSplitCLE ρ_radial) radialMap …,
        conjBlockFactor (paramsBlockSplitCLE ρ_schur_s) schurFrameMap …,   -- per boundary s
        conjBlockFactor (paramsBlockSplitCLE ρ_ldu_s) lduCoreMap …, … chainMap].
  Each factor conjugates a block self-map (schurFrameMap |det|=|det K|^{r+c}, lduCoreMap
  |det|=∏|q_i|^{2(t-1-i)}, banked) by a CLE `paramsBlockSplitCLE ρ : Params M ≃L Block × Rest` built
  from a per-role reindex `ρ : ChartIdx M t ≃ Block ⊕ Rest`. The CLE-collapse `composeFold_bridge_eq`
  reduces `composeFold fs = phiFlatLDU` to a Params-level fold equality. PROBLEM: NO per-role reindex
  `ρ` is banked anywhere — `paramsBlockSplitCLE`/`conjBlockFactor` exist only as machinery, never
  instantiated. So Route A needs me to DESIGN + BUILD a dependency-ordered sequence of `ChartIdx ≃
  Block ⊕ Rest` reindexes over opaque widths (radial pivot → per-boundary Schur-K → per-boundary LDU
  pivots → chain), each a finite `Equiv` on the disjoint-role `ChartIdx` decomposition. That reindex
  sequence is the bulk of the work.

ROUTE B — anchor-style flat composite (how the WORKING fixed-width anchors did it):
  The (4,4,2,2) anchor PROVED `composeFold [linearFactor Q4422CLM, radialFactor active 0] = phi4422`
  (banked `phi4422_eq_composeFold`), and (3,3,3,3) computed its det via `phi3333 = Q3333CLM ∘ T3333`,
  `T3333 = Frame3333 ∘ Kparam3333`, det via `det_comp` on the flat maps `Frame3333Deriv`/`Kparam3333Deriv`.
  So the anchors used a SHORT flat composite: a linear outer reshape (Q = paramsEquivFlat∘pack, a CLM,
  `linearFactor`, |det|=1) ∘ a frame map ∘ a Kparam-lens ∘ radial. But over OPAQUE widths the frame
  (Schur) and Kparam-lens are NONLINEAR full-ambient maps, not CLMs — so `linearFactor` only covers Q;
  the frame/Kparam factors would need to be full-ambient `ChartFactor`s with their fderivs, which is
  essentially Route A's content WITHOUT the per-role CLE split (just flat self-maps + their fderivs
  via the chain rule, det via det_comp).

QUESTION: which route is the cheaper BOUNDED path to `fs` for ∀M-L2, and what is the single most
load-bearing sub-step to build first (the cheapest de-risking probe)? Specifically:
1. Does Route B (flat composite, no per-role CLE) actually avoid the per-role reindex work, or does the
   det-telescope `∏|det factor_i| = ∏|u_j|^{leafH_j}` SECRETLY need the block structure (so Route A's
   reindex is unavoidable to read off which axis each |det K_s|=∏q_i lands on)?
2. The kLDU lens already makes `det(readK(kLDU x) s) = ∏_i q_{s,i}` a monomial (banked readK_kLDU_det).
   Given that, can the frame factor's det `|det K_s|^{r+c}` be read as a monomial in the FLAT coords
   directly (Route B), or only after a per-role coordinate identification (Route A)?
3. Recommend: A or B, the first lemma to build, and the cheapest fixed-width (e.g. (3,3,4)) probe that
   would confirm the chosen route generalizes before the opaque-width build.
</task>

<output_contract>
1. ROUTE verdict: {A, B, HYBRID} + ≤4 sentences why it's the cheaper bounded path.
2. Q1+Q2 answer: does the det-telescope force the per-role block structure (Route A reindex), or can
   the monomial be read flat (Route B)? ≤4 sentences, mark DERIVED vs INFERENCE.
3. The single first lemma to build (exact shape) + the cheapest fixed-width probe.
Total under ~350 words. Mark each claim DERIVED (from the machinery shapes I gave) vs INFERENCE.
</output_contract>

<grounding_rules>
You do NOT have the repo. Reason only from the machinery shapes/facts above. Do not invent Mathlib or
repo lemma names beyond those I named. The anchors (phi4422, phi3333) ARE built sorry-free — treat
their construction style as DERIVED evidence. The opaque-width generalization is the uncertain part.
</grounding_rules>
