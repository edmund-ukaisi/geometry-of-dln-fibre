<task>
Lean 4 / Mathlib (v4.29). DLN RLCT formalisation. I'm closing an L=2 diffeo bridge; two germ-local
discharges remain. Give me the PROOF SKELETON (Lean tactic outline + the exact lemma applications) for
each, OR name the precise obstruction. I hold the context below; reason from it.

## GOAL 1 (the PRECONDITION blocking both fills — highest priority): the germ-membership
At a point in `deepest_gauge_construction` (L=2), with `wstar0 := (paramsEquivFlat H) (deepestPoint …)`,
`split := deepestSplit H r hr hL wstar0` (a `≃ₜ`, `split wstar0 = 0` via `hsplit_base`), I must prove:
  `∀ᶠ x in nhds wstar0, psiSplitRawL2 H r hr hL (split x) ∈ Metric.closedBall (0) (cutoffBump … ).rIn`
AND (for the hWdet of sub-4)
  `∀ᶠ x in nhds wstar0, split x ∈ Metric.ball (0) (l2ExtraRadius …)`  [the UNIT-locus radius].
Facts available:
- `psiSplitRawL2_zero : psiSplitRawL2 … 0 = 0`.
- `psiSplitDeltaL2 = psiSplitRawL2Core − id` (at L=2 `psiSplitRawL2 = psiSplitRawL2Core`);
  `contDiffAt_psiSplitDeltaL2_of_mem_tsupport : q ∈ tsupport (cutoffBumpSplit) → ContDiffAt ℝ ⊤
   (psiSplitDeltaL2) q`. (So psiSplitRawL2 is ContDiffAt — hence ContinuousAt — at 0, since 0 ∈ tsupport.)
- `split` is a homeomorphism (`≃ₜ`), so `Continuous split`, `split wstar0 = 0`.
- `(cutoffBump …).rIn = jointUnitRadiusSplit/4 > 0` (`rIn_pos`); `closedBall_mem_nhds`.
- For the second: there's `ball_l2ExtraRadius_subset`/`l2ExtraUnitSetSplit` (a ball of radius
  `l2ExtraRadius` around 0 ⊆ the unit locus); `l2ExtraRadius > 0` (presumably). Need `0 ∈ ball`.
Q1: skeleton for `∀ᶠ x in 𝓝 wstar0, psiSplitRawL2 (split x) ∈ closedBall 0 rIn`. I think it's:
  `ContinuousAt (psiSplitRawL2 ∘ split) wstar0` (from ContinuousAt psiSplitRawL2 0 ∘ ContinuousAt split
  wstar0, using split wstar0 = 0 and psiSplitRawL2 0 = 0 = center) → `Filter.Tendsto … (𝓝 0)` →
  `(… ⁻¹' closedBall 0 rIn) ∈ 𝓝 wstar0` via `closedBall_mem_nhds`. Confirm the exact lemma names
  (`ContinuousAt.comp`? `ContDiffAt.continuousAt`? `Filter.Tendsto.eventually`? `Metric.closedBall_mem_nhds`?)
  and the cleanest way to get `ContinuousAt psiSplitRawL2 0` from `contDiffAt_psiSplitDeltaL2_of_mem_tsupport`
  (needing `0 ∈ tsupport (cutoffBumpSplit)` — is 0 in the support? the bump is 1 near 0, so yes).

## GOAL 2 (hLDUtie): prod c'' = Score-(1,1)-Schur-integrand
Sub-4 (Option-2) needs: `prod (deepestM H r) c'' = Matrix.of (fun i j => Score-integrand i j)` where
`c'' = Function.update (fun s => decode(q).2.1 s + schurCorrection(q) s) (lastLayer) ((1−K)·S1)` and the
Score-integrand = the (2,2)-Schur complement `M₂₂ − M₂₁(M₁₁+1)⁻¹M₁₂` of
`Mw = reindex(rThr, pivotThr J)(endpointP0·(prod(symm x)−B)·endpointQL)`.
Available engine: `rcore_schur_factor_of_corner_split (Mw Mhat eR eMid eC G0 G1) (hGG : Mhat = G0*G1)
  (hsplit : reindex eR eC Mhat = fromBlocks 1 0 0 0 + reindex eR eC Mw) [Invertible (reindex eR eMid
  G0).toBlocks₁₁] [Invertible (reindex eMid eC G1).toBlocks₁₁] [Invertible (reindex eR eC (G0*G1)).toBlocks₁₁]`
  → the Schur factorization. Plus banked: `prod_deepestM_eq_two_of_L2` (L=2: prod(deepestM) c = c₀·c₁),
  `prod_absorbed_eq_schur_ldu`, `reindex_mul_schur_factor`, `schur_frame_transform`,
  `absorbedCore_psiSplitRawL2Core_last`, `l2T1p_sub_Z1A1invY1p_eq`. And `hS3b : reindex(endpointP0·B·
  endpointQL) = fromBlocks 1 0 0 0` (corner-split). hWdet : det(l2W q) ≠ 0.
Q2: skeleton for hLDUtie — how do `prod_deepestM_eq_two_of_L2` (→ G0=c₀, G1=c₁) + the corner-split
(hS3b gives `Mhat = endpointP0·prod(decode x)·endpointQL` corner = fromBlocks 1 0 0 0 + Mw?) + the 3
invertibility instances + rcore_schur_factor_of_corner_split compose to the integrand? Where's the
likeliest cast/defeq snag (the Fin-2 `deepestM` width, the cleaned-tuple-vs-c₀·c₁ match)?
</task>

<output_contract>
GOAL 1: a concrete Lean tactic skeleton (5-10 lines) with exact lemma names; flag any unverified name.
GOAL 2: the composition order (which lemma feeds which) + the single likeliest snag. If GOAL 2 needs a
piece not in my list, name it.
Rank: which of GOAL 1 / GOAL 2 is lower-risk to land first.
</output_contract>

<grounding_rules>
v4.29 Mathlib. Mark any lemma name you're unsure exists as "(verify)". If GOAL 1's ContinuousAt route
has a hole (e.g. 0 ∉ tsupport, or psiSplitRawL2 not ContDiffAt 0), say so — that's the real obstruction.
</grounding_rules>
