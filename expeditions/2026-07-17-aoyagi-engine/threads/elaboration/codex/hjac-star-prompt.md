<task>
Decorrelated adjudication of a Jacobian claim in a Lean formalisation of Aoyagi's DLN resolution.
A seat flagged that FoldProduced.hjac_tie may be UNSATISFIABLE; I (independent reviewer) reached the
OPPOSITE conclusion and need you to VERIFY or REFUTE mine from first principles. Do not trust me.

SETUP (observed from the files):
- A chart's map is gmap = pathMap(steps) = σ_1 ∘ σ_2 ∘ … ∘ σ_k, ROOT-OUTERMOST: σ_1 (root/shallowest,
  first clear) is applied LAST (outermost); σ_k (leaf/deepest, last clear) is applied FIRST (innermost).
- Each step σ_j = shear_j ∘ blockBlowupMap(center_j, pivot_j). blockBlowupMap(S,p): p ↦ w_p;
  j ∈ S∖{p} ↦ w_p·w_j; spectators (j ∉ S) ↦ w_j. Its Jacobian determinant is EXACTLY w_p^(|S|−1)
  — a power of the PIVOT coordinate ONLY, independent of all other coordinates.
- The shear is Jacobian-exactly-1 (hshear) and KEEPS the pivot coordinate: (shear u) pivot = u pivot
  (hshear_pivot). So per-step |jacDet σ_j|(w) = w_{pivot_j}^(|center_j|−1) = jacWeight(jexp_j)(w),
  with jexp_j = (|center_j|−1) at pivot_j, 0 elsewhere.
- FoldProduced.hjac_tie pins atlas.jac c a = Σ_j jexp_j(a) (the naive per-step sum, in SOURCE coords).
- Chart.hjac (the L6 obligation) requires |jacDet gmap|(u) = jacWeight(atlas.jac c)(u) · |unit u| with
  unit NON-VANISHING at the origin.
- CONSTRUCTION FACT (canonCenterOf, corrected): clears in a layer proceed in INCREASING index order
  (cleared = 0,1,2,…); the k-th clear's center EXCLUDES all earlier-cleared indices (the filter has
  cleared ≤ row ∧ cleared ≤ col). Boosts (case11) reuse an earlier-born pivot; a divisor boosted
  multiple times reuses the SAME pivot each time.

THE SEAT'S COUNTEREXAMPLE (D=2): σ₂ = blockBlowupMap({0,1}, 0) [inner/deeper], σ₁ =
blockBlowupMap({0,1}, 1) [outer/shallower]; g = σ₁∘σ₂. Then |jacDet g| = |u0|²|u1| by the chain rule
(jacDet σ₁ at σ₂u = (σ₂u)_1 = u0·u1), while Σjexp = (1,1) gives jacWeight = |u0||u1|, so unit = |u0|
VANISHES ⟹ hjac unsatisfiable. The seat concludes hjac_tie's naive sum is wrong and proposes making
edgeδ/supportAt or jac boost-aware (a statement touch on the locked FoldProduced).

MY CLAIM (verify or refute): the counterexample does NOT model the real construction, and hjac_tie is
CORRECT as rendered.
- Reason A: the chain rule gives |jacDet gmap|(u) = ∏_j |jacDet σ_j|(intermediate_j u) =
  ∏_j (intermediate_j u)_{pivot_j}^(|center_j|−1), where intermediate_j = the composition of the steps
  DEEPER than j (applied before σ_j). This equals ∏_j u_{pivot_j}^(|center_j|−1) = jacWeight(Σjexp)(u)
  (unit ≡ 1) IFF each pivot_j is PRESERVED by all deeper steps: (intermediate_j u)_{pivot_j} = u_{pivot_j}.
- Reason B: in the real construction this preservation HOLDS. The deeper steps (later clears) have
  centers that EXCLUDE earlier-cleared indices, so pivot_j (an earlier index) is a SPECTATOR of every
  deeper step ⟹ unchanged. For a multiply-boosted divisor the deeper boost has pivot_j as ITS OWN pivot,
  which blockBlowupMap preserves (p ↦ w_p) and hshear_pivot preserves ⟹ still unchanged.
- Reason C: crucially, a shallow step σ_j MODIFYING later pivots (via its center∖pivot) does NOT affect
  the Jacobian, because |jacDet σ_j| depends ONLY on pivot_j, and later pivots were already consumed by
  deeper steps at their original values.
- Reason D: the seat's counterexample violates the construction: its deeper step σ₂ has center {0,1}
  INCLUDING coord 1 = the shallower step σ₁'s pivot, and it clears index 0 AFTER index 1 (reversed
  order). A real deeper/later clear's center EXCLUDES earlier-cleared indices, so a real σ₂ would have
  center excluding coord 1, restoring pivot-preservation.

QUESTIONS:
1. Is |jacDet blockBlowupMap(S,p)|(w) = |w_p|^(|S|−1), independent of the other coordinates? (Confirm.)
2. Is Reason A's telescoping criterion correct: naive Σjexp = accumulated |jacDet gmap| (unit ≡ 1) IFF
   every pivot_j is preserved by all deeper steps?
3. Does the real construction satisfy pivot-preservation (Reasons B, C), given shrinking centers +
   pivot-preserving blow-ups + hshear_pivot? Consider both consecutive fresh clears AND a
   multiply-boosted divisor.
4. Is the seat's counterexample therefore UNREAL (Reason D), so hjac_tie is CORRECT as rendered and the
   only missing piece is a per-step-accumulation LEMMA (a proof obligation), NOT a boost-aware statement
   touch on FoldProduced?
5. If you find a REAL scenario (respecting shrinking centers + increasing clear order) where
   pivot-preservation FAILS, exhibit it concretely — that would confirm the seat and refute me.
</task>

<output_contract>
Five numbered answers, terse. For each: TRUE/FALSE/PARTIAL + the decisive reason. End with a one-line
BOTTOM LINE: "hjac_tie correct as rendered (missing = accumulation lemma)" OR "hjac_tie defective
(needs statement touch)" OR "cannot determine — need <X>". Mark INFERENCE vs OBSERVED-in-file.
</output_contract>

<grounding_rules>
Check the jacDet-of-blockBlowupMap claim and the center-shrink filter against the files if you can;
paths: lean/DLNFibre/Core/Aoyagi/BlockBlowup.lean, BlockDivision.lean;
lean/DLNFibre/DLN/RLCT/Engine/EngineConstruction.lean (canonCenterOf);
lean/DLNFibre/DLN/Aoyagi/MonumentAtlas.lean (GeoStep, FoldProduced, hjac_tie :155-156, hσ_jac :72).
If the jacDet-only-depends-on-pivot fact is false, say so — my whole argument rests on it. Flag
inference vs observed.
</grounding_rules>
