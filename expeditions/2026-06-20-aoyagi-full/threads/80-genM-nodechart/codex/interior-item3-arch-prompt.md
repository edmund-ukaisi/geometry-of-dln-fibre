<task>
Lean 4 + Mathlib. Designing the general-M (opaque-width) interior achiever chart's Jacobian-determinant
route. I need a decorrelated opinion on an ARCHITECTURE FORK I just discovered. Facts (verified by reading code):

GOAL: a chart `phi : (Fin N → ℝ) → (Fin N → ℝ)` (N opaque) with MONOMIAL Jacobian
`|det Dφ(u)| = ∏_j |u_j|^{leafH j}`, plus a decoder-agnostic rate `routeMCore(phi u) = (u_p)²·U`.

I have TWO banked worked instances and they use DIFFERENT det architectures:

INSTANCE 1 — (4,4,2,2), pure-radial (no Schur/LDU, K-cores trivial):
  phi4422 = composeFold [linearFactor Q4422CLM, radialFactor {0,1,2,3} 0].
  A clean 2-factor FOLD. Det via the banked telescope `composeFold_abs_det` (per-factor |det| product).
  Map equality `composeFold fs = phi4422` is a 5-line funext+rfl-chain. CLEAN.

INSTANCE 2 — (3,3,3,3), the only t≥2 K-core instance:
  phi3333 = Q3333CLM ∘ Frame3333 ∘ Kparam3333.
  - Q3333CLM: LINEAR (measure-preserving coord reshape, |det|=1).
  - Kparam3333: the LDU lens — IDENTITY on all coords EXCEPT it maps free (x1,x2,x3,x4) to the 2×2
    K-core entries [x1, x1·x2, x1·x3, x1·x2·x3+x4]; |det DKparam| = (x1)² (lower-triangular). Does NOT
    touch the radial pivot x0.
  - Frame3333: a SINGLE FUSED bilinear map. CRITICAL: the radial coordinate x0 is NOT a separate
    pivotBlowupOn factor — it is DISTRIBUTED across Frame3333's output entries (it appears ADDED in one
    diagonal entry `z0 + (bilinear)`, and MULTIPLIED into specific other entries `z0·z13`, `z0·z24`, …).
    Frame3333 fuses the Schur frame + the B/C chain + the radial into one bilinear map. Its det
    `|det DFrame3333| = |z0|^5·|z9|^3·|z1·z4−z2·z3|^2` comes from a BLOCK-TRIANGULAR analysis of the
    27×27 Jacobian (BlockTriangular.det over an SCC grading), NOT a composeFold telescope.
  Det via `LinearMap.det_comp` on the literal Fin-27 fderivs: det = |det Q|·|det DFrame|·|det DKparam|
    = 1 · (z0^5·z9^3·(z1z4−z2z3)^2) · (x1)^2, then substitute Kparam's z-values to get the monomial
    |x0|^5·|x1|^4·|x4|^2·|x9|^3.

So phi3333 is NOT a composeFold of [radial, schur, ldu, chain] factors — the radial scaling is fused into
Frame3333, and the det is via det_comp on the FUSED map's block-triangular Jacobian.

THE BANKED FACTOR MACHINERY: `composeFold` + `composeFold_abs_det` (telescope), `radialFactor`
(pivotBlowupOn, det |u_p|^{card−1}), `schurChartFactor E` (det |K.det|^{r+c}), `lduChartFactor E`
(det ∏|q_i|^{2(t−1−i)}), `chainChartFactor` (det 1) — each conjugated by an abstract CLE
`E : (Fin N → ℝ) ≃L[ℝ] Block × R`. These ASSUME the chart decomposes as a CLEAN COMPOSITION of block-wise
maps. The general decoder `genBlkFlatStruct` reads block coords through an OPAQUE `chartIdxEquiv`
(`Fintype.equivFin`-based, Classical.choice — NOT rfl-reducible).
</task>

<output_contract>
Answer in 3 short sections:

1. THE FORK — which det architecture should the general-M interior chart use?
   (A) FUSED: define phi_M = Q_M ∘ Frame_M ∘ Kparam_M generalizing phi3333 directly; det via
       det_comp + a general BLOCK-TRIANGULAR det of DFrame_M over opaque widths. (Cost: building
       Frame_M as one fused opaque-width bilinear map + its block-triangular Jacobian det ∀M — does
       BlockTriangular.det generalize over opaque Wext/Text block sizes, or does the SCC-grading need
       per-M definitional structure?)
   (B) FOLD: re-engineer the chart as composeFold [radialFactor active p, per-boundary {lduChartFactor,
       schurChartFactor, chainChartFactor}]; det FREE via composeFold_abs_det. (Cost: this requires the
       chart to ACTUALLY be a clean composition of block factors — but phi3333 shows the real chart fuses
       radial into Frame. Can the fused chart be REFACTORED into an extensionally-equal clean fold? Is the
       radial genuinely separable from Frame, or is the fusion essential?)
   Rank A vs B, with the single biggest risk of each.

2. THE RADIAL-FUSION QUESTION (load-bearing for B): in phi3333, is the radial x0 distributed across
   Frame3333 because it's MATHEMATICALLY essential (the blow-up must interleave with the bilinear frame),
   or is it an INCIDENTAL packaging choice (x0 could be pulled out as a separate pivotBlowupOn prefactor
   and Frame made x0-free, giving phi = Q ∘ Frame' ∘ radial ∘ Kparam, a clean 4-fold)? If separable: what
   has to be true of the chart for the radial to commute out to the front?

3. If A (fused): does Mathlib's `Matrix.BlockTriangular.det` (the det = ∏ diagonal-block dets for a
   block-triangular matrix under a grading) work when the block sizes are OPAQUE `Wext/Text k` (not
   Fin-literals)? What is the single hardest obstruction to a general-width block-triangular det, and is
   there a cleaner route (e.g. det as a product over the chain layers via a per-layer det, sidestepping
   the SCC grading)?
</output_contract>

<grounding_rules>
You have only my summary, not the code. Mark any step depending on an unstated fact as "ASSUMPTION: …".
Distinguish "clearly follows from your summary" vs "you must verify X". No Lean code blocks >5 lines —
I want the architecture call + the risk ranking, not an implementation.
</grounding_rules>
