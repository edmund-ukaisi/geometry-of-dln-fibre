<task>
Lean 4 / Mathlib v4.29. (2,2,2) RLCT ≤-direction, the LAST hard piece. I need a change-of-variables
lemma for the SPECTATOR-LIFTED step-2 blow-up. THRASHING: 5+ attempts, Fin-indexing friction.

DEFINITIONS (all gated/proven):
- tailLift F u = Fin.cons (u 0) (F (Fin.tail u))   : (Fin 8→ℝ)→(Fin 8→ℝ), F : (Fin 7→ℝ)→(Fin 7→ℝ).
- step2E z = ![z0, z1, z1*z2, z1*z3, z4, z5, z6]   : a pivot-blow-up on Fin 7 (pivot z1, active {1,2,3}).
- step2E_lintegral_image (V hV g) : ∫⁻_{step2E''(V\{z1=0})} g = ∫⁻_{V\{z1=0}} ofReal|det₂|·(g∘step2E),
    where det₂ = (pivotBlowupOnDeriv {1,2,3} 1 z).det = z1²  (GATED, via the pivotBlowupOn infra).
- finPeel 7 : (Fin 8→ℝ) ≃ₜ ℝ×(Fin 7→ℝ), finPeel 7 u = (u0, tail u), measure-preserving (finPeel_mp 7).
- tailLift_eq_finPeel : tailLift F = (finPeel 7).symm ∘ (Prod.map id F) ∘ finPeel 7.
- setLIntegral_image_of_mp (e:M≃ᵐN)(he:MeasurePreserving e)(S)(g) : ∫⁻_{e''S} g = ∫⁻_S g∘e.
- I tried proving "tailLift step2E = pivotBlowupOn {2,3,4} 2 on Fin 8" (true numerically) to reuse the
    Fin-8 pivotBlowup c-o-v directly — but the Fin.cons/Fin.tail vs pivotBlowupOn-if-membership simp
    won't close (Fin.cons _ _ ⟨k,_⟩ doesn't reduce; fin_cases gives ⟨k,_⟩ not Fin.succ form).

GOAL: a c-o-v for tailLift step2E over a domain. For the ≤-direction I integrate over a PRODUCT box
(cubeBox 8 δ = univ.pi (Icc -δ δ)), so finPeel 7 '' box = (Icc -δ δ) ×ˢ (univ.pi(Icc -δ δ) on Fin 7).
I want: ∫⁻_{tailLift step2E '' (boxδ \ {u2=0})} g  expressed with the Jacobian |u2|² and g∘(tailLift step2E).
</task>

<output_contract>
≤ ~400 words, concrete v4.29 lemma names. ONE recommended route + the Lean skeleton:
(A) PUSH the "tailLift step2E = pivotBlowupOn {2,3,4} 2" identity through (so I reuse the gated Fin-8
    pivotBlowupOn c-o-v). What's the robust tactic for "Fin.cons a g ⟨k,_⟩ = explicit" + the
    pivotBlowupOn if-membership? Is `Fin.cases` + `Fin.cons_zero`/`Fin.cons_succ` + `Finset.mem_insert`
    + `Fin.reduceEq`/`decide` the way, and how to handle the step2E ![...] indexing after Fin.cons_succ
    (the ![...] applied to j : Fin 7 needs Matrix.cons_val reductions per j)? OR
(B) finPeel-PEEL: ∫⁻_{tailLift step2E '' (box\Z)} g — transport via setLIntegral_image_of_mp through
    finPeel.symm, then on ℝ×(Fin7→ℝ) the (id×step2E)-image of a PRODUCT set s×ˢt via setLIntegral_prod
    + Tonelli + the gated step2E_lintegral_image on the t-fiber. Give the exact set-image identities
    (finPeel''(box) = product; (id×step2E)''(s×ˢt') = s ×ˢ (step2E''t'); the \{u2=0} ↔ \{(tail).1=0}
    bookkeeping) and the Jacobian-passthrough (det depends only on the tail's z1 = u2).
Which is SHORTER + less Fin-friction? If (A), give the EXACT working tactic for the identity (I've
failed 5×). If (B), the exact product/image identities + the Tonelli skeleton.
</output_contract>

<grounding_rules>
SURE vs INFERRED v4.29 names. The Fin.cons reduction under fin_cases is the documented friction — if
(A) needs a specific normal form (Fin.cons_succ wants i.succ; fin_cases gives Fin.mk), say exactly how
to bridge. For (B), flag whether (id×step2E)''(s×ˢt) = s ×ˢ (step2E''t) is a SURE Set lemma
(Set.image_prod / Set.prod_image_image?) or needs a manual ext proof.
</grounding_rules>
