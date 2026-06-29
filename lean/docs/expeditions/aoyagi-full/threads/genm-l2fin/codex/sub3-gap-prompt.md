<task>
Lean4/Mathlib v4.29. Follow-up on a SPECIFIC gap in a formalisation route. Answer ONLY this.

I am closing sub-3 by instantiating a banked entry-point lemma:

  deepestEFull_sq_sum_eq_of_resid_blocks (q₁ q₂ : DeepestSplit) (A₁ A₂ : Params H)
    (hframe₁ : ∀ s, framedParamsPivot q₁ s = Pf s * A₁ s * Qf s)
    (hframe₂ : ∀ s, framedParamsPivot q₂ s = Pf s * A₂ s * Qf s)
    (hinterface) (hS3b)
    (h11 h12 h21 : reindex(endpointP0·(prod A₁ − B)·endpointQL).toBlocksᵢⱼ
                 = reindex(endpointP0·(prod A₂ − B)·endpointQL).toBlocksᵢⱼ)
    : (∑ deepestEFull q₁ ²) = (∑ deepestEFull q₂ ²)

with q₁ = psiSplitRawL2 q (the "moved" point), q₂ = q.

The brief tells me to THREAD A₁=Aψ, A₂=Aq, hframe₁, hframe₂, hinterface, hS3b as INPUT
hypotheses to the sub (the controller discharges them later at the call site), and to PROVE
only h11/h12/h21 inside the sub.

THE GAP I am checking: A₁=Aψ and A₂=Aq are now ABSTRACT (universally-quantified inputs)
constrained only by hframe₁: framedParamsPivot (psiSplitRawL2 q) s = Pf s · Aψ s · Qf s and
hframe₂: framedParamsPivot q s = Pf s · Aq s · Qf s (plus hinterface, hS3b).

To prove h11/h12/h21 I need prod Aψ and prod Aq to agree on raw blocks {11,12,21}. But Aψ/Aq
are abstract — the only thing I know is the FRAME equations. Question:

(Q) Can I prove `reindex(endpointP0·(prod Aψ −B)·endpointQL)` agrees with
    `reindex(endpointP0·(prod Aq −B)·endpointQL)` on {11,12,21} FROM hframe₁+hframe₂+hinterface+hS3b
    ALONE (+ the readback lemmas relating framedParamsPivot(ψq) to framedParamsPivot(q))?

Key facts:
- L = 2. Layers {0, 1}, last = 1. hinterface forces Qf 0 = 1 and Pf 1 = 1.
- framedParamsPivot_psiSplitRawL2Core_of_ne: framedParamsPivot(ψq) 0 = framedParamsPivot(q) 0
  (layer 0 = non-last, fully fixed under the move).
- At last layer, framedParamsPivot differs only in middle's Y(→Y1') and T(→T1').
- The frame eqs give: Pf s · Aψ s · Qf s = framedParamsPivot(ψq) s and Pf s · Aq s · Qf s =
  framedParamsPivot(q) s. If Pf s, Qf s are INVERTIBLE we could solve Aψ s = Pf s⁻¹ · framedParamsPivot(ψq) s · Qf s⁻¹.
  But invertibility of Pf/Qf is NOT given.

(Q2) Without invertibility of the per-layer Pf/Qf, are Aψ s and Aq s pinned enough?
     Specifically: endpointP0·prod Aψ·endpointQL = prod(framedParamsPivot ψq) by the telescope
     (endpoint_telescoping_eq, which is what hframe+hinterface feed). So
     reindex(endpointP0·prod Aψ·endpointQL) = reindex(prod(framedParamsPivot ψq)) — and SIMILARLY for q.
     Then the {11,12,21} agreement of the RESIDUALS (after subtracting the common reindex(P0·B·QL)=fromBlocks 1 0 0 0)
     is EXACTLY the {11,12,21} agreement of reindex(prod(framedParamsPivot ψq)) vs reindex(prod(framedParamsPivot q)).
     Is THIS the intended path — i.e. I do NOT work with the abstract prod Aψ blocks at all, but
     rather (a) use endpoint_telescoping_eq to rewrite reindex(endpointP0·prod Aψ·endpointQL) =
     reindex(prod(framedParamsPivot ψq)), then (b) prove the framed-product {11,12,21} agreement
     directly via reindex_mul_fromBlocks at L=2 (the per-layer framed factors), using e2_regPreserve
     for {12}? And the abstract Aψ/Aq + hframe/hinterface/hS3b are threaded ONLY so the entry point
     accepts them, while the actual proof re-derives the telescope?
</task>

<output_contract>
Answer (Q) and (Q2) decisively:
1. Is h11/h12/h21 provable from the abstract frame inputs alone (no Pf/Qf invertibility)? YES/NO + why.
2. State the SINGLE cleanest proof path for h11/h12/h21. If it is "rewrite both residuals to
   reindex(prod(framedParamsPivot ·)) via endpoint_telescoping_eq, then compare framed products
   directly", confirm that and give the exact step sequence. If instead the entry point is the
   WRONG tool (because comparing framed products directly via deepestEFull_sq_sum_eq_blocks would
   be strictly simpler and needs only hPtri/hQtri, NOT hframe/hinterface/hS3b), SAY SO — that would
   mean the sub should NOT thread the telescope hyps.
3. CRITICAL: for the {12} leak-kill via e2_regPreserve in the FRAMED product (per-layer frames
   Pf,Qf baked in, NOT just endpoint frames), does the per-layer frame Pf(last)/Qf(last) on the
   last factor BREAK the e2_regPreserve application, or does it go through? e2_regPreserve is
   A0·(Y1+⅟A0·Y0·(T1−T1')) + Y0·T1' = A0·Y1+Y0·T1 — it's about the RAW (unframed) per-layer blocks
   A0,Y0 (first factor) and Y1,T1 (second factor). In the framed product the relevant blocks are
   the framed factors' toBlocks. Does the {12} preservation hold for the FRAMED product, and if so
   does it reduce to e2_regPreserve on the raw blocks (via the telescope de-framing) or does it
   need a framed version? This determines whether the telescope route (de-frame first, then
   e2_regPreserve on raw blocks) is REQUIRED vs optional.
Under 400 words. Mark inference vs certainty.
</output_contract>

<grounding_rules>
No repo access. If you cannot determine whether the per-layer frame breaks e2_regPreserve from
the given signatures, say which additional fact you'd need to check. Distinguish "the telescope
route is required for cleanliness" from "either route works".
</grounding_rules>
