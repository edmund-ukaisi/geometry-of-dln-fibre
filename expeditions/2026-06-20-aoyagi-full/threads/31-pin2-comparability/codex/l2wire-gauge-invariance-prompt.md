<task>
Lean 4 / Mathlib formalisation, DLN RLCT geometry. RED-TEAM ONE reasoning chain my controller approved
for closing an L=2 diffeo bridge. I need you to find any HOLE in it (especially a gauge-invariance
step). This is a pen-and-paper soundness check, not Lean tactics.

## Setup
- `deepestPoint s` (L=2, layers s=0,1): the deepest critical point's rank-r layer matrices. Layer 0:
  tail-COLUMNS zero, leading r×r block A11 INVERTIBLE. Layer 1: tail-ROWS zero.
- The squared-Frobenius loss `dlnLoss B w = frobSq(prod(w) − B)` where prod(w) = layer product, B target.
- `rlctAt(dlnLoss, deepestPoint)` = the real-log-canonical-threshold (local RLCT) we want. It equals
  `rlctAtOn Φ wstar` for various reparametrizations Φ (the loss pulled back through gauge charts).
- A gauge chart factors the loss near the deepest point into a REG part (`Sreg`, the off-corner blocks)
  + a SINGULAR/CORE part (`Score`, the (2,2)-Schur complement of the residual). Both are read off
  `reindex( P0 · (prod(w) − B) · QL )` in the corner split (Fin n → Fin r ⊕ Fin (n−r)), where
  P0, QL are ENDPOINT FRAMES (changes of basis at the two ends).
- Two frame choices for (P0, QL):
  - PRODUCER frames `Pf0, Qf1` from a generic rank-normal-form (NOT block-triangular). These currently
    key the `Score` used in the loss-squeeze (`rlctAt(loss) = rlctAtOn(Sreg_producer + Score_producer)`,
    proven).
  - CONSTRUCTED TRIANGULAR frames `P0', Q1'` via explicit normalizers:
    P0' = [[A11⁻¹,0],[−A21·A11⁻¹, I]] (block-LOWER), Q1' = [[Ã11⁻¹, −Ã11⁻¹·Ã12],[0,I]] (block-UPPER),
    [Invertible A11] from the leading-block-invertible fact. These give hPtri/hQtri (block-triangularity)
    needed by the diffeo bridge.

## THE APPROVED REASONING CHAIN (what I must red-team)
"Use the CONSTRUCTED triangular frames P0', Q1' EVERYWHERE — define Score' (and Sreg') via P0', Q1'
(not the producer frames). Then:
  (i)   hPtri/hQtri hold by construction (P0' block-lower, Q1' block-upper).
  (ii)  The loss-squeeze `rlctAt(loss) = rlctAtOn(Sreg' + Score')` holds with the SAME proof, since the
        squeeze is frame-parametric and P0', Q1' satisfy the same 7 frame facts the producer frames did
        (units, boundary-triviality Qf0=I/Pf1=I, hNF: P·deepestPoint·Q = corM, hcorner, hinterface).
  (iii) The diffeo bridge then fires (hPtri/hQtri available), giving
        `rlctAtOn(Sreg' + Score') = rlctAtOn(Sreg' + coreΦ)` (coreΦ = absorbed-core energy).
  (iv) CLAIM (the controller's gauge-invariance step): the RLCT is the same whether keyed to the
       producer frames or the triangular frames, because 'reg + singular are CO-FRAMED' and 'RLCT is
       gauge-invariant'. So no Score-equality between producer-Score and triangular-Score is needed —
       we just work entirely in the triangular frame and never reference the producer Score."

## What I need you to scrutinize
- Is step (ii) actually true? The 7 frame facts: do the CONSTRUCTED P0', Q1' satisfy ALL of them — in
  particular hNF (P0'·deepestPoint_0·(boundary Q=I) = corM, and the LAST layer's
  deepestPoint_1·Q1' = corM), boundary-triviality (Qf0=I means layer-0 RIGHT frame is identity — but
  P0' is the layer-0 LEFT frame, consistent?), and hinterface (vacuous at L=2)? Flag any frame fact the
  triangular construction might VIOLATE (e.g., does forcing P0' block-lower clash with hNF, or with the
  layer-1 right-frame having a UNIT (2,2) block hQf22 that PIN1 needs)?
- Is step (iv) even NECESSARY, or does working-entirely-in-triangular-frame make it vacuous? I think if
  Score' and the loss-squeeze are BOTH keyed to the triangular frame, the producer Score never appears,
  so there's NO cross-frame equality to prove and NO gauge-invariance argument needed — the whole thing
  is self-consistent in the triangular frame. Confirm or refute: is the controller's gauge-invariance
  appeal (iv) actually load-bearing, or a red herring (the real content is just (ii))?
- The LANDMINE I care about most: does the loss-squeeze / the rest of the gauge construction
  (regStraighten, deepestEFull_deriv, the PIN1 hQf22 unit-(2,2)-block fact) depend on the SPECIFIC
  producer frame in a way that the triangular frame BREAKS? I.e., is "P0', Q1' satisfy the same 7 facts"
  enough, or are there HIDDEN dependencies on the producer frame's structure beyond those 7 facts?
</task>

<output_contract>
1. VERDICT on the chain: SOUND / SOUND-WITH-CAVEAT / HOLE. One paragraph.
2. Step (ii): for EACH of the 7 frame facts, does P0'/Q1' satisfy it? Flag the risky ones (hNF on
   layer-1, hQf22 unit-(2,2)-block, the boundary L/R frame consistency). If any is violated or unclear,
   say which and why.
3. Step (iv): is the gauge-invariance appeal load-bearing or a red herring? If working entirely in the
   triangular frame is self-consistent (no producer Score reference), say so plainly — that's the
   cleanest route and avoids any cross-frame RLCT-invariance lemma.
4. The single biggest risk to "P0'/Q1' satisfy the same 7 facts" — name the hidden dependency if one
   exists, else state you found none from what I gave.
5. If HOLE: the minimal extra fact or different construction that fixes it.
</output_contract>

<grounding_rules>
Block-matrix algebra + RLCT-gauge-invariance reasoning. Mark each claim (i) one-line-justifiable
identity, or (ii) inference/assumption you can't verify from what I gave — flag (ii) explicitly. Don't
invent Lean lemma names. If the gauge-invariance step (iv) is unnecessary because the triangular-frame
route is self-contained, say so directly — I'd rather drop a load-bearing-looking step than carry a
hand-wave.
</grounding_rules>
