<task>
Lean4/Mathlib v4.29. Give me the cast-correct TACTIC sequence for THREE goals (hdiff11/12/21).
I have the math; I need the exact assembly to avoid finCongr/reindex cast thrash.

## Context (all banked, consume verbatim)
- `prod_eq_two_of_L2 (K : Fin 3 → ℕ) (C : Params (L:=2) K) :
    prod K C = reindex (finCongr rfl) (finCongr rfl) (C 0) * reindex (finCongr rfl) (finCongr rfl) (C 1)`
  (the L=2 peel; running widths K 0, K 1, K 2 = K (last 2)).
- `reindex_mul_split (eR eMid eC) G0 G1 : reindex eR eC (G0*G1) = reindex eR eMid G0 * reindex eMid eC G1`.
- `reindex_mul_fromBlocks (eR eMid eC) G0 G1 : reindex eR eC (G0*G1) = fromBlocks (4 block-multiply combos)`
  with {11}=A0·A1+Y0·Z1, {12}=A0·Y1+Y0·T1, {21}=Z0·A1+T0·Z1 (Aᵢ=toBlocks₁₁ etc of reindex eR eMid G0 / reindex eMid eC G1).
- `framedParamsPivot_psiSplitRawL2Core_of_ne (s) (hs: s ≠ lastLayer) : Cψ s = Cq s` (layer 0 identical).
- `framedParamsPivot_last : Cp last = reindex⁻¹(fromBlocks 1 0 0 0) + Pf last · reindex⁻¹(fromBlocks X Y Z T) · Qf last`
  (X=readX, Y=readY, Z=readZ, T=core, all reads of p).
- move readbacks: readX/readZ FIXED; readY last → l2Y1p; core last → l2T1p.
- `e2_regPreserve [Invertible A0] : A0·(Y1+⅟A0·Y0·(T1−T1')) + Y0·T1' = A0·Y1 + Y0·T1`.
- hinterface (s=0): Qf 0 = 1 ∧ Pf 1 = 1  (so Pf last = Pf 1 = 1, Qf 0 = 1).
- hPtri: (reindex (rThr (H 0)) (rThr (H 0)) (endpointP0 Pf)).toBlocks₁₂ = 0   (endpointP0 = Pf 0 cast).
- hQtri: (reindex (pivotThr (H last) J) (pivotThr (H last) J) (endpointQL Qf)).toBlocks₂₁ = 0  (endpointQL = Qf last cast).

## Current goal state (after `set Cψ Cq M N`, L=2, H : Fin 3)
  M := reindex (rThr (H 0)) (pivotThr (H last) J) (prod H Cψ)
  N := reindex (rThr (H 0)) (pivotThr (H last) J) (prod H Cq)
  hdiff11 : (M - N).toBlocks₁₁ = 0
  hdiff12 : (M - N).toBlocks₁₂ = 0
  hdiff21 : (M - N).toBlocks₂₁ = 0

## My derived math (CONFIRMED sound by prior consult — just need the Lean)
- M - N = reindex (..)(prod Cψ - prod Cq)  [reindex subtractive].
- prod Cψ - prod Cq = reindex(Cψ 0)·reindex(Cψ 1) - reindex(Cq 0)·reindex(Cq 1)  [prod_eq_two_of_L2].
- Cψ 0 = Cq 0 (layer-0 fixed) ⟹ = reindex(C0)·[reindex(Cψ 1) - reindex(Cq 1)] = reindex(C0)·reindex(ΔC1),
  ΔC1 = Cψ 1 - Cq 1.
- ΔC1 = framedParamsPivot_last(ψq) - framedParamsPivot_last(q). Corner cancels; Pf last = 1 (hinterface);
  X,Z fixed ⟹ ΔC1 = reindex⁻¹(fromBlocks 0 ΔY 0 ΔT) · Qf last, ΔY = l2Y1p - readY, ΔT = l2T1p - core.
- reindex(M-N) via reindex_mul_split (eMid = rThr (H 1)): M - N = reindex(C0-part) · reindex(ΔC1-part).
- the RIGHT factor reindex(rThr(H1), pivotThr J)(reindex⁻¹(fromBlocks 0 ΔY 0 ΔT)·Qf last):
  the inner fromBlocks has ZERO LEFT COLUMN ({11}=0,{21}=0); right-mult by Qf last which is block-UPPER
  ({21}=0 by hQtri) PRESERVES zero {11},{21} (fromBlocks 0 b 0 d · fromBlocks a' b' 0 d' = fromBlocks 0 (b·d') 0 (d·d')).
- product fromBlocks_multiply with right factor having zero {11},{21}: the FULL product has {11}=0, {21}=0
  AUTOMATICALLY (left·0 + left·0). So hdiff11, hdiff21 are CLEAN (need only hQtri).
- {12} = leftFactor.{11}·(rightFactor.{12}) + leftFactor.{12}·(rightFactor.{22})
        = leftFactor.{11}·(ΔY·d') + leftFactor.{12}·(ΔT·d')  where d' = Qf last {22}.
  leftFactor = reindex(rThr H0, rThr H1)(reindex(C0)) where C0 = corner + Pf 0 · reindex⁻¹(fromBlocks X0 Y0 Z0 T0)
  (Qf 0 = 1). leftFactor.{11} = 1 + (Pf 0 framed){11}, leftFactor.{12} = (Pf 0 framed){12}.
  With hPtri (Pf 0 block-LOWER: {12}=0) the frame of Pf 0 does NOT mix into {12}... NEED to confirm this
  makes leftFactor.{12} = A0-row-related so e2_regPreserve closes {12}=0.

## Questions
1. Is hdiff11/hdiff21 genuinely closable with ONLY hQtri + the zero-left-column structure (no hPtri, no e2)?
   Give the exact tactic sequence (reindex subtractive → prod_eq_two_of_L2 → layer-0 cancel →
   reindex_mul_split → fromBlocks_multiply read). Name the Mathlib lemmas for "reindex of sub",
   "fromBlocks with zero left column", and the {11}/{21} extraction.
2. For hdiff12: does hPtri (Pf 0 block-lower) + hinterface + e2_regPreserve close it, and what is the
   EXACT residual identity to feed e2_regPreserve (accounting for the trailing ·d' = Qf last {22})?
   The e2 raw identity is A0·ΔY + Y0·ΔT = 0 form; with the framing, is it (frame)·(A0·ΔY+Y0·ΔT)·d' = 0?
3. The #1 cast risk: prod_eq_two_of_L2's finCongr reindexes vs the outer reindex eMid. How to make the
   eMid (= rThr (H 1)) split line up with the finCongr-wrapped middle width? The doc says: collapse
   finCongr rfl via `finCongr_refl` then `reindex_refl_refl` (erw), or compose reindexes via
   `Matrix.reindex_reindex` / `submatrix_submatrix`. Which composition lemma merges
   `reindex (finCongr rfl) (finCongr rfl) X` with the outer `reindex eR eMid`?
</task>

<output_contract>
For EACH of the 3 goals, give an ordered tactic sketch (≤ 10 lines each), naming the exact Mathlib /
banked lemma at each step. Then: the single biggest cast pitfall + the precise idiom to avoid it.
Be concrete about lemma names (mark "assumed name" if unsure). Under 600 words.
</output_contract>

<grounding_rules>
No repo. Mark inference vs certainty. If hdiff12 actually needs MORE than hPtri+hinterface+e2 (e.g.
Invertible (Pf 0) or a framed e2 variant), say so explicitly — that is a signature/lemma gap I must surface.
</grounding_rules>
