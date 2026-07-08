<task>
FOLLOW-UP with a CORRECTED premise. In a prior consult I claimed L≥3 interior frames Pf_s, Qf_s are
non-trivial (block-triangular), and you confirmed an obstruction for the framed-chain move identity.
I MISREAD a stale comment. The DATA (Lean source of the triangular frame bundle
`deepestPoint_frame_pivot_triangular_exists`) actually GUARANTEES:

  * INTERIOR frames are the IDENTITY: ∀ s, 0 < s ∧ s+1 < L → Pf_s = 1 ∧ Qf_s = 1.
  * LAYER 0 (first): Pf_0 is block-LOWER (reindex(Pf_0)₁₂ = 0) with IDENTITY ₂₂-block; Qf_0 = 1.
  * LAST layer (L−1): Pf_{L−1} = 1; Qf_{L−1} is block-UPPER (reindex(Qf)₂₁ = 0) with IDENTITY ₂₂-block.
  * Deepest boundary off-diagonals vanish: deepBlkY_0 = 0 (layer-0 (1,2)-block), deepBlkZ_{L−1} = 0
    (last-layer (2,1)-block). Also the bundle's normal-form fact: Pf_s · deepestPoint_s · Qf_s = corner
    (= reindex.symm(fromBlocks 1 0 0 0)) for every non-last layer.

So the framed chain `Cq_s = reindex(deepestChain(framedParamsPivot q)_s)` equals the FRAME-FREE decode
chain `reindex(decode(q)_s) = fromBlocks (deepBlkA_s+X_s)(deepBlkY_s+Y_s)(deepBlkZ_s+Z_s)(coreT_s)` on
ALL INTERIOR layers, and differs only at the two boundary layers by a ONE-SIDED triangular frame.

## The two germs (unchanged) that ONE psiSplitRawGen must satisfy
- GERM 1 hsub3reg (banked): needs `deepestChain(framedParamsPivot(psi q)) = movedC(deepestChain(framedParamsPivot q)) (Z0edit0)`
  — a PER-LAYER identity on the FRAMED chain Cq. movedY/movedZ/movedT are defined from Cq's OWN blocks
  (S=blockSchur, K=Kcoup via partProd Cq); the move preserves the reg residual blocks {11,12,21} of the
  full product partProd Cq L (abstract Invariants A/B, exact-verified).
- GERM 2 hsub4core (banked half): `deepestCoreF(deepestCoreAbsorbConj(psi q)).2.1 =
  frobSqMat(∏_s [(1,1)-Schur of reindex(decode(psi q)_s)])` — reads the FRAME-FREE DECODE of psi q. Must
  equal Score(x) = frobSqMat(Schur of reindex(endpointP0·(prod(decode x)−B)·endpointQL)).

## Layer-0 concrete blocks (computed)
Writing reindex(Pf_0) = fromBlocks P11 0 P21 1 (block-lower, ₂₂=1), Qf_0 = 1, and psi q's layer-0 reads
X',Y',Z',T':
  Cq'_0 = deepestChain(framed(psi q))_0 = fromBlocks (1+P11·X') (P11·Y') (P21·X'+Z') (P21·Y'+T').
The DECODE layer-0 of psi q is fromBlocks (deepBlkA_0+X')(0+Y')(deepBlkZ_0+Z')(T') (deepBlkY_0=0), and
from the normal-form fact deepBlkA_0 = P11⁻¹, deepBlkZ_0 = (reindex(Pf_0⁻¹))₂₁.

hmove FORCES (matching Cq'_0 = movedC Cq_0 blockwise): X'=X (unchanged), P11·Y' = movedY(Cq_0) so
Y' = P11⁻¹·movedY(Cq_0); P21·X'+Z' = Z0edit0 so Z' = Z0edit0 − P21·X; P21·Y'+T' = movedT(Cq_0) so
T' = movedT(Cq_0) − P21·P11⁻¹·movedY(Cq_0). These layer-0 reads are FRAME-DEPENDENT (P11, P21).
GERM 2 then reads the decode layer-0 Schur with these frame-dependent reads.

## QUESTIONS (answer each; this is the decisive re-adjudication)

1. With interior frames trivial and ONLY the two boundary layers carrying one-sided triangular frames
   (layer 0: block-lower P, ₂₂=1, Q=1; last: P=1, block-upper Q, ₂₂=1) AND the deepest boundary
   off-diagonals vanishing (deepBlkY_0=0, deepBlkZ_last=0), does the obstruction from the prior consult
   STILL hold, or does the vanishing + one-sidedness make the frame-dependent reads at the two boundary
   layers STILL consistent with GERM 2's frame-free-decode Schur = Score? Compute the layer-0 decode
   Schur core with the FORCED frame-dependent reads above and compare to blockSchur(movedC Cq_0) =
   (1−K_0)·S_0 (Invariant B). Do they agree (⟹ no obstruction) or differ (⟹ obstruction persists)?

2. If they AGREE at the boundary: is the whole framed-chain move identity then REACHABLE — i.e. does the
   frame-dependent read choice at the 2 boundary layers (plus clean decode reads on interior) give BOTH
   the framed movedC (GERM 1) AND the frame-free decode Schur product = Score (GERM 2)? Note Score itself
   uses ENDPOINT frames endpointP0/endpointQL (block-lower/upper, ₂₂=1), which are the SAME boundary
   frames — so any boundary frame factor in the decode Schur may be exactly cancelled by the endpoint
   frame in Score's definition. Assess whether this cancellation closes the loop.

3. Verdict: REACHABLE-AS-BANKED / NEEDS-REARCHITECT / UNSURE-NEED-X. If REACHABLE, name the key lemma(s)
   (boundary-layer Schur/frame cancellation) that must be proven and estimate whether it is bounded
   plumbing or new math. If still NEEDS-REARCHITECT, give the crisp reason the boundary frames obstruct
   despite the vanishing.
</task>

<output_contract>
Three numbered sections. Q1: compute the layer-0 decode Schur core with the forced reads and state
AGREE/DIFFER with a one-line algebraic reason. Q3: one verdict tag. Under ~600 words. Flag INFERENCE vs
computed-from-given-algebra at each step.
</output_contract>

<grounding_rules>
The corrected block algebra above is given as fact from Lean source. The prior obstruction was under
NON-trivial interior frames; that premise is now retracted. Re-adjudicate honestly for the corrected
boundary-only-frame regime. If you need a fact I didn't give (e.g. the exact relation between movedZ at
layer 0 / Z0edit0 and the frame), state the assumption and branch.
</grounding_rules>
