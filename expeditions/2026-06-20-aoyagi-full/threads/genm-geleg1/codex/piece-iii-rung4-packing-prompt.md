<task>
Lean 4 + Mathlib v4.29, DLN networks. Settle the CONCRETE packing design for the general-L
corner-elimination chart map `schurChartRawGen` (rung 4), so its rational two-sided inverse (rung 6)
and `recoverProductGen` (rung 5) go through. Diagnosis only, no Lean code.

L=2 REFERENCE (works, banked). Chart `schurChartRaw : BlockParamsL2 → BlockParamsL2` (same type).
Blocks: A0=[[X,Y],[Z,W]] (layer 0), A1=[[S,T],[U,V]] (layer 1). Products M11=XS+YU, M12=XT+YV,
M21=ZS+WU. Reduced cores A0red=W−ZX⁻¹Y, A1red=V−U M11⁻¹ M12. PACKING:
  out slot 0 = fromBlocks X    Y    M21  A0red
  out slot 1 = fromBlocks M11  M12  U    A1red
Two-sided rational inverse on {det X≠0}∩{det M11≠0}. `recoverProduct(out) = A0·A1` rebuilds the product:
  recoverProduct Q = fromBlocks Q.2₁₁ Q.2₁₂ Q.1₂₁ (Q.1₂₁ Q.2₁₁⁻¹ Q.2₁₂ + Q.1₂₂ Q.2₂₂)
i.e. from (M11,M12,M21, A0red·A1red) — the (2,2) corner is the reduced-core PRODUCT = Schur complement.

GENERAL-L SETUP (mine, banked). Block chain C_s : (r ⊕ (H_s−r))×(r ⊕ (H_{s+1}−r)), s=0..L−1
(genChain). Prefix products P_k = partProd C k : (r ⊕ (H_0−r))×(r ⊕ (H_k−r)), P_0=I, P_L=full.
I have (rungs 1-3): every (P_k)₁₁ invertible (prefix pivots, det≠0); reduced factors
R_k = (C_k)₂₂ − (C_k)₂₁ (P_{k+1})₁₁⁻¹ (P_{k+1})₁₂; and the telescope blockSchur(P_L) = R_0·R_1·…·R_{L−1}
(= Schur complement of full product = the reduced core). All from prefix pivots ONLY (no per-layer pivot).

TARGET: `schurChartRawGen : BlockParamsGen H r → BlockParamsGen H r` (L block-matrix slots, SAME type),
a rational C² diffeomorphism near a base point with invertible prefix pivots, whose conjugation by
blockFlatEquivGen gives the flat chart Φ, and such that a `recoverProductGen` rebuilds the reindexed
product prod (= P_L reindexed), and the loss reads off {regular directions} + {reduced core R_0···R_{L−1}}.
Free coordinate budget = the L layer slots (slot s : (r ⊕ (H_s−r))×(r ⊕ (H_{s+1}−r))).

QUESTIONS:
1. THE PACKING. Give the explicit per-slot packing of `schurChartRawGen` output (which of
   {(C_s) blocks, prefix-product corners (P_k)₁₁/₁₂/₂₁, the R_s} goes into each of the 4 sub-blocks of
   each output slot s), generalizing the L=2 packing above. It must (i) be a rational bijection on the
   prefix-pivot domain, (ii) let recoverProductGen rebuild P_L, (iii) expose the reduced core R_0···R_{L−1}
   as a readable corner. Is the "each slot s holds (C_s top rows + P_{s+1} corner info + R_s)" pattern right?
2. DEGREE-OF-FREEDOM CHECK. Confirm the packing is a bijection: the input has ∑_s dim(C_s) coords; the
   output must have the same. Does packing prefix corners + R_s exactly fill the L slots without
   over/under-determination? Where do the "regular directions" (the nReg = r·(H_0+H_L−r) count) live?
3. INVERSE STRUCTURE. Sketch how the two-sided inverse reconstructs the C_s from the packed output
   (Codex's earlier hint: suffix reconstruction clean, first layer via final P_L₂₁). Give the recursion
   direction (forward/backward) and which prefix pivots each step inverts.
4. RECURSION vs CLOSED FORM. Should schurChartRawGen be defined by recursion on L (peeling one layer,
   reusing the L=2 schurChartRaw step) or as a closed-form per-slot formula? Which makes the inverse +
   recoverProduct proofs tractable (induction reusing rungs 2-3 vs direct)? Flag the dependent-width
   cast concentration.
5. SIMPLIFICATION. Is there a SIMPLER same-type packing than mimicking L=2 slot-by-slot — e.g. one that
   makes recoverProductGen a clean fold, or avoids reconstructing intermediate P_k? What would you pick.
</task>

<output_contract>
1. PACKING: explicit per-slot 4-block layout (or the cleanest equivalent), <=10 lines.
2. DOF CHECK: bijection confirmed? where nReg lives. 2-3 sentences.
3. INVERSE: recursion direction + per-step pivot, <=6 steps.
4. DEF STYLE: recursion vs closed-form verdict + why (tractability of inverse/recoverProduct), 3-4 sentences.
5. SIMPLER OPTION: yes/no + the pick, 2-4 sentences.
Under ~450 words. Distinguish algebra-fact from Lean-effort-inference.
</output_contract>

<grounding_rules>
You can reason about the block algebra (facts). Flag as INFERENCE any claim about Lean proof effort or
what the downstream germ/interface needs (I have those; you're advising on the design).
</grounding_rules>
