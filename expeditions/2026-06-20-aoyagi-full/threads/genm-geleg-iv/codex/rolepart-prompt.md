<task>
Lean 4 / Mathlib, DLN networks. Design the general-L "reg/core/spec role partition" for the ≥-leg
RESIDUAL strand (piece iv), generalizing an L=2 construction. Diagnosis only, no Lean code.

L=2 REFERENCE (works). The flat coords of a 2-layer tuple (block-reindexed at a common pivot ι, so
each layer s has blocks ₁₁,₁₂,₂₁,₂₂ over Fin r ⊕ Fin(H_s−r)) partition into 3 roles via an equiv
`roleEquiv : RegIdx ⊕ (CoreIdx ⊕ SpecIdx) ≃ FlatIdx H`:
- REG (the ∑p² regular block, card = nReg = r(H₀+H₂−r)): layer-0's ₂₁ (Z: (H₀−r)×r) + layer-1's ₁₁,₁₂
  (S,T: r×r, r×(H₂−r)).
- CORE (= FlatIdx(H−r), the reduced Params): layer-0's ₂₂ (W) + layer-1's ₂₂ (V) — the (2,2) blocks.
- SPEC (untouched leftover): layer-0's ₁₁,₁₂ (X,Y) + layer-1's ₂₁ (Uu).
Then `splitMP : flat ≃ (Fin nReg → ℝ) × ((core-flat) × (spec))` reindexes by roleEquiv; the residual
qₑ is the ₂₂ Schur residual, and its slice value (p=0) = the reduced-core product A0red·A1red
= dlnLoss(H−r)(coreParams+shift).

GENERAL-L SETUP (mine, all banked). L block layers C_s (s<L), each (r ⊕ (H_s−r))×(r ⊕ (H_{s+1}−r)).
Prefix products P_k=partProd C k. I have: the chart `schurChartRawGen` with packing — output slot s =
fromBlocks (P_{s+1})₁₁ (P_{s+1})₁₂ [Q_s.21] R_s, where Q_s.21 = (P_L)₂₁ at s=0 else (C_s)₂₁, and
R_s = C_s₂₂ − C_s₂₁(P_{s+1})₁₁⁻¹(P_{s+1})₁₂; the asymmetric telescope blockSchur(partProd C L) = ∏R_s
(`blockSchur_partProd_asym_fold`); recoverProductGen rebuilds the product; blockFlatEquivGen: flat ≃L
BlockParamsGen (the L block layers). nReg = r(H₀+Hᴸ−r) (same formula).

QUESTIONS:
1. THE GENERAL-L ROLE PARTITION. For the L layers, give the explicit per-layer-block role assignment
   (which of the 4 blocks ₁₁/₁₂/₂₁/₂₂ of each layer s ∈ {0,…,L−1} is REG / CORE / SPEC). The L=2 pattern
   is asymmetric (layer 0 vs layer 1 differ). What is the right general-L generalization — in particular:
   (i) CORE = all L layers' ₂₂? (ii) REG = first layer's ₂₁ + last layer's ₁₁,₁₂ (as in L=2, giving
   exactly nReg=r(H₀+Hᴸ−r))? (iii) SPEC = everything else (first layer ₁₁,₁₂; last layer ₂₁; ALL of the
   INTERIOR layers' ₁₁,₁₂,₂₁)? Verify the cardinality/DOF: does REG=r(H₀+Hᴸ−r) still hold, and do the
   interior layers contribute only CORE(₂₂)+SPEC(the other 3 blocks)?
2. CONSISTENCY WITH THE CHART. Does this partition make the chart's readout split as ∑p²(REG regular
   directions = the final (P_L)₁₁/₁₂/₂₁) + ∑qₑ²(₂₂ residual telescoping to ∏R_s)? I.e. is "REG = first
   ₂₁ + last ₁₁,₁₂" the right RAW-coord choice so the chart maps them to (P_L)₂₁,(P_L)₁₁,(P_L)₁₂? Flag if
   the interior layers' ₂₁/₁₁/₁₂ being SPEC (not REG) is correct.
3. SLICE VALUE. Confirm: at the REG-slice (p=0), qₑ's ₂₂ residual = ∏_s R_s = blockSchur(partProd C L)
   (my telescope), and this equals dlnLoss(H−r)(the reduced core = the L layers' ₂₂ blocks as a Params).
   So `hfact` (u≡1) follows from `blockSchur_partProd_asym_fold` + `recoverProductGen`. Any gap?
4. BUILD ORDER / REUSE. Should the split reuse blockFlatEquivGen (banked) or re-port an splitMP-style
   raw reindex? Give a 5-7 step build order for the general-L strand (role types → roleEquiv → split
   homeo (MP/ME) → qResid + ContDiff → slice value via telescope → e/hfact/hRne).
</task>
<output_contract>
1. ROLE PARTITION: the per-layer-block assignment table + DOF check (<=10 lines).
2. CHART CONSISTENCY: yes/no + why, esp. interior layers SPEC. (<=5 sentences)
3. SLICE VALUE: confirmed? gap? (<=4 sentences)
4. BUILD ORDER: 5-7 numbered steps, each naming banked pieces reused. Flag the one hardest step.
Under ~450 words. Distinguish algebra-fact from Lean-effort-inference.
</output_contract>
