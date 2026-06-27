<task>
Lean 4 / Mathlib v4.29. I must construct a `DeepestGaugeChart` instance (the producer side of an RLCT
proof). The algebra is fully banked (5 GREEN matrix lemmas); I need the cleanest LEAN CONSTRUCTION
STRATEGY for the two homeomorphisms + their measure/RLCT properties, before sinking hundreds of lines.

THE TARGET (existential, I supply all fields):
∃ (nGauge : ℕ) (split : (Fin N → ℝ) ≃ₜ DeepestSplit) (coreAbsorb : DeepestSplit ≃ₜ DeepestSplit),
  MeasurePreserving split volume volume ∧ split (flatDeepest) = 0 ∧
  coreAbsorb 0 = 0 ∧ (∀q, (coreAbsorb q).1 = q.1) ∧ (∀q, (coreAbsorb q).2.2 = q.2.2) ∧
  (coreAbsorb_rlct: rlctAtOn (∑reg² + coreF (coreAbsorb q).2.1) 0 = rlctAtOn (∑reg² + coreF q.2.1) 0) ∧
  (loss_squeeze: ∃ c₁ c₂>0, ∃U∈𝓝 flatDeepest, ∀w∈U, c₁Φ ≤ dlnLoss∘flatSymm w ≤ c₂Φ,
     Φ = ∑(split w).1² + coreF (coreAbsorb (split w)).2.1)
where DeepestSplit = (Fin nReg→ℝ) × ((Fin (flatDim M)→ℝ) × (Fin nGauge→ℝ)), N = flatDim H,
coreF y = dlnLoss M 0 (paramsEquivFlatM.symm y), flatDeepest = paramsEquivFlatH (deepestPoint).

BANKED (GREEN, reusable):
- core_comparability_squeeze: given P11=leak+R and ∑leak²≤t²∑E², gives c₁(∑E²+‖R‖²)≤∑E²+‖P11‖²≤c₂(...).
- layer_schur_blockDiag: L·C·R = blockdiag[(1+X), S], S=T−Z(1+X)⁻¹Y (per-layer Schur).
- frobenius_fromBlocks, schur_P11_decomp, twofactor_block_product.
- paramsEquivFlat H : Params H ≃ᵐ (Fin (flatDim H)→ℝ), MP + homeo (measurePreserving_paramsEquivFlat).
- block_elimination: ∃ P Q units, P·B·Q = blockdiag[I_r,0] (on the rank-r product B).
- weightedThreshold_weight_unit_invariant: peels a bounded-unit weight φ from rlctAtOn.
- weightedThreshold_transport: c-o-v π (proper a.e.-diffeo) deposits |det Dπ| weight.
- rlctAtOn_comp_homeomorph: MP homeo transports rlctAtOn (det=1 case).

KEY FACTS established (decorrelated, trusted):
- split is the block_elimination-on-PRODUCT-B MP reindex (boundary gauge, nReg=r(H0+Hlast−r) regular dirs;
  interior gauge = nGauge spectators; core slot = raw T blocks). MP (it's a coordinate reindex/relabel).
- coreAbsorb core-output = the FULL-product Schur R (NOT per-layer ∏S_s). It factors: (a) per-layer Schur
  shear T→S [additive, det=1, MP] + (b) the inter-layer unit [∏S_s → R, non-MP, the coreAbsorb_rlct peel].
- loss_squeeze ← core_comparability_squeeze directly (the SQUEEZE, c₁=(2(1+t²))⁻¹, c₂=2+2t²).
</task>

<output_contract>
Terse strategy guidance (this is a build-plan sanity pass, not a proof):
1. SPLIT: cleanest Lean route to build `split : Flat ≃ₜ DeepestSplit` + MP, given it's a coordinate
   reindex induced by block_elimination's units. Is it: (i) a linear MeasurableEquiv (matmul by the
   P,Q units + a Fin-reindex, MP via volume_preserving_arrowCongr'-style), or (ii) something needing
   the full paramsEquivFlat composition? What's the dimension-bookkeeping pain (nReg+flatDim M+nGauge = N)?
   The single biggest Lean risk in split.
2. COREABSORB: should it be ONE map (R-output, factoring a+b internally) or should I make coreAbsorb
   the MP shear (a) ALONE and handle (b) the inter-layer unit inside coreAbsorb_rlct's weight-peel? The
   latter keeps coreAbsorb MP (trivial _rlct via comp_homeomorph for part a) and isolates the non-MP (b).
   Which factoring minimizes Lean pain?
3. COREABSORB_RLCT: the exact chain — weightedThreshold_transport (deposit |det| of the (b) inter-layer
   unit) + weightedThreshold_weight_unit_invariant (peel it). What must I show about the (b) unit's det
   (bounded in [a,b], a>0, near 0)? Is the inter-layer unit's det a clean det(I−VY)^k I can bound?
4. LOSS_SQUEEZE: wiring core_comparability_squeeze through split+coreAbsorb. The hleak hypothesis
   (∑leak²≤t²∑E²) discharge — leak=E10(I+E00)⁻¹E01, need it bounded by t²∑E² near 0. Cleanest Lean route
   (Frobenius submultiplicativity? bounded (I+E00)⁻¹ near 0? continuity?). Is this the hardest sub-piece?
5. ORDERING: which of {split, coreAbsorb, coreAbsorb_rlct, loss_squeeze} to build first, and the single
   piece most likely to wall (where I should consult/pair early).
</output_contract>

<grounding_rules>
Strategy only — don't write the proofs. Distinguish "Mathlib has this" (name it) from "needs building".
Flag the single biggest risk per piece. If split-as-linear-MeasurableEquiv is clean, say so; if the
dimension bookkeeping (the Fin reindex nReg⊕flatDimM⊕nGauge ≃ flatDim H) is the pain, flag it.
