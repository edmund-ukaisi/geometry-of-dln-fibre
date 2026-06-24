<task>
Lean 4 + Mathlib v4.29 (DLN-fibre). I'm wiring `deepest_loss_squeeze` (the L2 geometric heart) around
banked leaf lemmas + ONE frame-bridge hypothesis. I need the EXACT shape of that hypothesis + the
per-`w` chain tactic-sequence, so the ~120-150 line assembly is right first time. Give the hypothesis
+ skeleton; flag the one step most likely to wall.

THE GOAL (deepest_loss_squeeze):
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ U ∈ 𝓝 wstar, ∀ w ∈ U,
    0 ≤ Φ(w) ∧ c₁·Φ(w) ≤ dlnLoss H B (paramsSymm w) ∧ dlnLoss H B (paramsSymm w) ≤ c₂·Φ(w)
  where Φ(w) = (∑ i, (regStraighten (split w)).1 i ^2) + deepestCoreF H r (coreAbsorb (split w)).2.1,
  paramsSymm := (paramsEquivFlat H).symm, wstar = paramsEquivFlat (deepestPoint …).
  dlnLoss H B A = ∑ i, ∑ j, ((prod H A − B) i j)^2.

HYPOTHESES already in the signature: hsplit_base (split wstar = 0), hregval (∀ q, (regStraighten q).1 =
deepestEPivot H r hr hL (q.1, q.2.2)), hcoreabs (coreAbsorb = deepestCoreAbsorb H r hr hL).

BANKED LEAF LEMMAS (clean-three, to consume):
- dlnLoss_two_sided_of_frame (N P0 QL Pi Qi) (hP: Pi·P0=1) (hQ: QL·Qi=1) (e₁ e₂) (P00 P01 P10 P11)
  [Invertible P00] (t) (hconj: reindex e₁ e₂ (P0·N·QL) = fromBlocks (P00−1) P01 P10 P11) (hleak) :
  (∑E² + ‖Rcore‖²) ≤ (2(1+t²)·(∑P0²·∑QL²))·∑N²  ∧  ∑N² ≤ (∑Pi²·∑Qi²)·((2+2t²)·(∑E²+‖Rcore‖²)).
  [E = (P00−1,P01,P10) energies, Rcore = P11−P10·⅟P00·P01, N : Matrix (Fin (H 0)) (Fin (H last))]
- deepestEPivot_sq_sum_eq_blocks (p) : ∑ i, (deepestEPivot p i)^2 = ∑(P_p.toBlocks₁₁−1)² + (∑P_p.toBlocks₁₂²
  + ∑P_p.toBlocks₂₁²)  where P_p = reindex (rThresholdSplit r (H 0)) (rThresholdSplit r (H last))
  (prod H (framedParamsReg p)). [the Φ-reg-id: ∑(regStraighten(split w)).1² = ∑(deepestEPivot (split w))²
  via hregval, = the framed reg-residual block energies]
- deepestCoreF H r y = dlnLoss (deepestM H r) 0 (paramsSymm-of-deepestM y) [the reduced-network loss; the
  Schur core ‖Rcore‖² should = deepestCoreF (coreAbsorb(split w)).2.1 — this is the core-id, the OTHER
  geometric piece; treat as part of the bridge].
- deepestPoint_frame s : (P_s, Q_s) units (deepestPoint_frame_invertible); endpoint_telescoping (sorry-free,
  IsUnit-exposing): given per-layer frames + hframe (C s = P s·A s·Q s) + hinterface (interior=1) →
  ∃ P0 QL, prod C = P0·prod A·QL ∧ (IsUnit-given → IsUnit P0 ∧ IsUnit QL).
- prod_paramsEquivFlat, dlnLoss_nonneg.

THE FRAME-BRIDGE (the ONE non-leaf input — I'll state it as a hypothesis hframe_bridge, threaded from the
construction where split = deepestSplit, sorry'd there as the g164/g222 cert): the per-`w` relation that
prod(paramsSymm w) conjugates to the framed product. QUESTION: what's the CLEANEST hframe_bridge shape that
(a) feeds dlnLoss_two_sided_of_frame's hconj for N_w = prod(paramsSymm w)−B, AND (b) gives the block-energy
identification ∑E² = ∑(deepestEPivot(split w))² [reg] + ‖Rcore‖² = deepestCoreF(coreAbsorb(split w)).2.1
[core]? Options: (i) hframe_bridge per-w: reindex e₁ e₂ (P0·(prod(paramsSymm w)−B)·QL) = fromBlocks
((P11_w)−1) (P12_w) (P21_w) (T_w) with P11_w/.. = the deepestEPivot blocks of split w + T_w the core; (ii)
the per-layer framedParams(split w) s = P_s·(paramsSymm w) s·Q_s + let endpoint_telescoping + block-algebra
derive hconj; (iii) something tighter.
</task>

<output_contract>
1. The EXACT `hframe_bridge` hypothesis (Lean type) — the minimal shape that feeds both hconj and the
   block-energy IDs. Prefer the one that makes the leaf wire shortest.
2. The deepest_loss_squeeze skeleton: the c₁/c₂ choice (from dlnLoss_two_sided_of_frame's constants +
   frame energies), the U choice, the per-w chain (obtain the bridge → dlnLoss_two_sided_of_frame →
   rewrite ∑E²/‖Rcore‖² to Φ via deepestEPivot_sq_sum_eq_blocks + hregval + the core-id + hcoreabs →
   the two ≤ + the 0 ≤). Name the banked lemma each step uses.
3. The ONE step most likely to wall (the leak hleak? the c₁ positivity from frame-energy? the core-id
   ‖Rcore‖²=deepestCoreF?) + the fallback.
Under ~650 words, Lean-concrete.
</output_contract>

<grounding_rules>
Flag any Mathlib/DLNFibre lemma you're unsure exists as "(verify)". Distinguish "this closes it" from
"this probably works". If the core-id (‖Rcore‖²=deepestCoreF) is itself a separate geometric cert (not
derivable from hframe_bridge), say so — it may be a SECOND bridge piece.
</grounding_rules>
