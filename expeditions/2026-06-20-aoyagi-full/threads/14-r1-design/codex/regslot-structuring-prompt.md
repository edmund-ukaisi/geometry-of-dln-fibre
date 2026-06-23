<task>
Lean 4 / Mathlib formalisation (DLN deep-linear-network RLCT). A `deepestEPivot` map and a
derivative obligation `dE(0) = ContinuousLinearMap.fst` are blocked on a coordinate-layout decision.
Adjudicate whether the fix is BOUNDED (a clean local change) or SUBSTANTIAL (a design rework), and
give the cheapest SOUND resolution.

SETUP (exact):
- Deep linear net, L layers, the "deepest point" of the loss fibre. Each layer's gauge deviation is
  a block matrix C^(s) = [[I_r + X_s, Y_s],[Z_s, T_s]] (s = 0..L-1). The gauge-normalized product is
  P = C^(0)·C^(1)···C^(L-1).
- nReg := r·(H_0 + H_L − r) = r² + r·(H_L−r) + (H_0−r)·r. This counts ONE r×r block (call it the
  "X-corner"), one r×(H_L−r) block (Y), one (H_0−r)×r block (Z). It does NOT count per-layer X_s/Y_s/Z_s.
- The combined reg+gauge index type is `RegGaugeIdx = Σ s : Fin L, (X_s ⊕ Y_s ⊕ Z_s)` — it has L
  copies of each block (one per layer). card(RegGaugeIdx) = nReg + nGauge.
- Current split: `regGaugeIdxSplit : RegGaugeIdx ≃ Fin nReg ⊕ Fin nGauge` is `Fintype.equivFin`
  (an OPAQUE arbitrary bijection by cardinality — no per-block structure).
- The downstream consumer `gaugeSlotRead` reads the STRUCTURED side (`g ⟨s, inl(inl(i,j))⟩` = X_s entry),
  so it is INVARIANT to the opaque flat ordering.
- KEY DERIVATIVE FACT (proven, "#91", general-L, idempotent-sandwich): the linearization of (P − blockNormal)
  at 0 is d(P−B)|_0 = [[Σ_s X_s, Y_L],[Z_1, 0]] — the X-corner of the derivative is the SUM Σ_s X_s
  (all layers), the Y-block is Y_{L-1} (last layer ONLY), the Z-block is Z_0 (first layer ONLY).
- `deepestEPivot : (Fin nReg → ℝ) × (Fin nGauge → ℝ) → (Fin nReg → ℝ)` is the reg-block residual of P.
- OBLIGATION: `HasStrictFDerivAt deepestEPivot (ContinuousLinearMap.fst ℝ (Fin nReg → ℝ) (Fin nGauge → ℝ)) 0`.
- CONSTRAINT (the g161 counterexample): PIN2 (a downstream loss-squeeze) needs `deepestEPivot ≈ E` where
  E is the loss residual whose linear part IS (Σ_s X_s, Y_L, Z_1). So `dE(0) = fst` must hold for the
  reg slot Fin nReg interpreted AS the boundary generators (Σ_s X_s, Y_L, Z_1), NOT an arbitrary subset.

MY ANALYSIS (red-team this): `regGaugeIdxSplit` is an Equiv (index permutation). The reg generator
"Σ_s X_s" is a SUM across L layers — a LINEAR COMBINATION of L distinct RegGaugeIdx entries, NOT a single
entry. An index Equiv can only relabel individual entries; it CANNOT produce "the reg slot = Σ_s X_s".
So the controller's proposed fix ("swap regGaugeIdxSplit from equivFin to a structured boundary-generator
equiv") is IMPOSSIBLE as an Equiv — the X-sum needs a LINEAR MAP (summing), not a relabeling. Hence the
fix is SUBSTANTIAL: deepestEPivot must apply a linear X-summing map, or the layout must change to carry
the sum. Is this analysis correct, and what is the cheapest SOUND resolution?
</task>

<output_contract>
1. VERDICT (one line): is my analysis correct that an index Equiv cannot express "reg slot = Σ_s X_s",
   making the swap substantial? YES / NO / PARTIALLY, with the crisp reason.
2. THE CHEAPEST SOUND RESOLUTION (rank options): e.g.
   (A) deepestEPivot applies a linear X-sum map before the residual read (keep regGaugeIdxSplit opaque);
   (B) restructure so the reg slot carries Σ_s X_s as a derived coordinate;
   (C) prove dE(0)=fst differently (does PIN2 actually need the literal X-SUM, or only that the
       derivative is the reg-projection in SOME basis where deepestEPivot=E holds — i.e. is there a
       basis-free CLM identity that sidesteps the sum?);
   (D) other.
   For the top option: the exact Lean construction (which CLM/LinearMap, which Mathlib lemmas), and
   whether it ripples to gaugeSlotRead / regGaugeSlotEquiv consumers.
3. BLAST RADIUS (one line): bounded (≤ ~50 LoC, no consumer ripple) vs substantial (consumer ripple /
   layout rework). 
4. The SINGLE cheapest discriminating check to confirm the verdict before building.
</output_contract>

<grounding_rules>
Flag inference vs fact. You don't have the Lean source — reason from the stated types/facts. If a claim
needs the actual `deepestEPivot` definition or PIN2's exact statement to settle, say so and name the check.
Do NOT assume Mathlib lemma names exist without flagging them as "verify".
</grounding_rules>
