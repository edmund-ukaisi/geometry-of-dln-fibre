<task>
Lean 4 (v4.29, Mathlib) formalisation of the ∀M Aoyagi achiever chart. Follow-up to a prior consult
that established: a PURE radial blow-up fails the rate on split-codim nodes; the genuine chart needs
the uniform Schur/`b=aβ` block-elimination structure (T_next = u·Γ − β·S), giving product = u·(...)
hence F = u²·U.

I must build `chartParamsGeneral M T* u : Params M` (∀M, opaque widths M_s·M_{s+1}) and prove
`dlnLoss M 0 (chartParamsGeneral M T* u) = u²·U` with U > 0 a.e. (the RATE), AND a det side.

TWO ROUTES to the RATE, I need you to pick the tractable one for Lean over opaque widths:

ROUTE 2a (RE-DERIVE directly): define chartParamsGeneral as explicit per-layer matrices (uniform
Schur block formulas) and prove `dlnLoss = u²·U` by a UNIFORM recursion. The product
`A_0·A_1·...·A_{L-1}` is a left-associated fold (`prodAux`, peelable by a banked `prodAux_succ`
lemma: prodAux(k+1) = prodAux(k) · reindex(A_k)). I'd prove by induction on the prefix that the
running product `prodAux M A k` is divisible by u (once we pass the deepest Schur boundary) /
factors as u·(running structure). The L=2 single-boundary case is the banked `loss_schur_blowup_factor`
(a pure `ring` on the 3×4 entries). For general L, the achiever path T* drops rank at SEVERAL
boundaries; the recursion must thread the "u·Γ − β·S" cancellation at EACH boundary.

ROUTE 2b (BRIDGE to banked): there is a banked decoder-AGNOSTIC theorem
`routeMCore_phiFlatStructV M t ha = (x p)²·V` ∀M (consumes only a GenBlk block structure + width
ineq hle + identity-boundary hC0; proven by a chain-telescope, NOT per-entry ring). To use it for my
genuine chart φ_M I must prove `φ_M = phiFlatStructV` (a map equality over opaque widths), OR show
my chartParamsGeneral's GenBlk-decoding equals the structured decoder's. A prior tide WALLED on this
"composeFold fs = phiFlatStructV" bridge: the coordinate-alignment between the chart's role-slot
decoding (chartIdxEquiv K/X/N/E slots) and the raw Params layer layout, over opaque Text/Wext widths,
proven funext-s per layer.

KEY FACTS:
- `prodAux M A : (k:ℕ) → k<L+1 → Matrix (Fin (M 0)) (Fin (M k))`, with
  `prodAux_succ : prodAux(k+1) = prodAux(k) * reindex(finCongr..) (A k)`.
- `dlnLoss M 0 A = ∑_i ∑_j (prod M A i j)²`, `prod = prodAux M A L`.
- The chart's pivot u = x_p is ONE scalar. The achiever center is the deepest point (B=0).
- I have a banked uniform `loss_schur_blowup_factor` for ONE Schur boundary (L=2, the (3,3,4) case).
- The chain telescope `chain_telescope_zero` in the banked rate engine extracts EXACTLY ONE u from
  the whole telescoped suffix regardless of how many u-carrying terms appear (so prod = u·H).

QUESTIONS:
1. For ROUTE 2a: is `dlnLoss(chartParamsGeneral) = u²·U` provable by induction on the layer prefix
   using prodAux_succ, threading the Schur cancellation per boundary — WITHOUT the chartIdxEquiv
   role-slot machinery? Specifically: can the achiever chart's per-layer matrix be defined so that
   the running prefix product `prodAux M A k` admits a CLEAN inductive invariant
   (e.g. "prodAux k = u·(frame_k) + (lower-order)" or "= u·G_k for k past the first drop") that
   the next-layer Schur block preserves? Give the invariant and the inductive step, or explain why
   the multi-boundary cancellation does NOT telescope cleanly (the per-boundary β·S cancellations
   might interfere across boundaries).
2. CRITICAL: does the order-of-vanishing stay EXACTLY 1 across multiple Schur boundaries, or does
   each additional rank-drop boundary add another power of u (giving u^{#drops} not u^1)? The rate
   needs EXACTLY u² total (F = u²·U), i.e. prod divisible by exactly u^1. If multiple boundaries each
   force a u, the single-global-pivot design is WRONG and I need per-boundary independent pivots
   (which breaks the single-axis u² rate). Settle this: for a 3-layer achiever with rank drops at
   TWO interior boundaries, sharing ONE pivot u, is the product ~ u^1 or ~ u^2?
3. Given 1+2, which route (2a re-derive by prefix induction, or 2b bridge to banked) is the
   LOWER-RISK Lean path over opaque widths? If 2a, give the cleanest inductive invariant. If neither
   is clean, what is the MINIMAL reformulation that makes the rate tractable ∀M?
</task>
<output_contract>
Answer Q1, Q2, Q3 in order. Q2 is the gating question — give a DEFINITE answer (u^1 or u^{#drops})
with a concrete 3-layer two-drop worked schematic. For Q3 name ONE route and the single cleanest
inductive invariant (Route 2a) or the single hardest bridge sub-lemma (Route 2b). Be decisive.
</output_contract>
<grounding_rules>
Flag inference vs certainty. Q2's answer is the load-bearing one — if you're inferring the vanishing
order, say so and give the schematic that would confirm it.
</grounding_rules>
