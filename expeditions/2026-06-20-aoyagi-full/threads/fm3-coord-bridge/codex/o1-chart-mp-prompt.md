<task>
Lean 4 + Mathlib, deep-linear-network RLCT. I need to adjudicate whether a banked lemma's hypothesis
is SATISFIABLE at a real node, or whether the lemma is effectively VACUOUS (a subtle soundness/usability
flaw). This is a yes/no architecture question with a concrete worked example.

THE LEMMA (banked, green, sorry-free):
  dlnLoss_chart_squeeze_descent (chart : ((Fin nReg → ℝ) × Y) ≃ₜ Params M)
    (hmp : MeasurePreserving chart volume volume) (hemb : MeasurableEmbedding chart)
    (G : Y → ℝ) ... (c₁ c₂ : ℝ) (hc₁ hc₂ : 0 < ·)
    (hsq : ∃ U ∈ nhds (0,0), ∀ w ∈ U, 0 ≤ Φ w ∧ c₁·Φ w ≤ dlnLoss M 0 (chart w) ∧ dlnLoss M 0 (chart w) ≤ c₂·Φ w)
    : rlctAtOn (dlnLoss M 0) (chart (0,0)) = nReg/2 + rlctAtOn (G²) 0
  where Φ w = smoothBlockSplitForm G w = (∑ⱼ w.1ⱼ²) + G(w.2)².
  Proof: rw [← rlctAtOn_comp_homeomorph chart hmp hemb (dlnLoss M 0) (0,0)]; exact schur_recursion_step_squeeze ...
  (i.e. transport dlnLoss to the chart SOURCE via the MP homeomorphism, then apply the chart-free squeeze).

THE CONCERN (an Explore agent flagged it, I must verify or refute):
For the (2,2,2) network, the RLCT is computed via the A-PIVOT BLOW-UP `step1A : (Fin 8→ℝ)→(Fin 8→ℝ)`,
`step1A y = ![y0, y0·y1, y0·y2, y0·y3, y4..y7]`, which has Jacobian determinant `|det| = y0³` — so step1A
is NOT measure-preserving. The agent concluded: "dlnLoss_chart_squeeze_descent requires a MEASURE-PRESERVING
chart, but the only available (2,2,2) chart (the blow-up) is non-MP, so the lemma is INCOMPATIBLE with the
(2,2,2) proof / its hmp hypothesis is unsatisfiable → the lemma may be vacuous."

MY COUNTER-HYPOTHESIS (which I need you to confirm or refute):
The `chart` in my lemma is NOT the blow-up. It is a measure-preserving COORDINATE homeomorphism
`Params M ≃ₜ (Fin nReg → ℝ) × Y` (the analog of the existing `paramsEquivFlat M : Params M ≃ᵐ (Fin (flatDim M) → ℝ)`,
which IS measure-preserving — it's just a reindexing/currying of coordinates, det 1). The BLOW-UP's Jacobian
`y0³` does NOT live in `chart`; it lives INSIDE the function `G` (and the squeeze): after the MP coordinate
chart, `dlnLoss M 0 ∘ chart` is the loss in flat product coordinates, and the SQUEEZE
`c₁·Φ ≤ dlnLoss∘chart ≤ c₂·Φ` is a pointwise inequality near (0,0) — NO change of variables, NO Jacobian.
The squeeze is the per-node Schur normal-form bound (`flatCore − Φ ∈ ideal(regular gens)`), which the
(2,2,2) hnode cert verifies as an EXACT identity: `core = ∑Erow² + ‖bcol·Erow + SΓ‖²` (so c₁=c₂=1 there,
modulo the unit). The blow-up `y0³` is a SEPARATE step that the COVER handles (the residual G's rlct,
`rlctAtOn (G²) 0` = the child cover) — it is NOT part of the chart-squeeze descent.

So my claim: the MP chart IS satisfiable (it's the coordinate reindex `paramsEquivFlat`-style, MP/det-1),
the squeeze IS satisfiable (the Schur normal-form bound, the cert's exact identity), and the blow-up
Jacobian correctly lives downstream in `rlctAtOn(G²)` (the child), NOT in the chart. The lemma is sound
and instantiable. The Explore agent CONFLATED "the chart" with "the blow-up".

WHICH IS RIGHT?
</task>

<output_contract>
Terse, these sections:

1. VERDICT (1 line): Is the lemma's MP-chart hypothesis SATISFIABLE for a real blow-up node (so the lemma
   is sound + usable), or is the Explore agent right that it's effectively vacuous/incompatible? Pick one.

2. THE CHART vs THE BLOW-UP (1 para): Are these genuinely separate maps (my view), or is the agent right
   that the only Params-decomposition for (2,2,2) IS the non-MP blow-up? Specifically: does a MEASURE-
   PRESERVING product homeomorphism `Params M ≃ₜ (Fin nReg → ℝ) × Y` exist (a coordinate reindex), and is the
   blow-up Jacobian y0³ correctly downstream (inside G / the cover), NOT in this chart? Or does the squeeze
   `c₁·Φ ≤ dlnLoss∘chart ≤ c₂·Φ` SECRETLY require the blow-up (i.e. dlnLoss∘chart is NOT squeezable by a
   smooth-block form without first blowing up, so the chart can't be just a reindex)?

3. THE REAL LOCATION OF y0³ (the crux): In the squeeze route, where does the blow-up Jacobian y0³ go? Is it
   (a) absorbed into rlctAtOn(G²) downstream (the child's contribution — my view), or (b) genuinely required
   in the transport from dlnLoss to the squeezable form (so the MP chart is insufficient and the agent is
   right)? Reason from: rlctAtOn is a threshold of ∫|F|^{-c}, scale-invariant under MP maps; the blow-up
   changes the integral by the y0³ weight, which SHIFTS the threshold — so does the squeeze route capture
   that shift via G, or does it MISS it (making the lemma compute the wrong rlct)?

4. IF VACUOUS — THE FIX (1 para, only if section 1 says vacuous/flawed): what's the minimal correction? A
   non-MP chart variant with explicit Jacobian (rlctAtOn_comp_blowup with a y0³-weight)? Or is the squeeze
   route fundamentally the wrong tool and the cover-lintegral route (Jacobian in the integrand) is the only
   sound one for blow-up nodes?
</output_contract>

<grounding_rules>
You cannot see my files — flag inference vs derivable fact. The CRUX is section 3 (where y0³ goes): reason
it out from RLCT scaling, don't hand-wave. If my counter-hypothesis is WRONG (the squeeze route misses the
blow-up shift), SAY SO PLAINLY — that means my banked dlnLoss_O1_descent computes the wrong value at blow-up
nodes and needs a Jacobian-aware fix, which is the most valuable possible finding (catching a subtle
soundness flaw before building weeks of producer on it).
</grounding_rules>
