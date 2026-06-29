<task>
Lean 4 + Mathlib v4.29 formalisation. I am building a "D1 IFT-chart producer" module at L=2 for deep
linear networks (DLN). I need a SCOPING verdict on the cleanest honest theorem shape, given a hard
analytic gap that Mathlib lacks.

CONTEXT (the banked reduction). A file `D1ChartProducer.lean` already banks two theorems
(sorry-free, axiom-clean):

1. `deepest_le_of_optimal_chart` — given a general optimal point `v` (in the fibre `prod A = B`) at
   layer-count L=2, it CONCLUDES `rlctAt (dlnLoss H B) deepest ≤ rlctAt (dlnLoss H B) v` PROVIDED these
   inputs (m = nReg = r(H0+H2−r), Y a finite-dim flat gauge space, t0 ∈ Y, F/Q/R real functions):
     hDeepest : rlctAt (dlnLoss H B) deepest = m/2 + coreDeepest      (= the EXISTING #44 sorry; I leave it)
     hchart  : rlctAt (dlnLoss H B) v = rlctAtOn F (0, t0)            (the IFT chart transfer)
     hF      : ∀ p, F p = (∑ i, p.1 i ^2) + Q p                       (post-chart sum-of-squares form)
     hQ0     : ∀ p, 0 ≤ Q p ;  hFmeas : Measurable F
     hR      : ∀ t, R t = Q (0, t) ;  hRmeas : Measurable R
     hRne    : R a.e.-nonzero near t0
     C, hC : 0<C ;  hcmp : (∑s²)+R ≤ C·F near (0,t0)
     hCore   : coreDeepest ≤ rlctAtOn R t0
   The proof = the banked quasi-split engine `rlct_quasiSplit_ge` + `deepest_le_of_optimal_via_L2_ge`.

2. `hCore_slice_residual_eq` — discharges `hCore` WITH EQUALITY given a bounded-unit local diffeo Φ on
   an open V∋(t0,g0) with `R w = core₀ (Φ w).1` (the slice residual = reduced core pulled back along a
   bounded-unit diffeo): concludes `rlctAtOn R (t0,g0) = rlctAtOn core₀ t0`. Sorry-free, conditional on
   the diffeo data.

WHAT IS UNBUILT. The producer must, at a GENERAL optimal v (rank pattern possibly OFF the rank-exact
deepest point), construct F/Q/R/t0/Y/the chart-transfer hchart + the comparison hcmp + the diffeo data.
The analytic heart is the CONSTANT-RANK QUADRATIC SPLIT (splitting / Morse-Bott / Gromoll-Meyer): a
local diffeo φ at v with loss∘φ⁻¹(u) = u₁²+…+u_m² + R(rest). Mathlib v4.29 has NO such lemma (verified:
no Morse / Morse-Bott / Gromoll-Meyer / splitting / constant-rank quadratic decomposition). The
existing DEEPEST-POINT analog (a 2900-line construction `DeepestGaugeConstruction.lean` building the
gauge-slice chart at the rank-r-EXACT deepest point) is ITSELF still open (multiple sorries in its
`deepest_gauge_squeeze_exists`). The general-v version is strictly harder (no rank-exact pivot
structure) and is described in the expedition notes as "a major multi-tide build, rung-1-scale,
WALL-FREE but substantial."

MY CONSTRAINT. One bounded module, ideally green + sorry-free + axiom-clean. I do NOT have the budget to
re-derive the 2900-line gauge construction + the new IFT splitting to full closure. The disposition
forbids fabricating a fake closure (naming a sorry-laden thing "done") but rewards filling everything
genuinely reachable and isolating the true gap as a PRECISELY NAMED hypothesis.
</task>

<output_contract>
Answer in 4 short sections, terse:

1. VERDICT on the honest deliverable. Pick ONE:
   (A) State the producer theorem taking the genuinely-unbuildable analytic primitive(s) as NAMED
       HYPOTHESES (so the module is sorry-free + axiom-clean, and the theorem is a faithful REDUCTION
       of the producer to those named primitives), then assemble `deepest_le_of_optimal_chart`'s
       conclusion from them.
   (B) Attempt the full sorry-free construction.
   (C) Something else.
   Justify in 2-3 sentences.

2. If (A): name the MINIMAL set of hypotheses to abstract (the irreducible analytic content Mathlib
   lacks) vs what I should actually PROVE in-module (the mechanical glue). Be concrete: which of
   {the IFT diffeo existence at v, the post-chart sum-of-squares form hF, the measurability facts,
   the comparison hcmp, the diffeo bounded-unit Jacobian facts, the hRne nonvanishing} are
   "genuinely Mathlib-lacking analytic content" (→ hypothesis) vs "mechanical, provable now" (→ prove)?

3. The cleanest Lean theorem signature shape (just the shape / which args are hypotheses), so the
   conclusion is `rlctAt (dlnLoss H B) deepest ≤ rlctAt (dlnLoss H B) v` and it composes with the
   two banked theorems above.

4. Any soundness trap in stating the producer as a reduction (e.g. a hypothesis so strong it makes the
   theorem vacuous or assumes the conclusion). Flag explicitly if my hypothesis set risks circularity.
</output_contract>

<grounding_rules>
Distinguish what you can verify from the description vs what you infer. If you cannot tell whether a
given primitive is Mathlib-lacking, say so and give the cheapest check. Do not invent Mathlib lemma
names; if you reference one, mark it as "verify-first".
</grounding_rules>
