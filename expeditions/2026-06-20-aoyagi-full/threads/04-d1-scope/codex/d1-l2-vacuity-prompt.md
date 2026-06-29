<task>
Lean 4 + Mathlib v4.29. I built a sorry-free, axiom-clean (propext/Classical.choice/Quot.sound)
"D1 IFT-chart producer" reduction theorem at L=2 for deep linear networks. I need a RED-TEAM on two
things: (1) circularity/soundness of the reduction, (2) the best non-vacuity witness.

THE THEOREM (paraphrased). A `structure GeneralVChartL2` over abstract finite-dim normed spaces
`Reduced`, `Gauge` bundles, for a fixed `(H, B, v, coreDeepest)` with `v` an optimal point of the DLN
loss `dlnLoss H B` (fibre `prod A = B`), `m = nReg = r·(H0+H2−r)`:
  - F, Q : (Fin m → ℝ) × (Reduced × Gauge) → ℝ ; R : Reduced × Gauge → ℝ ; t0 : Reduced ; g0 : Gauge ;
    core₀ : Reduced → ℝ
  - hchart : rlctAt (dlnLoss H B) v = rlctAtOn F (0, (t0,g0))      -- IFT chart transfer to post-chart F
  - hF     : ∀ p, F p = (∑ i, p.1 i ^2) + Q p                       -- post-chart sum-of-squares form
  - hQ0    : ∀ p, 0 ≤ Q p ; hFmeas ; hR : ∀ t, R t = Q(0,t) ; hRmeas ; hRne (R a.e.≠0 near (t0,g0))
  - C, hC>0 ; hcmp : (∑s²)+R ≤ C·F near (0,(t0,g0))
  - hcoreDeepest : coreDeepest = rlctAtOn core₀ t0                  -- ties coreDeepest to the reduced core
  - Φ, Φsymm, DΦ, DΦsymm, V (open ∋(t0,g0)), the bounded-unit local-diffeo facts, and
    hRform : ∀ w, R w = core₀ (Φ w).1   -- R = (core₀∘fst)∘Φ, the residual-core diffeo
  - hG : a positive-finite gauge nbhd

The producer theorem takes `Γ : GeneralVChartL2 …` + `hDeepest : rlctAt (dlnLoss H B) deepest =
m/2 + coreDeepest` (the existing #44 sorry, taken as a hypothesis), and CONCLUDES
`rlctAt (dlnLoss H B) deepest ≤ rlctAt (dlnLoss H B) v`. The proof: derive
`hCoreEq : rlctAtOn R (t0,g0) = rlctAtOn core₀ t0` from the diffeo (`hCore_slice_residual_eq`, banked);
then `hCore : coreDeepest ≤ rlctAtOn R (t0,g0)` = `le_of_eq (hcoreDeepest.trans hCoreEq.symm)`; then
call the banked `deepest_le_of_optimal_chart` (which internally runs the quasi-split engine to get
`hAtV : m/2 + rlctAtOn R (t0,g0) ≤ rlctAt v` from F/Q/R/hcmp, and combines with hDeepest + hCore).

The honest framing: the structure's fields are EXACTLY the obligations the unbuilt constant-rank
quadratic split (Morse-Bott/Gromoll-Meyer, Mathlib-lacking) must satisfy at general v; the theorem
certifies that GIVEN them, the D1 leg is mechanical wiring + the banked diffeo transfer.
</task>

<output_contract>
Answer terse, 3 sections:

1. CIRCULARITY / SOUNDNESS AUDIT. Does any field (or the field combination) covertly ASSUME the
   conclusion `rlctAt deepest ≤ rlctAt v`, or assume `hAtV` (the engine's job), or assume `hCore`
   directly? Check `hchart` + `hcoreDeepest` + `hRform` specifically. State PASS or a concrete defect.
   Also: is `m = nReg` tie sound (could a wrong m make it vacuously composable)?

2. VACUITY RISK. Could the field set be JOINTLY CONTRADICTORY for the real DLN loss (making the
   producer vacuously true)? If you think the fields are jointly satisfiable in principle (the G1
   verify-first found the explicit Φ:(T,g)↦((T1,(I+G(g))·T2),g), R=‖T1(I+G)T2‖²), say so; if there's a
   subtle inconsistency (e.g. hRne vs hRform vs hcmp at the basepoint), name it.

3. BEST NON-VACUITY WITNESS. `hchart` ties to the real `rlctAt (dlnLoss H B) v`, so a witness can't
   freely choose F. Recommend the cheapest HONEST non-vacuity demonstration in Lean. Options:
   (a) an `ofExactGerm`-style smart constructor: build `GeneralVChartL2` from a strictly-realizable
       weaker premise (e.g. loss already in sum-of-squares form at v + identity residual diffeo),
       analogous to the codebase's `DeepestGaugeChart.ofExactGerm`;
   (b) a concrete tiny instance (which H/B/v is computable?);
   (c) argue the witness is itself the unbuilt chart, so skip it and just document non-vacuity via the
       field-type consistency + the G1 finding.
   Rank these and give the SHAPE of the recommended one (no full Lean).
</output_contract>

<grounding_rules>
Mark inference vs fact. Do not invent Mathlib lemma names. If you cannot determine satisfiability from
the description, say which field-pair you'd check first.
</grounding_rules>
