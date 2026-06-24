<task>
Lean 4 + Mathlib v4.29. Design the cleanest STRUCTURE-FIELD shape for one issue in a gauge-chart
squeeze datum. I need the field shape, not a full proof.

CONTEXT. We compute an RLCT (real log-canonical threshold) reduction for a deep-linear-network loss.
`rlctAtOn F wstar : ℝ≥0∞` is a local invariant of `F : M → ℝ` at `wstar` (a sSup over exponents `c`
with `∫ |F|^{-c} < ⊤` near `wstar`). Key proven lemmas available:
- `rlctAtOn_comp_homeomorph (e : M ≃ₜ M') (he : MeasurePreserving e) (hemb) F w0 : rlctAtOn (F∘e) w0 = rlctAtOn F (e w0)` — MP transport.
- `rlctAtOn_squeeze (F Φ) wstar … (c₁Φ ≤ F ≤ c₂Φ near wstar, c₁,c₂>0) : rlctAtOn F wstar = rlctAtOn Φ wstar`.
- `rlctAtOn_spectator_peel (F : X→ℝ) x0 y0 (V finite-vol nbhd) : rlctAtOn (fun p:X×Y => F p.1) (x0,y0) = rlctAtOn F x0`.
- `rlct_additive_smooth_block (G:Y→ℝ) y0 … : rlctAtOn (fun p:(Fin n→ℝ)×Y => ∑p.1² + G p.2²) (0,y0) = n/2 + rlctAtOn (G²) y0`.
- `weightedThreshold_weight_unit_invariant (F φ) wstar (a b) (0<a, a≤|φ|≤b near wstar) : weightedThreshold F φ {wstar} = weightedThreshold F 1 {wstar}` — peels a bounded-unit WEIGHT.
- `weightedThreshold_transport (F φ) wstar (π Dπ E) (proper/inj-off-E/deriv/surj/null E) : weightedThreshold F 1 {wstar} = weightedThreshold (F∘π) (φ∘π · |det Dπ|) {π⁻¹ wstar}` — non-MP c-o-v deposits |det Dπ| in the WEIGHT slot.
- `rlctAtOn F w = weightedThreshold F 1 {w}` by def.

THE SETUP. `H : Fin (L+1) → ℕ` layer widths, `r` the rank, `M = fun s => H s - r` reduced widths.
`Params H = ∀ s:Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ`. `flatDim H` the flat
dimension, `paramsEquivFlat H : Params H ≃ᵐ (Fin (flatDim H) → ℝ)` the FIXED measure-preserving
flattening. `dlnLoss M 0 : Params M → ℝ` the reduced-core loss (a sum of squared entries of the
matrix product `∏ T_s`). `deepestPoint H r B … : Params H`. `wstar := (paramsEquivFlat H) deepestPoint`.

MY STRUCTURE `DeepestGaugeChart` (a squeeze datum, R-squeeze form) currently has:
- `nGauge : ℕ`
- `split : (Fin (flatDim H)→ℝ) ≃ₜ (Fin nReg→ℝ) × ((Fin (flatDim M)→ℝ) × (Fin nGauge→ℝ))` — a
  MEASURE-PRESERVING coordinate reindex (field `split_mp`), `split wstar = 0` (field `split_basepoint`).
- `loss_squeeze`: `∃ c₁ c₂>0, near wstar: c₁Φ ≤ dlnLoss H B ∘ (paramsEquivFlat H).symm ≤ c₂Φ`, where
  `Φ(w) = ∑(split w).1 i² + dlnLoss M 0 ((paramsEquivFlat M).symm (split w).2.1)`.

MY PROVEN CONSUMING LEMMAS (all on this Φ):
- sub-5: `rlctAt (dlnLoss H B) deepest = rlctAtOn Φ wstar` (rlctAtOn_eq_rlctAt + MP transport via paramsEquivFlat H + rlctAtOn_squeeze on loss_squeeze).
- sub-6: `rlctAtOn Φ wstar = nReg/2 + rlctAtOn (dlnLoss M 0) (fun _=>0 : Params M)` (split MP-transport via rlctAtOn_comp_homeomorph, then rlct_additive_smooth_block with G=√∘coreF, then spectator-peel of nGauge, then sub-7).
- sub-7: `rlctAtOn (dlnLoss M 0 ∘ (paramsEquivFlat M).symm) 0 = rlctAtOn (dlnLoss M 0) (fun _=>0)` (paramsEquivFlat M MP transport).

THE BUG (a co-builder caught it, verified by exact-numeric + Codex). `split` is a MEASURE-PRESERVING
REINDEX (a coordinate permutation). So `(split w).2.1` (the "core slot") holds the RAW matrix blocks
`T_s` of the layers. `dlnLoss M 0 ((paramsEquivFlat M).symm (raw T)) = ‖∏ T_s‖²` (the RAW reduced
chain). BUT the honest reduced core (proven correct) is the GAUGE-NORMALIZED `‖∏ T̃_s‖²` where
`T̃_s = T_s · (I − V_s Y_s)⁻¹` — the internal gauge units `(I−V_s Y_s)⁻¹` (the "g" factors, a UNIT at
wstar where V=Y=0, ≠ I nearby) absorbed = the product Schur complement. The RAW squeeze
`dlnLoss H B ≍ ∑E² + ‖∏ T_s‖²` is FALSE for matrices: `g` sits BETWEEN layers, so `‖T·g·S‖²/‖T·S‖²→∞`
as `T·S→0`. Only the gauge-normalized `‖∏ T̃‖²` works.

THE COUPLING ISSUE. `T̃_s = T_s · g_s(V_s, Y_s)` depends on the GAUGE data `V_s, Y_s` — which live in
the REGULAR/SPECTATOR slots of `split`, NOT the core slot. So the gauge-normalized core value at a
flat point `w` is a function of the FULL `w` (it reads T from the core slot AND V,Y from the other
slots), not of the core slot alone. So I cannot write `Φ`'s core as `dlnLoss M 0 (someEmbed (core
slot))` with `someEmbed` a function of the core slot only.

KEY FACTS that make a clean shape possible:
- The g-absorption is a UNIT-Jacobian change of variables: for FIXED V,Y, `T ↦ T·g(V,Y)` is LINEAR in
  T with Jacobian det `= det(g)^{M0} = det(I−VY)^{-M0}`, a UNIT (=1 at wstar).
- At wstar, `g = I` (V=Y=0), so the gauge-normalized core = raw core there; the difference is a
  germ-level unit deformation.

THE QUESTION. What is the cleanest STRUCTURE-FIELD design so that (a) `Φ` expresses the
GAUGE-NORMALIZED core (so `loss_squeeze`/the exact germ is TRUE), and (b) my sub-6 still reduces
`rlctAtOn Φ wstar` to `nReg/2 + rlctAtOn (dlnLoss M 0) (fun _=>0)` using the proven lemmas above
(possibly + `weightedThreshold_weight_unit_invariant` to peel the g-unit)?

Candidate shapes to evaluate (rank them, pick one, justify):
A. Replace the core term in Φ with an ABSTRACT field `coreVal : (Fin (flatDim H)→ℝ) → ℝ` + a field
   `coreVal_rlct : rlctAtOn coreVal wstar' = rlctAtOn (dlnLoss M 0) (fun _=>0)` for the appropriate
   basepoint, + `coreVal` factors through the core after the spectator-peel. (Does the spectator-peel
   still apply if coreVal depends on the spectator slot?)
B. Keep `Φ`'s core = `dlnLoss M 0 (coreEmbed w)` with `coreEmbed : (Fin (flatDim H)→ℝ) → Params M` a
   field reading the FULL w (T from core, g from regular/spectator), + a field asserting
   `rlctAtOn (fun w => dlnLoss M 0 (coreEmbed w)) wstar = rlctAtOn (dlnLoss M 0) (fun _=>0)`. But then
   the additive-block split (which needs Φ = ∑(reg coords)² + G(core-and-spectator-coords)²) — does
   coreEmbed reading the regular slot break the `∑reg²` additivity?
C. Make `split` NON-MP (absorb g into the reindex so the core slot already holds T̃), carrying a
   bounded-unit Jacobian field; sub-6's split-transport then uses weightedThreshold_transport +
   weight-peel instead of rlctAtOn_comp_homeomorph. (Heavier — loses the clean MP transport.)
D. A two-stage split: MP reindex to (reg, raw-core, spec), THEN a unit-Jacobian g-absorption on the
   core factor alone, peeled by weightedThreshold_weight_unit_invariant after the additive block.
   (Does the g-absorption commute with the additive-block split?)

Pick the shape that keeps the additive-block + spectator-peel + my sub-5 INTACT while making the core
gauge-normalized, with the LEAST new proof burden on the consuming side (my sub-6/7), pushing the
g-absorption obligation to the producer (the co-builder). State the exact Lean field signatures.
</task>

<output_contract>
1. RANK the four shapes (A/B/C/D) for: (i) keeping sub-5/6's additive-block + spectator-peel + MP
   transport intact, (ii) least consuming-side proof burden, (iii) cleanly pushing the g-absorption to
   the producer. One short paragraph each, then the WINNER.
2. The WINNER's exact Lean field signatures (the structure fields that change + any new field), and a
   one-line-per-step sketch of how sub-6 reduces `rlctAtOn Φ wstar` to `nReg/2 + rlctAtOn (dlnLoss M 0) 0`
   under it (which proven lemma at each step).
3. The single field the PRODUCER (co-builder) must discharge (the g-absorption / core-RLCT identity),
   stated precisely.
Keep prose tight; the deliverable is the field shape + the reduction skeleton.
</output_contract>

<grounding_rules>
You cannot run Lean. Mark any lemma name you're unsure exists at v4.29 as UNVERIFIED + give a
fallback. The proven lemmas listed above DO exist (I built them). Distinguish "this shape keeps the
proof intact" (structural inference) from "this is standard" (recalled). Do NOT invent that a lemma
does something it doesn't — e.g. the additive-block REQUIRES Φ = ∑(fresh coords)² + G(disjoint block)²,
so any shape where the core value reads the regular coords breaks it unless the regular coords are
genuinely disjoint from the core's dependence.
</grounding_rules>
