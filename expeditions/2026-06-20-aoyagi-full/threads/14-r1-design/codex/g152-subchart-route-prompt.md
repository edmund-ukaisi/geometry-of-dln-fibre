<task>
Lean 4 + Mathlib v4.29 formalisation. I must discharge ONE theorem,
`deepest_gauge_chart_exists`, the heaviest remaining piece of an RLCT proof for deep
linear networks. I need a DECOMPOSITION-STRATEGY judgement, not code.

== CONTEXT ==
We prove the local RLCT (real log-canonical threshold) of the square-Frobenius loss
`dlnLoss H B : Params H → ℝ` (a polynomial, sum of squares of entries of a matrix product
`A^1···A^L − B`) at a "deepest point" w0 splits as nReg/2 + (reduced-core RLCT), where
nReg = r(H_0 + H_last − r).

`rlctAtOn F wstar : ℝ≥0∞` is defined as the sup of exponents c' for which `|F|^{-c'}` is
locally integrable near wstar (no chart, intrinsic).

We have PROVEN, general-domain lemmas (all `[MeasureSpace M][TopologicalSpace M][OpensMeasurableSpace M]`):
 - `rlctAtOn_mono F G wstar (hFmeas) (hdom : ∃U∈𝓝 wstar, ∀w∈U, |G w|≤|F w| ∧ (G w=0→F w=0)) : rlctAtOn G wstar ≤ rlctAtOn F wstar`
 - `rlctAtOn_squeeze F Φ wstar (hFmeas)(hΦmeas) c₁ c₂ (0<c₁)(0<c₂) (hsq : ∃U∈𝓝 wstar, ∀w∈U, 0≤Φ w ∧ c₁·Φ w ≤ F w ∧ F w ≤ c₂·Φ w) : rlctAtOn F wstar = rlctAtOn Φ wstar`   -- NO change of variables, NO measure Jacobian
 - `rlctAtOn_unit_invariant_aux F u wstar a b (0<a)(Measurable u)(∃U∈𝓝, a≤|u|≤b) : rlctAtOn (u·F) wstar = rlctAtOn F wstar`
 - `rlctAtOn_germ_local F G wstar (F =ᶠ[𝓝 wstar] G) : rlctAtOn F wstar = rlctAtOn G wstar`
 - `rlctAtOn_comp_homeomorph (e : M ≃ₜ M') (MeasurePreserving e)(MeasurableEmbedding e) F w : rlctAtOn (F∘e) w = rlctAtOn F (e w)`  -- requires e MEASURE-PRESERVING
 - `rlct_additive_smooth_block` : the (∑ nReg squares) + G² Fubini split → nReg/2 + rlctAtOn(G²).
 - a spectator-peel: `rlctAtOn (fun p => F p.1) (x0,y0) = rlctAtOn F x0`.
 - `paramsEquivFlat H : Params H ≃ᵐ (Fin (flatDim H) → ℝ)`, MEASURE-PRESERVING + homeomorphism.

== THE CERT (exact algebra, trusted bedrock) ==
At w0, gauge-slice each layer by `block_elimination` units P_s,Q_s (P_s (w0 s) Q_s = blockdiag[I_r,0]).
In gauge coords each layer is C_s = [[I_r+X_s, Y_s],[Z_s, T_s]], T_s the reduced (H_s−r)×(H_{s+1}−r) block.
The product ∏C_s has regular-residual blocks E = (∏C − blockdiag[I_r,0]) on the (0,0),(0,1),(1,0)
positions (Jacobian rank = nReg over the gauge regular coords), and the (1,1) reduced block.
CORRECTED finding (decorrelated Codex caught a raw-T error): on {E=0}, the reduced block is
`T̃_1···T̃_L = T·(I−VY)^{-1}·S`, the GAUGE-NORMALIZED chain (an internal gauge unit (I−VY)^{-1},
=I at w0), NOT raw `T_1 T_2`. Equivalently the product Schur complement R = P_11 − E_10(I+E_00)^{-1}E_01,
which factors as T̃_1···T̃_L. The endpoint leak E_10(I+E_00)^{-1}E_01 is reg×reg, absorbed into ∑E².
So: loss = ‖∏C − B‖²  and near w0,  loss = (∑ E_i²) + ‖T̃_1···T̃_L‖²  EXACTLY (a germ equality), with
‖T̃_1···T̃_L‖² = dlnLoss M 0 in the gauge-normalized blocks (M = H−r). The gauge chart Jacobian is a
bounded UNIT ≠ 1 (det = det(A)^{-(r+M)}·det(B)^{-M0}, A≈I_r near w0), hence NON-MP.

== THE STRUCTURE I MUST POPULATE (DeepestGaugeChart) ==
It currently demands ALL of: a literal self-homeomorphism `chart : (Fin (flatDim H)→ℝ) ≃ₜ (Fin (flatDim H)→ℝ)`;
its everywhere Fréchet derivative `Dchart` with `hasDeriv : ∀x, HasFDerivAt chart (Dchart x) x`;
`jac_unit : ∃U∈𝓝0, ∃ a b, 0<a ∧ ∀x∈U, a≤|(Dchart x).det|≤b`; `chart_zero` (chart 0 ↦ w0);
a measure-preserving reindex `split` (flat ≃ₜ regular×(core×spectators)) with `split_mp`,`split_zero`;
and `loss_form : (loss ∘ paramsEquivFlat.symm ∘ chart) =ᶠ[𝓝 0] (∑ (split x).1 i²) + dlnLoss M 0 (...(split x).2.1)`.

== THE TENSION ==
The GeneralR1 work in this very project RETIRED the measure-preserving-chart + explicit-Dchart route
in favour of `rlctAtOn_squeeze`, on the grounds that "the transvection is det-1/MP but the loss is NOT
invariant under it" — and the squeeze needs NO chart ≃ₜ, NO Dchart, NO HasFDerivAt, NO jac_unit det-bound.
The cert's content (cross-term ∈ ideal(reg), endpoint leak absorbed into ∑E²) reads to me as PRECISELY a
two-sided squeeze: flatCore and Φ=∑E²+dlnLoss M 0 differ by ideal(reg) terms that squeeze near 0.

But there is a real subtlety: the regular coords E are a NONLINEAR function of the raw flat coords
(they are product residuals). The squeeze comparison is between two functions OF THE FLAT COORDS at the
SAME point — so I still need E and the reduced core expressed as functions of the flat coords, and a
neighbourhood on which the two-sided bound holds. The GeneralR1 squeeze had the SAME issue and resolved
it per-node via an ideal-membership certificate giving the squeeze constants.
</task>

<output_contract>
Answer these, in order, tersely (this is a strategy call, not a proof):

1. ROUTE. Is `deepest_gauge_chart_exists` (i.e. populating DeepestGaugeChart) genuinely REQUIRED to
   carry the literal `chart ≃ₜ` + `Dchart` + `HasFDerivAt` + `jac_unit` measure-Jacobian — OR can the
   downstream RLCT split (nReg/2 + reduced-core RLCT) be obtained by the SQUEEZE route
   (rlctAtOn_squeeze + spectator-peel + rlct_additive_smooth_block), making the chart-≃ₜ/Dchart/jac_unit
   fields DEAD WEIGHT? Pick (A) literal-chart-needed or (B) squeeze-suffices, and say in ONE sentence why.

2. IF (B): what is the MINIMAL datum the structure should carry instead? (e.g. a measurable map
   flat→(reg coords) + flat→(core coords), nonneg, + a two-sided ideal-membership squeeze on a 𝓝 0, +
   a measurability/non-vanishing clause for the core G). Sketch the field list. Is the spectator/nGauge
   direction handled by the spectator-peel lemma, or does it still need a measure-preserving reindex?

3. THE SUBTLETY. The squeeze compares loss(flat) vs Φ(flat) where the regular coords E are nonlinear in
   flat. Concretely: is the two-sided bound `c₁·Φ ≤ loss ≤ c₂·Φ` near 0 ACTUALLY TRUE given the cert
   (cross-term ∈ ideal(reg), gauge-normalized core)? Or is there a trap where the gauge-normalization
   (I−VY)^{-1} breaks the squeeze (e.g. makes the core itself depend on reg coords, so Φ is not a clean
   ∑E² + (function of core coords alone))? Flag the single most likely way the squeeze is SUBTLY FALSE.

4. IF the squeeze IS subtly false / the literal chart genuinely needed: give the cheapest DECOMPOSITION
   of `deepest_gauge_chart_exists` into named sub-lemmas (the chart construction, the Dchart, the
   jac_unit, the loss_form germ), ordered by what to build first, with the single Mathlib API each leans on.

5. The ONE thing most likely to sink whichever route you recommend.
</output_contract>

<grounding_rules>
- Distinguish what the cert/lemma signatures STATE (fact) from your INFERENCE about Lean reachability.
- The exact algebra in the cert is TRUSTED — do not re-derive it; reason about Lean STRUCTURE only.
- If you cannot tell whether the squeeze is true from what I gave, say so and name the missing fact.
</grounding_rules>
