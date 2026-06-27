<task>
Lean 4 + Mathlib. I am building the GE (≥) direction of a per-node RLCT cover for deep linear networks.
Red-team the cleanest lemma shape before I build ~250 lines, focusing on the domain-clipping you
flagged earlier.

GOAL (GE leg): rlctAtOn F 0 ≥ min{ mk/2 , rlctAtOn core 0 }, where F = dlnLoss M 0 = ‖A·B‖² on the
flat ambient E = (Fin N → ℝ), N = mk + kn. Equivalently: for every c' < min{mk/2, rlctAtOn core 0},
there is an open Ω ∋ 0 with |F|^{−c'} integrable on Ω (so c' is admissible, hence ≤ rlctAtOn F 0).

PROVED PIECES I have:
- boxpm_integrableOn_of_lt: c' < (e+1)/2 (e=mk−1) ∧ |core|^{−c'} integrable on a core-box Vz ⟹ the
  pullback |y₀²·core|^{−c'}·|y₀|^e integrable on Iy ×ˢ Vz (Iy bounded). [the per-chart box feed]
- dlnLoss_nodeBlowup_factor: F∘(scale layer-0 by y₀) = y₀²·core (core = ‖Â·B‖², the post-pivot residual).
- flatIdx_layer0_card: the layer-0 flat block has mk coords ⟹ pivotBlowupOnDeriv_det = y₀^{mk−1}.
- pivotBlowupOn / its hasFDerivWithinAt / injOn (off {x_p=0}) / image (= argmaxCellOn) / deriv det.
- argmaxCellOn_cover: {y | ∃ j∈active, y j ≠ 0} = ⋃_{p∈active} argmaxCellOn active p  (EXACT).
- argmaxCellOn_aedisjoint: distinct cells AEDisjoint (overlap null via absEq_null).
- g5_flat_cover: for a finite chart family covering U a.e.-disjointly off null sets,
    ∫⁻_U g = Σ_i ∫⁻_{V_i\N_i} ofReal|det Dφ_i|·(g∘φ_i).   [E NormedAddCommGroup + IsAddHaarMeasure]
- core_admissible_of_lt: c' < rlctAtOn core 0 ⟹ |core|^{−c'} integrable on some open Ω_core ∋ 0.
- weightedThreshold/rlctAtOn: rlctAtOn F 0 = sSup{c' : |F|^{−c'} integrable on some open Ω ∋ 0}.

THE DOMAIN-CLIPPING ISSUE you flagged earlier: the chart images argmaxCellOn are UNBOUNDED (pivot
free); the cover is of {A≠0}, not of a bounded nbhd of 0. core_admissible_of_lt gives integrability on
SOME open Ω_core, not on the specific core-box the cover sums over. I need to reconcile: (a) localize F's
RLCT to a bounded box Ω, (b) cover Ω∩{A≠0} (≈ Ω mod the null {A=0}) by clipped charts V_p ∩ φ_p⁻¹'Ω \ Z_p,
(c) each clipped summand integrable via boxpm_integrableOn_of_lt — but its domain is Iy ×ˢ Vz, and the
clipped chart domain V_p ∩ φ_p⁻¹'Ω may not be a clean rectangle.

QUESTIONS (rank-ordered, cheapest sound route):

1. For the GE leg, is it cleaner to (A) use g5_flat_cover to get the EXACT equality ∫_Ω F^{−c'} = Σ
   summands then bound each, OR (B) avoid the cover equality entirely and use a DIRECT domination:
   pick Ω = a bounded box, and show |F|^{−c'} integrable on Ω by dominating ∫_Ω directly — e.g. since
   the mk argmax cells cover Ω∩{A≠0} and {A=0} is null, ∫_Ω = ∫_{Ω∩{A≠0}} ≤ Σ_p ∫_{Ω∩cell_p}, and each
   ∫_{Ω∩cell_p} transports (change of variables on the chart) to a bounded-chart-box integral handled
   by boxpm_integrableOn_of_lt? Which has less Lean surface — the exact g5_flat_cover equality, or a
   sub-additive domination (lintegral_iUnion_le / measure_biUnion_le style)?

2. THE CLIPPED-DOMAIN RECTANGLE worry. boxpm_integrableOn_of_lt wants the chart-pullback domain to be
   a rectangle Iy ×ˢ Vz (Iy the pivot interval, Vz the core-coords box). The clipped chart domain
   V_p ∩ φ_p⁻¹'Ω: φ_p is pivotBlowupOn (pivot y₀ = x_p free, active j≠p ↦ x_p·x_j bounded |x_j|≤1,
   spectators = the kn B-coords). Is φ_p⁻¹'(bounded box Ω) a rectangle in (pivot, active-rest, spectator)
   coords? The pullback of {|A_ij|≤r} under A_ij = y₀·x_ij is {|y₀·x_ij|≤r} — NOT a rectangle (couples
   y₀ and x_ij). Is this a real obstruction to using boxpm_integrableOn_of_lt's rectangle form, or can I
   (i) enlarge: drop the Ω-clip and integrate over the FULL bounded chart domain chartDomOn ∩ {|y₀|≤R}
   (a rectangle: |x_j|≤1 active, |y₀|≤R, spectators in a box) which CONTAINS the clipped domain, then
   monotonicity ∫_clipped ≤ ∫_rectangle < ⊤? Confirm the enlargement preserves finiteness and that
   chartDomOn∩{|y₀|≤R}∩{spectators bounded} IS a rectangle Iy ×ˢ Vz with Iy=[−R,R]∋pivot and
   Vz = (active box)×(spectator box).

3. THE CORE-BOX worry. boxpm needs |core|^{−c'} integrable on the core-box Vz = (active-rest box)×
   (spectator box). core = ‖Â·B‖² with Â having the unit pivot and the active-rest as its other entries,
   B the spectators. core_admissible_of_lt gives integrability on SOME open Ω_core ∋ 0 (0 = deepest core
   point). Is the core-box Vz (a specific bounded box around 0) inside Ω_core after shrinking? I.e. can I
   shrink the whole construction (R small, active/spectator boxes small) so Vz ⊆ Ω_core? Is "shrink Ω
   and the chart boxes to fit inside the core's admissible nbhd" sound and standard, or does the
   pivot-blow-up coupling break the shrink (the chart maps a small chart-box to a small A-nbhd only if
   y₀ small AND active bounded — confirm the image of a small rectangle is a small A-nbhd)?

4. Is there a cleaner ABSTRACT GE lemma to state first (over an abstract finite chart family with the
   box facts as hypotheses), provable from g5_flat_cover + finite-sum-finiteness, that I then instantiate
   with the mk pivot charts? Or is the instantiation (the mk charts, the argmaxCellOn re-index over flat
   coords, the spectator/active split) so entangled that a direct proof is cleaner? Give the cheapest
   sound lemma statement(s) in order, flagging any genuine obstruction (esp. Q2 rectangle, Q3 shrink).

5. Net: is the GE leg SOUND ASSEMBLY (composes the proved pieces, ~250L) or does Q2/Q3 hide a wall?
   If a wall, name it precisely (what new machinery). If assembly, give the 2-3 lemma statements + the
   key Mathlib pieces (lintegral cover bound / monotonicity / shrink) each rests on.
</task>

<output_contract>
Five numbered sections (Q1–Q5). Each: a crisp verdict (CLEANER-A/CLEANER-B, RECTANGLE-OK/WALL,
SHRINK-OK/WALL, ABSTRACT/DIRECT, ASSEMBLY/WALL) + one-line reason. Q5 ends with the ordered lemma
statements to build + the Mathlib piece each rests on, and an explicit FLAG list of obstructions.
Under 700 words.
</output_contract>

<grounding_rules>
Distinguish theorem (provable from the listed pieces) from a gap needing new machinery. For Q2 (the
rectangle-pullback) and Q3 (the shrink-into-admissible-nbhd): if either is a real obstruction, say WALL
and what is needed; do not paper over the y₀–active coupling. Flag inference vs established measure theory.
</grounding_rules>
