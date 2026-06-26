<task>
Lean 4 + Mathlib. I am building the per-node RLCT MIN fact for deep linear networks. I need to choose the
cleanest formulation of ONE glue lemma before building it. Red-team my plan for the cheapest sound route.

DEFINITIONS (all exist, proved in my repo):
- weightedThreshold G ρ K := sSup { (c':ℝ≥0) : ∃ Ω open ⊇ K, IntegrableOn (|G|^{−c'}·ρ) Ω volume }.
- rlctAtOn F w* := weightedThreshold F (ρ≡1) {w*}.
- The ambient is E = (Fin N → ℝ) with Lebesgue volume (finite-dim, IsAddHaarMeasure, BorelSpace).

EXISTING MACHINERY (all proved, in S1G5/S1G5Charts):
- pivotBlowupAt n p : (Fin(n+1)→ℝ)→(Fin(n+1)→ℝ),  φ(x)_p = x_p, φ(x)_j = x_p·x_j (j≠p).
- pivotBlowupAt_image: φ_p '' (chartDom p \ pivotZero p) = argmaxCell p, where
    argmaxCell p = {y | y p ≠ 0 ∧ ∀ j, |y j| ≤ |y p|}.
- argmaxCell_cover: {y ≠ 0} = ⋃_p argmaxCell p   (EXACT, the mk pivots cover the nonzero set).
- argmaxCell_aedisjoint: distinct cells are AEDisjoint (overlap ⊆ {|y p|=|y q|}, null by absEq_null).
- pivotBlowupDeriv_det: det Dφ_p = (x_p)^n   (the Jacobian; |det| = |x_p|^n).
- g5_flat_cover / g5_step: for a finite chart family covering U a.e.-disjointly off null sets,
    ∫⁻_U g  =  Σ_i ∫⁻_{V_i \ Z_i} ofReal|det Dφ_i| · (g ∘ φ_i).
  (the lintegral-additivity change-of-variables over the cover — PROVED.)
- weightedThreshold_le_transport: the ≤ half of transport (no surjectivity needed) — for a single
    proper/injOn-off-null/differentiable map π:  weightedThreshold F φ {w*} ≤ weightedThreshold (F∘π)
    ((φ∘π)·|det Dπ|) (π⁻¹{w*}).
- weightedProductMin_mono1D_of_ne (PROVED): weightedThreshold (y₀²·K(z)) (|y₀|^e) {(0,0)} =
    min((e+1)/2, rlctAtOn K 0).   [my per-chart threshold, e=mk−1.]

THE GOAL (the atom): for F = dlnLoss M 0 = ‖A·B‖² on the flat ambient (A is m×k, B is k×n, N=mk+kn),
  rlctAtOn F 0 = min{ mk/2 , rlctAtOn core 0 },   core = ‖Â·B‖² (the post-pivot residual),
and then (separately, via an existing squeeze) rlctAtOn core 0 = n/2 + rlctAtOn(child).

THE PLAN. Cover {A≠0} by the mk pivot charts (one per A-entry pivot (i,j)). Each chart φ_{ij},
post-pivot, gives F∘φ_{ij} = y₀²·core_{ij} with Jacobian |y₀|^{mk−1}; by weightedProductMin its
per-chart weighted threshold is min{mk/2, rlctAtOn core 0} (same value all charts, by row/col symmetry).
I want:  rlctAtOn F 0 = ⨅_{ij} (per-chart threshold) = min{mk/2, rlctAtOn core 0}.

THE GLUE LEMMA I think I need (weightedThreshold_cover_min): for a finite family of charts {φ_i} whose
images cover a punctured nbhd of w* mod null, a.e.-disjointly, with Jacobians, the weighted threshold of
F at w* equals the ⨅ over i of the per-chart weighted thresholds weightedThreshold (F∘φ_i)
(|det Dφ_i|) (φ_i⁻¹{w*}).

QUESTIONS (rank-ordered; I want the SINGLE cheapest sound route):

1. Is "weightedThreshold = ⨅ over a finite a.e.-disjoint cover of per-chart thresholds" the right
   abstraction, or is it cleaner to prove the two inequalities SEPARATELY against the target value v :=
   min{mk/2, rlctAtOn core 0}, namely:
   (LE)  rlctAtOn F 0 ≤ v   [F^{−c'}·1 integrable on a nbhd ⟹ each chart-pullback integrable ⟹ c' ≤ per-chart threshold = v]
   (GE)  v ≤ rlctAtOn F 0    [for c' < v, each chart-pullback integrable ⟹ via g5_flat_cover the sum is finite ⟹ F^{−c'} integrable on the cover nbhd]
   Which is less Lean surface: a reusable ⨅-cover lemma, or the two direct inequalities specialized to
   this F? Note all charts give the SAME value v, so the ⨅ is trivial once each chart = v.

2. THE KEY SOUNDNESS WORRY for GE. g5_flat_cover gives ∫⁻_U F^{−c'} = Σ_i ∫⁻_{V_i\Z_i} |det Dφ_i|·(F∘φ_i)^{−c'}.
   Each summand finite (c' < per-chart threshold) ⟹ the sum finite ⟹ ∫⁻_U F^{−c'} < ⊤ ⟹ integrable on U.
   But the per-chart threshold is weightedThreshold (F∘φ_i)(|det Dφ_i|)(φ_i⁻¹{w*}) — its admissibility is
   "integrable on SOME open Ω_i ∋ φ_i⁻¹{w*}", NOT on the specific V_i\Z_i that g5_flat_cover sums over.
   Is there a gap: does c' < per-chart-threshold give integrability on the PARTICULAR V_i\Z_i the cover
   uses (a bounded chart domain), or only on some chart-dependent Ω_i? How do I reconcile the cover's
   fixed domains V_i\Z_i with the threshold's existential Ω_i? (The chart domain V_i = chartDom is the
   bounded fundamental domain |x_j|≤1; the blow-up coords there are bounded, the pivot x_p free near 0.)
   Is the honest move to (a) shrink to a common small box and use monotonicity, or (b) does the
   weightedProductMin threshold's admissibility already deliver integrability on a box of the needed shape?

3. THE LE worry. ∫⁻_U F^{−c'} < ⊤ on a nbhd U of 0. Restrict to the chart image φ_i''(V_i\Z_i) ⊆ U;
   by the change-of-variables (g5_flat_cover or weightedThreshold_le_transport per chart) the pullback
   |det Dφ_i|·(F∘φ_i)^{−c'} is integrable on V_i\Z_i, hence (via weightedProductMin's threshold being a
   sSup) c' ≤ per-chart threshold = v. Is weightedThreshold_le_transport (the single-map ≤, no
   surjectivity) directly usable per chart for the LE, sidestepping a bespoke argument? The chart φ_i is
   proper? injective off pivotZero? — confirm these hold for pivotBlowupAt on the chart domain.

4. Is there a SUBTLETY with w* = 0 and φ_i⁻¹{0}? The blow-up φ_i⁻¹{0}: A=0 ⟺ y₀=0 (pivot), so the
   fibre is {x_p = 0} = pivotZero, a hyperplane (not a point). weightedProductMin is stated at the point
   (0,0). Does the per-chart threshold weightedThreshold (F∘φ_i)(|det|)(φ_i⁻¹{0}) over the HYPERPLANE
   fibre equal the at-a-point min{mk/2, rlctAtOn core 0}? Or do I need the fibre to be the point? Flag if
   the hyperplane fibre vs point-fibre mismatch is a real gap requiring care.

5. Net: give the CHEAPEST sound lemma statement(s) to build, in order, with the precise Mathlib/existing
   pieces each rests on, and FLAG any step that is a genuine new obstruction (vs assembly). If the
   hyperplane-fibre (Q4) or the domain-reconciliation (Q2) is a real wall, say so plainly.
</task>

<output_contract>
Five numbered sections (Q1–Q5). Each: a crisp verdict + one-line reason. Q5 ends with an ordered list of
the 1–3 lemma statements to build and which existing pieces discharge each, plus an explicit FLAG list of
any genuine obstructions. Under 700 words.
</output_contract>

<grounding_rules>
Distinguish theorem (provable now from the listed pieces) from a gap needing new machinery. For Q2 and
Q4 especially: if the domain-reconciliation or the hyperplane-fibre is a real mismatch, do NOT paper over
it — say it is a wall and what's needed. Flag inference vs established measure theory.
</grounding_rules>
