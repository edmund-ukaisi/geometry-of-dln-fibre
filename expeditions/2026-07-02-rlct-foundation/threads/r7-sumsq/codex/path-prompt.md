<task>
Lean 4 + Mathlib (pin v4.29.0). I must prove, cite-free and sorry-free, the RLCT of a
nondegenerate quadratic (sum of squares) in C variables equals C/2.

DEFINITIONS (already in the repo, fixed — I cannot change them):

  negPow K c : (Fin n → ℝ) → ℝ := fun x ↦ (K x) ^ (-c)          -- Real.rpow
  localAdmissibleExponents K x : Set ℝ := {c | 0 ≤ c ∧ IntegrableAtFilter (negPow K c) (𝓝 x)}
      -- IntegrableAtFilter f (𝓝 x) := ∃ s ∈ 𝓝 x, IntegrableOn f s   (integrable on SOME nbhd)
      -- measure is `volume` on (Fin n → ℝ)  (Lebesgue, MeasureTheory.volume via the Pi measure)
  rlctAt K x : ℝ := sSup (localAdmissibleExponents K x)

TARGET (C : ℕ, 1 ≤ C):
  Q : (Fin C → ℝ) → ℝ := fun y ↦ ∑ i, (y i)^2      -- = ‖y‖²_{ℓ²}
  GOAL:  rlctAt Q 0 = (C : ℝ) / 2

The math is standard: Q^(-c)(y) = ‖y‖^(-2c); local integrability at 0 in ℝ^C holds iff 2c < C
(polar coords: ∫_ball r^{-2c} r^{C-1} dr converges at 0 iff C-1-2c > -1). Boundary c = C/2 is
NON-integrable but sSup = C/2 either way. So localAdmissibleExponents Q 0 = Ico 0 (C/2) up to the
boundary point, and rlctAt Q 0 = C/2.

MATHLIB TOOLS I have found (v4.29):
  - integrableOn_Ioo_rpow_iff (ht : 0 < t) : IntegrableOn (fun x ↦ x^s) (Ioo 0 t) ↔ -1 < s
      -- the 1-D LOCAL threshold (bounded interval near 0). This is the clean local building block.
  - MeasureTheory.integrable_fun_norm_addHaar {f : ℝ → F} [Nontrivial E] [FiniteDimensional ℝ E]
      [BorelSpace E] [μ.IsAddHaarMeasure] :
        Integrable (fun x ↦ f ‖x‖) μ ↔ IntegrableOn (fun y : ℝ ↦ y^(dim E - 1) • f y) (Ioi 0)
      -- polar-coord reduction, but this is GLOBAL integrability over the whole space, not on a ball.
      -- dim E - 1 is ℕ subtraction; f : ℝ → F is radial. norm here is the E-norm.
  - integrableOn_Ioi_rpow_iff (ht : 0 < t) : IntegrableOn (fun x ↦ x^s) (Ioi t) ↔ s < -1

KEY TENSIONS I need adjudicated:
  1. The `norm` in integrable_fun_norm_addHaar is the E-norm. My Q = ∑(y i)^2 is the SQUARED ℓ²
     norm. On `Fin C → ℝ` (Pi type) the default norm is the SUP norm, not ℓ². On
     `EuclideanSpace ℝ (Fin C)` the norm IS ℓ². But Q is stated on `Fin C → ℝ`. Volumes agree
     (EuclideanSpace is defeq Pi with a different norm instance), but ‖·‖ differs.
     Q: which carrier should I do the analysis on, and what is the cleanest transport?
     Is `Q y = ‖(y : EuclideanSpace ℝ (Fin C))‖^2` provable by a clean lemma
     (EuclideanSpace.norm_eq / ∑ sq)? Does `volume` transport cleanly?
  2. integrable_fun_norm_addHaar is GLOBAL (over μ = whole space). I need LOCAL (IntegrableAtFilter
     (𝓝 0)), i.e. integrable on SOME neighbourhood of 0. `‖y‖^(-2c)` is integrable near 0 iff
     2c<C, and integrable near ∞ iff 2c>C, so the GLOBAL integral never converges (never both). So
     I CANNOT use the global lemma directly on the raw function. Options:
       (a) Prove the local threshold directly via a ball, WITHOUT the global polar lemma — is there
           a ball / closedBall version of the polar reduction in v4.29? (integral over ball 0 R of
           a radial function → 1-D integral on Ioo 0 R). I have NOT found one. If it exists, name it.
       (b) Multiply by a cutoff / use a radial function f that is t^(-2c) near 0 and 0 far away
           (e.g. f(t) = t^(-2c)·indicator[t<R]), apply the GLOBAL lemma to that f, get IntegrableOn
           (fun y ↦ y^(C-1)·f(y)) (Ioi 0) = IntegrableOn (y^(C-1-2c) on Ioo 0 R) → threshold. Then
           relate integrability of the cutoff-radial function to IntegrableAtFilter of the raw Q^(-c).
       (c) Some other route.
     Q: rank (a)/(b)/(c) by lowest total Lean friction at v4.29. Give the concrete lemma names for
     the winning route (search names you're confident exist at this pin; flag guesses).
  3. The `sSup` endgame. Once I have the characterization
        c ∈ localAdmissibleExponents Q 0 ↔ (0 ≤ c ∧ 2*c < C)
     i.e. the set = Set.Ico 0 (C/2) (as a subset of ℝ; note the set is {c | 0≤c ∧ c < C/2}), I need
     sSup {c | 0 ≤ c ∧ c < C/2} = C/2. With C ≥ 1, C/2 > 0. Cleanest Mathlib path for
     sSup (Ico 0 (C/2)) = C/2 or sSup {c|0≤c∧c<b} = b for b>0? (csSup_Ico / Real.sSup_...?)
     Need BddAbove for the ≤ direction. Name the lemmas.

  4. Is the direction split (prove characterization iff, then read off sSup) the right bedrock
     shape, or is there a trap (e.g. the boundary point, or the raw-function-vs-cutoff equivalence
     for IntegrableAtFilter) that makes a different decomposition cleaner?
</task>

<output_contract>
  1. CARRIER: recommend Fin C → ℝ vs EuclideanSpace, + the transport lemma names for ‖·‖ and volume.
  2. LOCAL-vs-GLOBAL: rank routes (a)/(b)/(c); for the winner, the concrete lemma chain (names +
     one-line role each), flagging any lemma name you are not confident exists at v4.29.
  3. SSUP ENDGAME: the lemma(s) for sSup{c|0≤c∧c<b}=b (b>0) and the BddAbove supply.
  4. TRAPS: the 2-3 things most likely to burn a build cycle here (rpow-at-0 convention, ℕ-subtraction
     dim E - 1 when C could interfere, measurability of negPow near a cutoff, IntegrableAtFilter
     mono/congr subtleties).
  Be concrete and terse. Prefer naming a real lemma over describing it. This is a decomposition /
  route-selection consult, not a request for full proof code.
</output_contract>

<grounding_rules>
  You may not have the exact v4.29 signatures memorized. For any lemma name you give, mark it
  [confident] or [guess — verify]. Distinguish "this is the mathematically correct reduction" (you
  can assert) from "this exact lemma exists with this name" (mark if unsure). Do NOT invent a
  ball-version polar lemma if you're not sure it exists — say so.
</grounding_rules>
