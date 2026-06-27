<task>
Lean 4 / Mathlib v4.29 proof-architecture review. I must formalise this RLCT lemma (the "smooth-block Fubini" lemma for deep-linear-network learning coefficients):

  Define rlctAt F w0 = sSup { c : ℝ≥0∞ | ∃ c':NNReal, c=c' ∧ ∃ U ∈ 𝓝 w0, IntegrableOn (fun w => |F w|^(-(c':ℝ))) U volume }.

  CLAIM: for F(x,y) = (∑_{i=1}^n x_i²) + G(y)  on  (EuclideanSpace ℝ (Fin n)) × Y, where G(y) ≥ 0 is the "core" (in a normal-crossing chart G = ∏_j y_j^{2k_j}, so G ≥ 0, measurable, ≢ 0), we have
    rlctAt F (0,0) = n/2 + rlctAt_core,
  where rlctAt_core = rlctAt (G) 0 (the core's own RLCT, = min_j (1)/(2k_j) for the plain monomial, shifted by Jacobian exponents h_j to min_j (h_j+1)/(2k_j) when a Jacobian weight ∏|y_j|^{h_j} is present).

  The design card sketches the proof via an EXACT identity ∫_{|x|<ε}(|x|²+s)^{-c}dx = C(n,c)·s^{n/2-c}, C a Beta integral finite iff c>n/2, then Fubini.

  I (the formaliser) have NUMERICALLY FOUND two problems with that route:
  (1) The exact identity ∫_{|x|<ε}(|x|²+s)^{-c} = C·s^{n/2-c} is FALSE for FINITE ε — it holds only for ε=∞. For finite ε (which is what an RLCT neighbourhood is), only the NEAR-0 ASYMPTOTIC g(s) := ∫_{|x|<ε}(|x|²+s)^{-c}dx ~ C·s^{n/2-c} as s→0+ holds (numerically confirmed n=1,2,3). The threshold result rlctAt F = n/2 + λ_core is nonetheless numerically correct (confirmed n∈{1,2}, k∈{1,2}: threshold c* = n/2 + 1/(2k)).
  (2) Mathlib v4.29 has NO parametric radial integral ∫(|x|²+s)^{-c}dx (neither exact value nor near-0 asymptotic). It HAS: integrable_fun_norm_addHaar (radial reduction: Integrable(f∘‖·‖) ⟺ IntegrableOn (y↦y^{n-1}•f y) (Ioi 0)); intervalIntegral.integrableOn_Ioo_rpow_iff; Fubini (MeasureTheory.integrableOn_prod_iff / Integrable fst-snd). I already proved, axiom-clean, radial_ball_iff : IntegrableOn ‖x‖^s (ball 0 R) ⟺ -(n)<s, via integrable_fun_norm_addHaar + ball-truncation.

  Since rlctAt only needs the INTEGRABILITY THRESHOLD (not the exact value), I do NOT need the Beta-integral exact identity. I need: the Fubini'd integral ∫∫_{nbhd}(∑x²+G(y))^{-c} converges IFF c < n/2 + λ_core.
</task>

<output_contract>
1. RANK the candidate Lean routes to the THRESHOLD (not the exact value), cheapest first. For each: the key Mathlib lemmas (v4.29 names), the # of genuinely-new sub-lemmas I'd have to build by hand, and the single hardest sub-step.
2. State whether the cleanest route needs the parametric radial integral's near-0 ASYMPTOTIC (a two-sided bound c1·s^{n/2-c} ≤ g(s) ≤ c2·s^{n/2-c} near 0), or whether there's a route that AVOIDS asymptotics entirely (e.g. a direct comparison/domination on the 2-variable integrand, or a clever variable change on (x,y) jointly).
3. Flag any step that is a REAL Mathlib-gap requiring a multi-hundred-line build, vs. a 1-2 lemma application.
4. Give your honest verdict: is this "light" (as the card claims) or is it heavy? If heavy, is there a DIFFERENT honest statement (weaker, or differently-shaped) that L2 could consume and that IS light?
</output_contract>

<grounding_rules>
Distinguish (a) Mathlib lemmas you are CONFIDENT exist in v4.29 from (b) lemmas you THINK should exist but are unsure — label each. Do not invent lemma names; if unsure of a name, describe the statement and say "name uncertain". Flag inference vs. fact.
</grounding_rules>
