<task>
Lean 4 / Mathlib v4.29, RLCT threshold-lift ≤ direction. rlctAtOn F w0 = sSup { c:ℝ≥0∞ | ∃c':NNReal, c=c' ∧ ∃Ω open ∋w0, IntegrableOn (|F|^(-c')·1) Ω volume }.

GOAL: rlctAtOn (fun p:ℝ×Y => p.1²+H p.2) (0,y0) ≤ 1/2 + rlctAtOn H y0, where H:Y→ℝ, H≥0, measurable, and hHne (∃U∈𝓝 y0, H≠0 a.e. on U). Y is a ProperSpace + IsFiniteMeasureOnCompacts (e.g. Fin d→ℝ).

I HAVE proven this contrapositive lemma:
  core_int_of_joint_int : (c R:ℝ) → 1/2<c → 0<R → (V:Set Y) → MeasurableSet V → (hHne_V: H≠0 a.e. on V) → (hHle: ∀z∈V, H z ≤ R²) → IntegrableOn (|x²+H|^(-c)·1) (Icc(-R)R ×ˢ V) → IntegrableOn (|H|^(-(c-1/2))) V.
[i.e. joint integrable on the rectangle ⟹ core integrable at the shifted exponent c-1/2 on V; via the cusp step_lintegral_top contrapositive.]

To finish ≤: by sSup_le, take a joint-admissible c (c=(c':NNReal), ∃Ω_joint open ∋(0,y0), IntegrableOn |x²+H|^(-c')·1 Ω_joint). Show (c':ℝ≥0∞) ≤ 1/2+lamH. If c'≤1/2 trivial. If c'>1/2: I want to apply core_int_of_joint_int to get core-admissibility at c'-1/2, hence (c'-1/2:ℝ≥0∞)≤lamH, hence c'≤1/2+lamH.

THE OBSTRUCTION: core_int_of_joint_int needs a rectangle Icc(-R)R ×ˢ V ⊆ Ω_joint with (a) V measurable, (b) H≠0 a.e. on V, (c) H ≤ R² on ALL of V, and the conclusion gives core-integrability on V — but for core-ADMISSIBILITY (to compare to lamH=sSup) I need IntegrableOn |H|^(-(c'-1/2)) on an OPEN nbhd of y0. The catches:
1. H is only MEASURABLE (not continuous), so H need not be bounded near y0 — can't guarantee H ≤ R² on an open nbhd.
2. core_int_of_joint_int gives integrability on V (which would be {H≤R²}∩nbhd, NOT open).
How do I bridge "IntegrableOn |H|^(-(c'-1/2)) on a non-open V" to "(c'-1/2:ℝ≥0∞) ≤ rlctAtOn H y0" (which is sSup over OPEN nbhds)? 

Note: if H(y0)>0 then rlctAtOn H y0 = ⊤ (locally non-vanishing) and RHS=⊤, ≤ trivial — but H measurable means H(y0)>0 doesn't imply H>0 on a nbhd. And rlctAtOn H y0 with H possibly unbounded near y0 — does the sSup-over-open-nbhds definition even interact well?
</task>

<output_contract>
1. Is the obstruction real, or is there a clean bridge? Give the cleanest Lean route to finish the ≤ direction. Options to assess: (a) does rlctAtOn's ∃-open-Ω let me use V=Ω_joint's y-slice directly if I choose R = some bound, handling H-unboundedness by a sub-nbhd? (b) restrict to a bounded open V₀∋y0 and split V₀ = (V₀∩{H≤R²}) ∪ (V₀∩{H>R²}) — is the {H>R²} part harmless (there |x²+H|^{-c'} is bounded ⟹ contributes finitely)? (c) a different sShape for core_int_of_joint_int that outputs an OPEN-nbhd integrability?
2. Does the lemma even need H bounded near y0, or can I pick R AFTER seeing Ω_joint's y-slice (R large)? If V₀ is a BOUNDED open nbhd (Y proper), is H bounded on V₀? (No — measurable. But is it bounded a.e./does it matter for the cusp?)
3. Name exact Mathlib v4.29 lemmas. Flag the cleanest minimal-friction path.
</output_contract>

<grounding_rules>
Label Mathlib lemmas CONFIDENT vs NAME-UNCERTAIN. Distinguish inference from fact. If the obstruction needs an extra hypothesis on H (e.g. continuity / local boundedness), say so explicitly — that would be a fidelity finding I must escalate.
</grounding_rules>
