<task>
Independent confirmation of a claimed FALSITY in a real-analysis lemma statement (RLCT formalisation).
Judge whether the stated hypotheses IMPLY the conclusion, or whether two specific gaps break it.

THE LEMMA (claimed FALSE as stated):
`weightedThreshold F φ {w*} = weightedThreshold (F∘π) ((φ∘π)·|det Dπ|) (π⁻¹{w*})`
where `weightedThreshold G ρ K := sSup { c'≥0 : ∃ Ω open ⊇ K, ∫_Ω |G|^{-c'}·ρ < ∞ }` (a threshold of
exponents for which a weighted density is locally integrable around the compact fibre K), on a
finite-dim real space M with additive-Haar (Lebesgue) `volume`.
HYPOTHESES: π proper; E measurable, volume E = 0; π injective on Eᶜ; π has derivative Dπ at each point
of Eᶜ (HasFDerivAt, only OFF E). NO surjectivity hypothesis; NO hypothesis that π(E) is null.

CLAIM: the EQUALITY is false; the reverse direction (RHS ≥ LHS, or vice versa) fails two ways:
GAP 1 (surjectivity): if w* ∉ range π, then π⁻¹{w*} = ∅, so RHS = weightedThreshold over the empty
  fibre. Claim: that RHS threshold = ⊤ (every exponent admissible, since ∅ ⊆ any Ω and one may take Ω=∅),
  while LHS can be FINITE (F with a genuine singularity at w*). So LHS ≠ RHS. Fix: add Surjective π.
GAP 2 (Luzin-N): "π differentiable off E + E null" does NOT imply π(E) is null. A π that is
  id + Cantor-staircase (strictly increasing, continuous, differentiable off the null Cantor set E with
  derivative 1 there) maps the null set E to a POSITIVE-measure set π(E). An F-singularity placed in π(E)
  contributes integrability mass to the LHS that the off-E change-of-variables never accounts for, breaking
  the reverse inequality. Fix: add volume(π(E)) = 0 (the absolute-continuity / Luzin-N condition).

QUESTIONS:
1. GAP 1: is it correct that w*∉range π ⟹ π⁻¹{w*}=∅ ⟹ the RHS weightedThreshold = ⊤ (under the given
   sSup-over-open-Ω-⊇-K definition with K=∅)? And that the LHS can be finite? So the equality is false
   without surjectivity? Confirm or refute.
2. GAP 2: is the Cantor-staircase (or id+staircase) a valid counterexample showing "differentiable off a
   null E" does NOT give π(E) null, and that this breaks the weighted-threshold transport equality without
   a Luzin-N / volume(π(E))=0 hypothesis? Is `volume(π''E)=0` the right minimal fix? Confirm or refute,
   and if there's a subtlety (e.g. does properness or the |det Dπ| weight rescue it?) flag it.
3. Are `Surjective π` + `volume(π''E)=0` TOGETHER sufficient to restore the equality (given the other
   hyps)? Or is something else still missing?
</task>

<output_contract>
Three numbered verdicts, terse. Each: CONFIRMED / REFUTED + one-or-two-line reason. For Q2 note if any
hypothesis (properness, the Jacobian weight) rescues it. For Q3, sufficient/insufficient + what's missing.
</output_contract>

<grounding_rules>
Distinguish what follows rigorously (fact) from heuristic (inference) — flag inferences. The Cantor
function's key property (maps a null set onto positive measure) is standard; use it. Don't invent Mathlib
lemma names.
</grounding_rules>
