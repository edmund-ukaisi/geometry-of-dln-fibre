<task>
Lean 4 / Mathlib v4.29. I'm proving the ≥ direction of an RLCT threshold-lift. The goal reduces to:

  rlctAtOn (joint) (0,y0)  is an  sSup S_joint  where
  S_joint = { c : ℝ≥0∞ | ∃ c':NNReal, c = c' ∧ ∃ Ω open ∋ (0,y0), IntegrableOn (|joint|^(-c')·1) Ω }

I must show:  (1/2 : ℝ≥0∞) + lamH  ≤  sSup S_joint,  where lamH = rlctAtOn H y0 (also an sSup of the analogous core-admissible set S_core).

I HAVE these proven lemmas:
- joint_admissible_of_split : ∀ (a b : ℝ), 0≤a → a<1/2 → 0≤b → (∃ Ω open ∋ y0, IntegrableOn |H|^(-b) Ω) → (∃ Ω open ∋ (0,y0), IntegrableOn (|joint|^(-(a+b))·1) Ω).  [i.e. a<1/2 on x-side + b core-admissible ⟹ a+b joint-admissible]
- core_admissible_of_lt : ∀ (b:NNReal), (b:ℝ≥0∞) < lamH → (∃ Ω open ∋ y0, IntegrableOn |H|^(-(b:ℝ)) Ω).
- core_admissible_zero : ∃ Ω open ∋ y0, IntegrableOn |H|^(-(0:ℝ)) Ω.

So from joint_admissible_of_split, the exponent (a+b) gives a member ((a+b).toNNReal : ℝ≥0∞) ∈ S_joint (when a+b ≥ 0), hence (a+b:ℝ≥0∞) ≤ sSup S_joint via le_sSup.

The REMAINING difficulty is purely the ENNReal/real arithmetic of the SPLIT: I'm using `le_of_forall_lt_imp_le_of_dense`: take q < 1/2 + lamH (q : ℝ≥0∞, q ≠ ⊤ since < a finite-ish... actually 1/2+lamH may be ⊤), must show q ≤ sSup S_joint. I want to produce reals a,b with 0≤a, a<1/2, 0≤b, b core-admissible (b<lamH via core_admissible_of_lt, OR b=0 via core_admissible_zero when lamH=0), and q ≤ ofReal(a+b) (or q < ofReal(a+b)). Corners: q=1/2 boundary (need a<1/2 STRICT), lamH=0 (forces b=0), lamH=⊤ (q any finite), q.toReal coercions.
</task>

<output_contract>
Give the CLEANEST Lean proof structure for `step_rlct_ge` (the ≥ direction), from `apply le_of_forall_lt_imp_le_of_dense; intro q hq` to the end. Specifically:
1. The cleanest way to extract a,b reals from `hq : q < 1/2 + lamH` handling all corners (lamH=0, lamH=⊤, q near 1/2). Prefer working with ENNReal directly (ENNReal.lt_add_iff / ENNReal.exists_..._btwn) over q.toReal if cleaner.
2. How to turn "a+b joint-admissible" into "q ≤ sSup S_joint" (the le_sSup step + the coercion (a+b:ℝ≥0∞) membership, given a+b≥0).
3. Name exact Mathlib v4.29 lemmas (flag any you're unsure of). Is there a slicker route than le_of_forall_lt_imp_le_of_dense — e.g. expressing 1/2+lamH itself as an sSup and using sSup_le_sSup / a Galois argument?
</output_contract>

<grounding_rules>
Label each Mathlib lemma CONFIDENT-exists vs NAME-UNCERTAIN. Don't invent names. Flag inference vs fact.
</grounding_rules>
