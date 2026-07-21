<task>
Independent soundness review of two Lean 4 statements from a resolution-of-singularities
formalisation (Aoyagi's DLN learning-coefficient machinery). Judge the STATEMENTS only (their
proofs are `sorry` blueprints). I want a decorrelated read; do not trust my framing.

CONTEXT / relevant definitions (Lean 4 + Mathlib, D M : ℕ, functions ℝ^D → ℝ):

  def StepInv (F : Fin M → (Fin D → ℝ) → ℝ) (g : (Fin D → ℝ) → (Fin D → ℝ))
      (b : (Fin D → ℝ) → ℝ) {nR : ℕ} (resid : Fin nR → (Fin D → ℝ) → ℝ)
      (q : Fin M → Fin nR → (Fin D → ℝ) → ℝ) (V : Set (Fin D → ℝ)) : Prop :=
    (∀ i j, ContinuousOn (q i j) V) ∧
      (∀ u ∈ V, ∀ i, (F i ∘ g) u = ∑ j, q i j u * (b u * resid j u))

  def PrincipalInv (F : Fin M → (Fin D → ℝ) → ℝ) (g : (Fin D → ℝ) → (Fin D → ℝ))
      (b : (Fin D → ℝ) → ℝ) (q r : Fin M → (Fin D → ℝ) → ℝ) (V : Set (Fin D → ℝ)) : Prop :=
    (∀ i, ContinuousOn (q i) V) ∧ (∀ i, ContinuousOn (r i) V) ∧
      (∀ u ∈ V, ∀ i, (F i ∘ g) u = q i u * b u) ∧
      (∀ u ∈ V, b u = ∑ i, r i u * (F i ∘ g) u)

FINDING 1 — the "terminal Bézout" leaf. Its Prop (universally quantified over M D F g b q V):

  StepInv F g b (fun _ : Fin 1 ↦ 1) q V →
  ∀ (i₀ : Fin M) (unit : (Fin D → ℝ) → ℝ),
    ContinuousAt unit 0 → unit 0 ≠ 0 → (∀ u ∈ V, (F i₀ ∘ g) u = b u * unit u) →
  ∃ (V' : Set (Fin D → ℝ)) (r : Fin M → (Fin D → ℝ) → ℝ),
    IsOpen V' ∧ (0 : Fin D → ℝ) ∈ V' ∧ V' ⊆ V ∧
    PrincipalInv F g b (fun i ↦ q i 0) r V'

  The conclusion asserts `0 ∈ V'` and `V' ⊆ V`. The hypotheses never assume `0 ∈ V` or `IsOpen V`.
  Question A: is this Prop TRUE as a standalone universally-quantified statement, or is it FALSE
  (missing a hypothesis)? If false, give the minimal missing hypothesis and a concrete counterexample.

FINDING 2 — a "structural chain" hypothesis carried by the fold. `buildTree d …` is a finite
resolution tree; each leaf `l` has `l.numDiv : ℕ` analytic divisors, and `l.divExp k : ℕ` is the
k-th divisor's ACCUMULATED SCALAR exponent, equal to `Mval(profile_k)` (a natural number). The Prop:

  StructuralChainResidual d : Prop :=
    ∀ l ∈ leaves (buildTree d …), ∀ k k' : Fin l.numDiv,
      l.divExp k ∣ l.divExp k' ∨ l.divExp k' ∣ l.divExp k     -- scalar divisibility in ℕ

  It is DOCUMENTED as "the divisibility chain terminal principality rides", justified by a closed
  form `b_i = ∏_{t̃<i} u_{s,k}` giving `b_1 | b_2 | … | b_M` as MONOMIALS (i.e. exponent VECTORS
  pointwise ≤). For (3,3,4) the terminal divisor exponents (Mval values) are {8, 9, 12}.
  Question B: distinguish "monomial/exponent-vector divisibility of the b_i" from "scalar ∣-divisibility
  of the accumulated ℕ exponents Mval". Does the closed form b_i=∏u justify the SCALAR statement above?
  If a single leaf carries two divisors with exponents like 8 and 9 (8∤9, 9∤8), is the Prop false there?
  Is scalar ∣-comparability of Mval values something a resolution's min-over-divisors value actually needs?
</task>

<output_contract>
Two sections, "FINDING 1" and "FINDING 2". For each: a one-line VERDICT (TRUE / FALSE / UNDERSPECIFIED),
then ≤6 lines of justification. If FALSE, give the minimal fix. Mark any claim that is inference vs
mathematical fact. No Lean code needed; prose + the decisive math only.
</output_contract>

<grounding_rules>
State plainly when you are inferring intent vs asserting a mathematical fact about the written Prop.
Judge the Prop AS WRITTEN, not the charitable reading. If you need an assumption to make it true, name it.
</grounding_rules>
