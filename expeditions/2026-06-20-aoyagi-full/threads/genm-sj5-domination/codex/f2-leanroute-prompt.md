# Consult: leanest Lean 4 / Mathlib v4.29 route for a MEASURABLE Hermitian eigendecomposition

I am formalising, in Lean 4 + Mathlib (pinned v4.29), this exact theorem (`X` an abstract
measurable space; `Matrix (Fin M₂)(Fin M₂) ℝ` carries the Pi/Borel measurable structure):

    theorem measurableEigendecomp {X : Type*} [MeasurableSpace X] {M₂ : ℕ}
      (A : X → Matrix (Fin M₂) (Fin M₂) ℝ) (hA : Measurable A)
      (hherm : ∀ z, (A z).IsHermitian) :
      Measurable (fun z => (hherm z).eigenvalues₀)                                    -- (i)
      ∧ ∃ U : X → Matrix (Fin M₂)(Fin M₂) ℝ, Measurable U ∧ (∀ z, (U z)ᵀ * U z = 1)
          ∧ (∀ z, A z = U z * diagonal (sorted eigenvalues of A z) * (U z)ᵀ)          -- (ii)

`eigenvalues₀ : Fin (Fintype.card (Fin M₂)) → ℝ` are the eigenvalues in DECREASING (antitone) order;
Mathlib's `IsHermitian.eigenvectorUnitary` gives a diagonalizing orthogonal matrix but it is
CHOICE-built (via `gramSchmidt` on a `Classical.choice`-selected eigenbasis) so it is NOT (provably)
measurable, and it uses the UNSORTED `eigenvalues`, not `eigenvalues₀`.

GROUNDED Mathlib-support facts I have already verified at this pin:
- Mathlib has NO Weyl perturbation / eigenvalue-Lipschitz / eigenvalue-continuity lemma.
- Mathlib has NO polynomial-root-continuity lemma (roots as a function of coefficients).
- Mathlib HAS: the real spectral theorem `A = U·diagonal(eigenvalues)·Uᵀ` (choice-built U);
  `IsHermitian.eigenvalues₀` with `sort_roots_charpoly_eq_eigenvalues₀`
  ((charpoly.roots.map re).sort(≥) = List.ofFn eigenvalues₀); `gramSchmidt` /
  `gramSchmidtOrthonormalBasis`; `LowerSemicontinuous` of `iSup`, and `LowerSemicontinuous.measurable`;
  a banked matrix Rayleigh bound `(⨅ i, eigenvalues i)·‖y‖² ≤ yᵀ(A y)`.
- `A.charpoly.coeff j` is a polynomial (continuous, measurable) in the entries of A.

A decorrelated pen-and-paper adjudication already established the TRUTH-VALUE (a Borel formula exists,
via multiplicity-pattern stratification + Sylvester eigenprojections `P_a = ∏_{b≠a}(A-μ_b I)/(μ_a-μ_b)`
+ lex-first-pivot Gram-Schmidt per block; NO measurable-selection / KRN, NO contour integral). I do NOT
need the truth-value re-litigated. I need a LEAN-FEASIBILITY / minimal-labour read.

QUESTIONS (answer concretely, Lean-idiom aware, v4.29):
1. CONJUNCT (i) — `Measurable (fun z => eigenvalues₀ (A z))`. Rank the routes by TOTAL Lean labour and
   name the load-bearing lemmas each needs:
   (a) prove `Continuous eigenvalues₀` via a from-scratch Weyl bound;
   (b) LSC route: `∑_{i<k} eigenvalues₀ = ⨆_{P rank-k orth proj} tr(P·A)` (Ky Fan), each `A↦tr(P·A)`
       continuous ⟹ the sup is LSC ⟹ Borel; then `eigenvalues₀ k = S_{k+1}-S_k`. Does this need the
       full Ky-Fan MAX principle proved, or is there a shorter sufficient inequality? Is indexing the
       `⨆` over the (uncountable) projection type OK for LSC in Lean?
   (c) sorted-roots-of-charpoly measurability directly from `sort_roots_charpoly_eq_eigenvalues₀`
       (measurability of "sorted real roots" as a function of measurable coefficients, given all roots
       real). What is the cleanest Lean statement of "sorted roots measurable" and does it dodge
       root-continuity?
   (d) any 4th route I'm missing (e.g. via `IsHermitian.eigenvalues` and a min-max over a COUNTABLE
       dense family; or an inertia/Sylvester-count `{λ_k ≤ c}` Borel characterization).
   Give the single route you'd bet is shortest in Lean, with an honest sub-lemma list.

2. CONJUNCT (ii) — the measurable sorted orthogonal `U`. Is there ANY Lean-shorter route than the full
   stratified-Sylvester + pivoted-Gram-Schmidt construction (e.g. an iterated measurable-deflation, or a
   trick reusing the choice-built `eigenvectorUnitary` up to a measurable correction)? Or is the
   stratification genuinely unavoidable in Lean? Sketch the leanest decomposition into named lemmas.

3. SCOPE: give an honest ORDER-OF-MAGNITUDE Lean line-count per sub-piece and a total, and say whether
   this is realistically ONE module/tide or a multi-module effort. If multi-module, propose the cut
   points (which sub-brick to land first as standalone sorry-free bedrock).

Be concrete and skeptical. If a route I listed is a dead end in Lean, say so and why.
