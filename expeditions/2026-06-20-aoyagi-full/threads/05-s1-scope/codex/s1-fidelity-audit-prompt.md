<task>
Independent statement-fidelity review of two Lean 4 theorem STATEMENTS (judge the statement, not the
proof — both are `sorry`). I need adversarial vacuity / over-under-claim checks. Real-analysis content.

CONTEXT: RLCT (real log-canonical threshold) formalisation. Definitions:
- `weightedThreshold (G ρ : M → ℝ) (K : Set M) : ℝ≥0∞ := sSup { c≥0 : ∃ Ω open ⊇ K,
     IntegrableOn (|G|^{-c} · ρ) Ω volume }`  on a finite-dim real `M` with Lebesgue `volume`.
- `rlctAtOn (F : M → ℝ) (w0) := weightedThreshold F (fun _ => 1) {w0}`.

STATEMENT 1 — S1.1 weighted-threshold transport (claimed: transport along a proper a.e.-analytic diffeo):
```
theorem weightedThreshold_transport
    {M} [NormedAddCommGroup M] [NormedSpace ℝ M] [MeasureSpace M] [BorelSpace M] [FiniteDimensional ℝ M]
    (F φ : M → ℝ) (wstar : M) (π : M → M) (Dπ : M → (M →L[ℝ] M)) (E : Set M)
    (hproper : IsProperMap π)
    (hE_null : volume E = 0)
    (hinj : Set.InjOn π Eᶜ)
    (hderiv : ∀ m ∈ Eᶜ, HasFDerivAt π (Dπ m) m) :
    weightedThreshold F φ {wstar}
      = weightedThreshold (F ∘ π) (fun m => φ (π m) * |(Dπ m).det|) (π ⁻¹' {wstar}) := by sorry
```
QUESTIONS for S1.1:
A. Are the hypotheses SUFFICIENT for the conclusion to be TRUE? In particular: is "InjOn π on Eᶜ +
   HasFDerivAt on Eᶜ + E null + π proper" enough to get the weighted change-of-variables identity, or is
   something missing (e.g. measurability of π, surjectivity, that π maps Eᶜ into the right target region,
   that the image of the null set E is null, local-diffeo/open-map so π⁻¹{wstar} behaves)? Flag any input
   under which the stated equality could FAIL.
B. Is the Jacobian weight placement correct: the pushed-forward weight is `φ(π m)·|det Dπ(m)|` on the
   SOURCE side, with target weight `φ`? (The known trap: the UNWEIGHTED identity rlctAt(F∘π)=rlctAt(F) is
   FALSE; e.g. F=x²+y², π=(u,uv) gives 1/2≠1, missing factor |det|=|u|.) Does this statement avoid that trap?
C. Could the statement be VACUOUS / trivially true (e.g. if no π satisfies the hyps, or both sides are
   always ⊤/equal for a trivial reason)?

STATEMENT 2 — S1.5 disjoint-block additivity:
```
theorem rlct_additive_disjoint
    {X Y} [MeasureSpace X][TopologicalSpace X][MeasureSpace Y][TopologicalSpace Y]
    (F : X → ℝ) (G : Y → ℝ) (x0 : X) (y0 : Y) :
    rlctAtOn (fun p : X × Y => F p.1 ^ 2 + G p.2 ^ 2) (x0, y0)
      = rlctAtOn (fun x => F x ^ 2) x0 + rlctAtOn (fun y => G y ^ 2) y0 := by sorry
```
QUESTIONS for S1.5:
D. Is `λ(F(x)²+G(y)²) = λ(F²)+λ(G²)` TRUE for ARBITRARY measurable F,G with NO analyticity/regularity
   hypothesis? Aoyagi's additivity (2013 App.C Lemma 2) is for analytic functions. Give a concrete
   counterexample with non-analytic (or wild) F,G where the additivity FAILS, if one exists — OR argue it
   holds in this generality. Also: does the product measure on X×Y need to be the relevant one (is
   `MeasureSpace (X×Y)` the product of the factor measures, and does the statement rely on that)?
E. Is the X×Y `volume`/`MeasureSpace` instance necessarily the product measure? If `weightedThreshold` on
   `X×Y` uses `volume` and that is NOT defeq to `volume.prod volume`, could the statement be ill-posed or
   false? Flag if the missing `[SFinite]`/product-measure linkage is a gap.
</task>

<output_contract>
For S1.1: A/B/C each a 2-3 line verdict (SUFFICIENT / INSUFFICIENT+missing-hyp / VACUOUS). For S1.5: D/E
each 2-3 lines, with a concrete counterexample if additivity fails in the stated generality. End with a
one-line "FLAG or PASS" per statement.
</output_contract>

<grounding_rules>
Separate what you can prove from the definitions (fact) from what you infer about Lean/Mathlib instance
resolution you cannot see (inference) — flag inferences. Do not invent Mathlib lemma names. If a
counterexample needs a specific non-analytic function, give it explicitly.
</grounding_rules>
