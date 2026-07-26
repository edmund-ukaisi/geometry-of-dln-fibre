<task>
Lean 4 + Mathlib v4.29. I am proving a reusable measure-theory brick and want the EXACT Lean
assembly for the fiddly measure-transport, validated against the pinned Mathlib. Please check lemma
names/shapes against the real v4.29 (run `lake env lean` if useful).

GOAL:
  theorem volume_zeroLocus (n : ℕ) : ∀ {p : MvPolynomial (Fin n) ℝ}, p ≠ 0 →
      volume {x : Fin n → ℝ | MvPolynomial.eval x p = 0} = 0

STRUCTURE (induction on n):
- BASE n=0: p ≠ 0 (a nonzero constant) ⟹ {x | eval x p = 0} = ∅ ⟹ volume = 0. What is the cleanest
  v4.29 way to show `eval x p ≠ 0` for `p : MvPolynomial (Fin 0) ℝ`, `p ≠ 0`? (isEmptyRingEquiv?
  eval injective on empty σ? constantCoeff?) Give the exact incantation.
- STEP n→n+1: set q := finSuccEquiv ℝ n p. Facts available (verified present):
  * eval_eq_eval_mv_eval' (s : Fin n → R)(y : R)(f) : eval (Fin.cons y s) f = Polynomial.eval y (Polynomial.map (eval s) (finSuccEquiv R n f))
  * Polynomial.finite_setOf_isRoot {p:R[X]}(hp:p≠0) : Set.Finite {x | IsRoot p x}
  * Set.Finite.measure_zero (h:s.Finite)(μ)[NoAtoms μ] : μ s = 0 ; NoAtoms (volume:Measure ℝ) is an instance
  * measure_prod_null {s}(hs:MeasurableSet s) : μ.prod ν s = 0 ↔ (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ[μ] 0
  * volume_eq_prod (α β) : (volume:Measure (α×β)) = (volume).prod (volume)
  * MeasurableEquiv.piFinSuccAbove (fun _=>ℝ) i : (Fin(n+1)→ℝ) ≃ᵐ ℝ × (Fin n → ℝ), toEquiv=(Fin.insertNthEquiv..).symm, fwd x ↦ (x i, fun j => x (i.succAbove j))
  * volume_preserving_piFinSuccAbove (fun _=>ℝ) i : MeasurePreserving (piFinSuccAbove ..)
  * Polynomial.leadingCoeff_ne_zero : leadingCoeff p ≠ 0 ↔ p ≠ 0
  Math of the step: eval x p = Polynomial.eval (x 0) (map (eval (x∘succ)) q). For a fixed s=(x∘succ)
  with map(eval s) q ≠ 0, the y-slice {y | Polynomial.eval y (map(eval s) q)=0} is finite→null. The
  set {s | map(eval s) q = 0} ⊆ {s | eval s (q.leadingCoeff)=0}, null by IH (q.leadingCoeff≠0). So
  for a.e. s the slice is null ⟹ (measure_prod_null) the whole set is null.
</task>

<output_contract>
Terse, in these sections:
1. BASE CASE: the exact ~3-line Lean for n=0.
2. TRANSPORT: the exact Lean to turn `volume {x | eval x p = 0}` into a prod-measure statement that
   `measure_prod_null` consumes, with the slice being over the LAST n coords (s) so the univariate
   poly is in the singled-out variable. CRITICAL: measure_prod_null slices the SECOND factor for a.e.
   FIRST — so which factor order do I need (ℝ×(Fin n→ℝ) vs (Fin n→ℝ)×ℝ), and do I need prodComm /
   Measure.prod_swap? Give the exact measure-preserving-transport chain + how to get MeasurableSet.
   Name the EXACT v4.29 lemmas (flag any you're unsure exists).
3. AE-SLICE: the exact Lean for "{s | slice not null} ⊆ {s | eval s q.leadingCoeff = 0}" ⟹ ae, and
   the leadingCoeff/map-eq-zero step (map(eval s) q = 0 → eval s q.leadingCoeff = 0).
4. PITFALLS: the top 2-3 v4.29 traps in this specific assembly (instance diamonds, prod vs pi,
   coeff/leadingCoeff, Fin.cons vs insertNth).
</output_contract>

<grounding_rules>
Flag any lemma name as "INFER — verify" unless you confirmed it in the v4.29 source. Distinguish
"typechecks" from "this exact name exists".
</grounding_rules>
