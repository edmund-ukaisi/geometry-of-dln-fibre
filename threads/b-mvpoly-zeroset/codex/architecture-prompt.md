<task>
Lean 4 + Mathlib (pinned v4.29.0). I am proving, network-free standalone:

  theorem mvpoly_nonzero_zeroset_volume_zero {n : ℕ}
      (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
      volume {x : Fin n → ℝ | MvPolynomial.eval x p = 0} = 0

`volume` on `Fin n → ℝ` is the Pi/MeasureSpace product Lebesgue measure.

Confirmed-existing Mathlib pieces (exact names + signatures verified by reading source):
- Polynomial.finite_setOf_isRoot {p : R[X]} (hp : p ≠ 0) : Set.Finite { x | IsRoot p x }
- Set.Finite.measure_zero (h : s.Finite) (μ : Measure α) [NoAtoms μ] : μ s = 0   (real volume has NoAtoms)
- MvPolynomial.finSuccEquiv R n : MvPolynomial (Fin (n+1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R)
- MvPolynomial.eval_eq_eval_mv_eval' (s : Fin n → R) (y : R) (f : MvPolynomial (Fin (n+1)) R) :
      eval (Fin.cons y s) f = Polynomial.eval y (Polynomial.map (eval s) (finSuccEquiv R n f))
- MeasurableEquiv.piFinSuccAbove (α) (i) : (∀ j, α j) ≃ᵐ α i × ∀ j, α (i.succAbove j);
    toEquiv = (Fin.insertNthEquiv α i).symm. For i=0: insertNthEquiv α 0 = consEquiv, succAbove 0 = succ.
- measurePreserving_piFinSuccAbove (μ) (i) : MeasurePreserving (piFinSuccAbove α i) (Measure.pi μ) ((μ i).prod (Measure.pi fun j => μ (i.succAbove j)))
    so volume_preserving_piFinSuccAbove gives, for i=0, MeasurePreserving e volume (volume.prod volume) where e : (Fin (n+1)→ℝ) ≃ᵐ ℝ × (Fin n → ℝ).
- MeasurePreserving.measure_preimage_equiv (hf : MeasurePreserving f μa μb) (s : Set β) : μa (f ⁻¹' s) = μb s
- measure_prod_null_of_ae_null {s} (hsm : MeasurableSet s) (hs : (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ[μ] 0) : μ.prod ν s = 0

My plan (induction on n):
- n=0: zero set is empty (constant nonzero poly), volume 0.
- n=1: via finite_setOf_isRoot + Set.Finite.measure_zero. (Need to connect MvPolynomial (Fin 1) eval to univariate Polynomial roots.)
- Step n -> n+1: Let e = piFinSuccAbove (fun _=>ℝ) 0, MeasurePreserving e volume (volume.prod volume).
  Write Z = {x | eval x p = 0}. Then volume Z = (volume.prod volume) (e '' Z)? No — use Z = e ⁻¹' T with T = e '' Z and measure_preimage_equiv: volume Z = volume (e ⁻¹' T) = (volume.prod volume) T.
  T = {(y, s) : ℝ × (Fin n→ℝ) | eval (e.symm (y,s)) p = 0} = {(y,s) | eval (Fin.cons y s) p = 0}.
  Reindex to put ℝ second for the slice over s? measure_prod_null_of_ae_null slices over the FIRST factor. I want: for a.e. s (off the null zero-set of a nonzero coefficient, by IH), the slice {y | (y,s)∈T} = {y | Polynomial.eval y (Polynomial.map (eval s) (finSuccEquiv p)) = 0} is the root set of a NONZERO univariate poly (eval s of finSuccEquiv p, which is nonzero whenever eval s of its leading/some nonzero coeff is nonzero) hence finite hence null.
  So I actually want to slice over the SECOND factor (s), i.e. use the prod with s first. So pick e mapping to (Fin n→ℝ) × ℝ instead, i.e. split off the LAST variable? Or swap. Question: cleanest way to orient the product so Fubini slices over s.

<output_contract>
1. VERDICT: is this plan sound and the cleanest route? (2-4 sentences)
2. The single biggest friction point you predict and how to handle it (orientation of the product / which variable to split / measurability of the zero set / connecting Fin 1 MvPolynomial to univariate). Rank top 3 frictions.
3. For the inductive step: the precise sequence of lemmas to get "slice is null for a.e. s", being explicit about (a) which factor Fubini slices, (b) how to prove the univariate slice poly is nonzero a.e. in s (which coefficient, why eval s of it nonzero a.e.), (c) measurability of T.
4. Any Mathlib lemma I'm missing or misusing (flag inference vs certainty — you don't have to have the exact name, but say if you doubt one exists at v4.29).
Keep it tight, mathematician-to-mathematician. No code dumps; name lemmas and the logical skeleton.
</output_contract>

<grounding_rules>
Distinguish what you know exists in Mathlib (high confidence) from what you infer should exist. Flag any step where you are guessing a lemma name. Do not invent measure-theory facts.
</grounding_rules>
