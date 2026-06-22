# Statement card — nonzero MvPolynomial zero-set is Lebesgue-null

> **Claim.** For a nonzero real polynomial `p` in `n` variables, its zero set
> `{x ∈ ℝⁿ | p(x) = 0}` has Lebesgue measure zero; equivalently `p` is nonzero
> almost everywhere.
>
> - **Lean:** `MvPolynomial.volume_zeroSet_eq_zero` and `MvPolynomial.ae_eval_ne_zero`
>   (`lean/DLNFibre/Core/MeasureTheory/PolynomialZeroSet.lean` @ `5f6a3924cb39f60835ba36a9561acb5e3451f8b7`)
> - **Gloss.**
>   - `volume_zeroSet_eq_zero {n} (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :`
>     `volume {x : Fin n → ℝ | MvPolynomial.eval x p = 0} = 0` — the zero set of a
>     nonzero `n`-variable real polynomial, as a subset of `Fin n → ℝ` carrying the
>     standard product Lebesgue measure `volume` (`MeasureSpace` via `Measure.pi`),
>     is `volume`-null.
>   - `ae_eval_ne_zero {n} (p) (hp : p ≠ 0) : ∀ᵐ x : Fin n → ℝ, MvPolynomial.eval x p ≠ 0`
>     — the almost-everywhere restatement.
> - **Proved.** Both statements, unconditionally, for every `n : ℕ`. The measure is
>   the genuine product Lebesgue measure on `Fin n → ℝ`. Proof: induction on `n`;
>   `n = 0` zero set is empty (evaluation at the empty point is injective, so a
>   nonzero constant never vanishes); step `n+1` transports `volume` along the
>   measure-preserving `(Fin (n+1) → ℝ) ≃ᵐ (Fin n → ℝ) × ℝ`
>   (`piFinSuccAbove 0` ∘ `prodComm`), views `p` as a univariate polynomial
>   `q = finSuccEquiv ℝ n p` whose leading coefficient is nonzero, applies the IH to
>   that coefficient (null base), and on the complement slices to a nonzero
>   univariate polynomial whose root set is finite (`Polynomial.finite_setOf_isRoot`)
>   hence null; Fubini (`measure_prod_null_of_ae_null`) closes the step.
> - **Assumed.** Only `p ≠ 0`. No hypotheses beyond what the informal claim needs.
> - **Cited.** Standard Mathlib only (no external/unproved interface):
>   `Polynomial.finite_setOf_isRoot`, `Set.Finite.measure_zero`,
>   `MeasurableEquiv.piFinSuccAbove` / `volume_preserving_piFinSuccAbove`,
>   `Measure.measurePreserving_swap`, `Measure.measure_prod_null_of_ae_null`,
>   `MvPolynomial.finSuccEquiv` / `eval_eq_eval_mv_eval'`, `MvPolynomial.continuous_eval`.
> - **Deferred.** none.
> - **Axioms.** `[propext, Classical.choice, Quot.sound]` (clean-three) for both lemmas.
> - **Status.** sorry-free (awaiting fidelity review).

## Provenance

Drafted for the Aoyagi-full L2 `hMid ⟹ hGne` bridge (part b), then the consuming
side (`crux2`) found a lighter route to the measure-zero leg directly on the DLN
product's last-layer structure, so this general lemma is **off that critical path**.
It is committed as reusable network-free `Core` bedrock for any future
measure-zero / almost-everywhere need (e.g. genericity arguments).

Codex architecture consult (gpt-5.x, xhigh) archived under
`threads/b-mvpoly-zeroset/codex/`.
