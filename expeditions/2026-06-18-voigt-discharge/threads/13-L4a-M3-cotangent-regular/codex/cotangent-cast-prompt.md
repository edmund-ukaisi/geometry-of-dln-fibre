<task>
Lean 4 + Mathlib v4.29.0. PURE LEAN-IDIOM question — I have the math; I need the cleanest tactic incantation
for ONE dependent-type-cast step. No new theory.

Setup (all real Mathlib at v4.29):
- `R` a Noetherian local ring, `[Algebra k R]`, `κ := IsLocalRing.ResidueField R` (= `R ⧸ maximalIdeal R`).
- `CotangentSpace R := (maximalIdeal R).Cotangent`, an `Ideal.Cotangent`, with `Module (ResidueField R)` instance.
- `Ideal.Cotangent I := I ⧸ (I • ⊤)`; it `deriving Module (R ⧸ I)`. So `(maximalIdeal R).Cotangent` has
  `Module (R ⧸ maximalIdeal R) = Module κ`, but `(RingHom.ker (algebraMap R κ)).Cotangent` only has
  `Module (R ⧸ RingHom.ker (algebraMap R κ))`, NOT syntactically `Module κ`.
- I have `hker : RingHom.ker (algebraMap R κ) = maximalIdeal R` (from `ResidueField.algebraMap_eq` + `ker_residue`).
- `hsurj : Function.Surjective (algebraMap R κ)`.
- The conormal map `f := KaehlerDifferential.kerCotangentToTensor k R κ` has type
  `(RingHom.ker (algebraMap R κ)).Cotangent →ₗ[R] κ ⊗[R] Ω[R⁄k]`, and I have `hinj : Function.Injective f`.
- `Module.Finite κ (κ ⊗[R] Ω[R⁄k])` is available.

What WORKS already (verified compiling):
```lean
have hbound : Module.finrank κ ((RingHom.ker (algebraMap R κ)).Cotangent)
      ≤ Module.finrank κ (κ ⊗[R] Ω[R⁄k]) :=
  LinearMap.finrank_le_finrank_of_injective
    (f := f.extendScalarsOfSurjective hsurj) hinj
```
Here `f.extendScalarsOfSurjective hsurj : (RingHom.ker (algebraMap R κ)).Cotangent →ₗ[κ] κ ⊗[R] Ω[R⁄k]`, and the
κ-module on the domain `(RingHom.ker ...).Cotangent` is the one PROVIDED by `extendScalarsOfSurjective` (built on
the fly from the R-module + `hsurj`). `LinearMap.extendScalarsOfSurjective` is at `Mathlib/Algebra/Algebra/Basic.lean`.

THE GOAL I must close (the LHS uses `CotangentSpace R = (maximalIdeal R).Cotangent` and ITS native `Module κ`):
```lean
⊢ Module.finrank κ (CotangentSpace R) ≤ Module.finrank κ (κ ⊗[R] Ω[R⁄k])
```
i.e. I need:
```lean
Module.finrank κ ((maximalIdeal R).Cotangent) = Module.finrank κ ((RingHom.ker (algebraMap R κ)).Cotangent)
```
THE TROUBLE: `rw [hker]` / `rw [show maximalIdeal R = RingHom.ker ... ]` FAILS with the dependent-motive error
("motive is not type correct" — the `Module κ` instance on `(·).Cotangent` depends on the rewritten ideal). And
`subst` doesn't apply (neither side of `hker` is a local hypothesis variable). `simp only [CotangentSpace]`
unfolds the abbrev fine but then I'm stuck rewriting the ideal inside `.Cotangent`.

A SUBTLETY to be careful about: the κ-module instance on `(maximalIdeal R).Cotangent` (the `deriving Module (R⧸I)`
one) vs the κ-module that `extendScalarsOfSurjective` puts on `(RingHom.ker ...).Cotangent` — after transporting
along `hker`, are these the SAME instance, or do I need `Subsingleton`/instance-irrelevance to identify them? If
they could differ, the finrank equality might need a κ-linear equiv that matches the right instances. Address this.

OUTPUT: give me the SHORTEST robust tactic block (or term) that closes the goal from `hbound` + `hker` + `hsurj`.
Rank 2-3 approaches by robustness:
(a) build a κ-`LinearEquiv` between the two `.Cotangent` types from `hker` and use `LinearEquiv.finrank_eq` —
    show me exactly how to construct that equiv handling the `Module κ` instance mismatch (e.g. via
    `LinearEquiv.ofEq`, `Ideal.Cotangent` functoriality, or a `hker ▸` cast on `LinearEquiv.refl` + which side);
(b) a `Module.finrank` congr / `Eq.mpr` with explicit motive avoiding the bad-motive `rw`;
(c) prove `Function.Injective (g.extendScalarsOfSurjective hsurj)` where `g` is the map TRANSPORTED to domain
    `(maximalIdeal R).Cotangent` (`g := hker ▸ f`), i.e. how to transport `hinj` to `Injective (hker ▸ f)`
    robustly (the `▸`-on-a-proof motive). For (c) give the exact `▸`/`Eq.rec`/`cast` term that typechecks.
For each, mark [CONFIRMED-recalled]/[GUESS] on every Mathlib name, and flag if it risks the same bad-motive error.
</task>

<output_contract>
Ranked approaches (a)/(b)/(c), each a concrete Lean snippet that I can paste and build, shortest first. Exact
Mathlib lemma names with confidence tags. One closing line: RECOMMENDED = (x), and the single snippet to use.
Keep it tight — this is one cast step, not a proof.
</output_contract>

<grounding_rules>
Be explicit about the `Module κ` instance-defeq concern: whether the two cotangent κ-module instances are defeq
after transport (so `LinearEquiv.finrank_eq` / a refl-cast just works) or whether instance-mismatch will bite.
If you are not sure a lemma exists at v4.29, mark [GUESS] and give its mathematical content so I can grep.
</grounding_rules>
