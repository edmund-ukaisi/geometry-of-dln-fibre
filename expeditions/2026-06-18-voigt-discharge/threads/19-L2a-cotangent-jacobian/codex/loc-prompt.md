<task>
Lean 4 + Mathlib v4.29. LAST sorry of a proof. A finrank equality for cotangent localization.

CONTEXT:
- `k : Field`, `A : CommRing`, `[Algebra k A]`, `m : Ideal A` maximal, with `A ⧸ m ≃ₐ[k] k` (a k-rational
  point: `m = ker (ε : A →ₐ[k] k)`, ε surjective). So `m.IsMaximal`, `m.IsPrime`.
- `m.Cotangent` (= `m ⧸ m²`) is a `k`-module (A is a k-algebra; it's killed by m so an `A/m ≃ k`-module).
- `Localization.AtPrime m` is a local ring; `CotangentSpace (Localization.AtPrime m) = maximalIdeal(_).Cotangent`,
  a module over `ResidueField (Localization.AtPrime m) = m.ResidueField` which `≃ k`.

GOAL (the sorry):
  `finrank k (IsLocalRing.CotangentSpace (Localization.AtPrime m)) = finrank k (m.Cotangent)`.

CONFIRMED BRICKS:
- `Module.Flat A (Localization.AtPrime m)` (instance, via `Mathlib.RingTheory.Flat.Localization`).
- `Ideal.tensorCotangentEquiv A T m : T ⊗[A] m.Cotangent ≃ₗ[T] (m.map includeRight.toRingHom).Cotangent`
  for `T` flat over `A`, where `includeRight : S →ₐ[R] T ⊗[R] S` ... CAUTION: here it's
  `Algebra.TensorProduct.includeRight : A →ₐ[A] T ⊗[A] A`? The `tensorCotangentEquiv R T I` is stated with
  R the base, S the ring containing I, T flat over R. I want R := A, S := A, T := Localization.AtPrime m,
  I := m. So `m.tensorCotangentEquiv A (Localization.AtPrime m) : T ⊗[A] m.Cotangent ≃ₗ[T] (m.map (includeRight : A →+* T⊗[A]A)).Cotangent`.
  But I need `(m.map (algebraMap A T)).Cotangent = (maximalIdeal T).Cotangent`. There's a mismatch:
  includeRight lands in `T ⊗[A] A`, not `T`. Is there `tensorCotangentEquiv` specialized to S = R = A so
  `T ⊗[A] A ≃ T` collapses? Or a cleaner localization-cotangent lemma?
- `Localization.AtPrime.map_eq_maximalIdeal : m.map (algebraMap A (Localization.AtPrime m)) = maximalIdeal (Localization.AtPrime m)`.
- `Module.finrank_baseChange : finrank R (R ⊗[S] M) = finrank S M`.
- `Module.finrank_tensorProduct : finrank R (M ⊗[S] M') = finrank R M * finrank S M'`.
- residue: `m.ResidueField`, `Ideal.bijective_algebraMap_quotient_residueField (m) [m.IsMaximal] : A⧸m ≃ m.ResidueField`.

KEY STEPS I expect:
1. `CotangentSpace (AtPrime m) = (maximalIdeal (AtPrime m)).Cotangent = (m.map (algebraMap A T)).Cotangent`
   (via map_eq_maximalIdeal).
2. `tensorCotangentEquiv` gives `T ⊗[A] m.Cotangent ≃ₗ[T] (that).Cotangent` — need includeRight↔algebraMap.
3. finrank over k: `finrank k (T ⊗[A] m.Cotangent)`. Since `m.Cotangent` is a `k`-module killed by m,
   `T ⊗[A] m.Cotangent ≅ (T/mT) ⊗[k] m.Cotangent ≅ κ(m) ⊗[k] m.Cotangent ≅ k ⊗[k] m.Cotangent ≅ m.Cotangent`
   (rational point: κ = k). So `finrank k (T ⊗[A] m.Cotangent) = finrank k m.Cotangent` — via finrank_baseChange?
   But finrank_baseChange is `finrank R (R ⊗[S] M) = finrank S M` — does that apply with R = k? No, the tensor
   is over A not k. Need: `finrank k (T ⊗[A] m.Cotangent) = finrank k m.Cotangent` somehow. Is there a cleaner
   route, e.g. m.Cotangent is finite k-dim and T⊗[A]- is an iso onto it over the residue?
</task>

<output_contract>
Give the cleanest COMPLETE Lean proof (or tight skeleton, each step a named lemma + simp set) of
  `finrank k (IsLocalRing.CotangentSpace (Localization.AtPrime m)) = finrank k (m.Cotangent)`.
Address precisely:
1. The `includeRight` vs `algebraMap A T` matching in `tensorCotangentEquiv` (the `T ⊗[A] A ≃ T` collapse).
   Name the exact lemma/equiv. If there's a cleaner cotangent-localization lemma than tensorCotangentEquiv,
   name it.
2. The finrank-over-k transport `finrank k (T ⊗[A] m.Cotangent) = finrank k m.Cotangent`. Which lemma?
   (finrank_baseChange variants, or m.Cotangent being a k-module so T⊗[A]m.Cot ≅ m.Cot as k-spaces.)
3. The residue-field κ(AtPrime m) = k step and how it makes the finranks over the right field agree.
Name every lemma; tag uncertain ones "verify name". Prefer a proof that elaborates.
</task_unused>
</output_contract>

<grounding_rules>
- Tag uncertain lemma names "verify name".
- Be decisive about whether tensorCotangentEquiv is the right tool or if there's a more direct localization-
  cotangent finrank lemma in Mathlib v4.29.
</grounding_rules>
