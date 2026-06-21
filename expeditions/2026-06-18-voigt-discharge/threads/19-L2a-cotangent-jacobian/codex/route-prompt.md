<task>
Lean 4 + Mathlib v4.29 (the leanprover-community pin matching toolchain v4.29.0). I am formalising a
GENERAL commutative-algebra lemma: "Zariski cotangent space = cokernel of the Jacobian" at a k-rational
point of an affine variety. I must choose the route that minimises risk of hitting an ABSENT Mathlib
sub-library, and decompose it into bounded pieces. This is the recon-flagged most-likely-to-break step.

SETUP. Fix:
- `k : Type*` `[Field k]`, `σ : Type*` `[Fintype σ]` `[DecidableEq σ]`.
- `R := MvPolynomial σ k`.
- a finite generating family `g : Fin m → R` of an ideal `I := Ideal.span (Set.range g)`.
- a k-rational point `a : σ → k` with `∀ i, MvPolynomial.eval a (g i) = 0` (so `a ∈ V(I)`).
- `A := R ⧸ I`.
- `m_A` := the maximal ideal of `A` at `a` (image in `A` of `ker (MvPolynomial.eval a : R →ₐ[k] k)`,
  equivalently `(Ideal.comap (Quotient.mk I)) ... ` — exact framing is part of what I want advised).

JACOBIAN. Define `jac : (σ → k) →ₗ[k] (Fin m → k)`,
  `jac v = fun i ↦ ∑ x, (MvPolynomial.eval a (MvPolynomial.pderiv x (g i))) • v x`
(rows = generators, columns = σ; the transpose of the usual Jacobian as a column-space map). Actually
the natural conormal direction gives the TRANSPOSE `Jᵀ : (Fin m → k) → (σ → k)` sending the i-th basis
vector to the gradient row of g_i; the cotangent is the cokernel of that. I want the headline:

  `Module.finrank k (IsLocalRing.CotangentSpace (Localization.AtPrime m_A))
     = Module.finrank k (LinearMap.ker jac)`

equivalently `= Fintype.card σ − rank(Jacobian)`. The residue field κ(m_A) = k since a is k-rational.

AVAILABLE MATHLIB BRICKS (verified to exist at this pin):
1. `IsLocalRing.CotangentSpace R := (IsLocalRing.maximalIdeal R).Cotangent` (an `Ideal.Cotangent`),
   a module over `ResidueField R`.
2. `Ideal.Cotangent`, `Ideal.toCotangent`, `Ideal.cotangentToQuotientSquare`,
   `Ideal.cotangentEquivIdeal`.
3. The CONORMAL exact sequence (KaehlerDifferential, in RingTheory/Kaehler/Basic.lean):
   `KaehlerDifferential.kerCotangentToTensor R A B : (RingHom.ker (algebraMap A B)).Cotangent →ₗ[A] B ⊗[A] Ω[A⁄R]`
   with `kerCotangentToTensor_toCotangent x = 1 ⊗ₜ D _ _ x.1`, and
   `range_kerCotangentToTensor` (when `algebraMap A B` surjective): range = ker(mapBaseChange), and
   `exact_kerCotangentToTensor_mapBaseChange`. Also `mapBaseChange`, `range_mapBaseChange`,
   `exact_mapBaseChange_map`. So for a surjection A ↠ B the sequence
   `(ker(A→B)).Cotangent → B⊗_A Ω[A/R] → Ω[B/R] → 0` is exact.
4. `MvPolynomial.mvPolynomialBasis R σ : Basis σ (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R]` with
   `(mvPolynomialBasis R σ).repr (D _ _ x) i = MvPolynomial.pderiv i x`, `Module.Free` of Ω.
5. `Ideal.CotangentBaseChange`: `Ideal.tensorCotangentEquiv R T I` for `T` flat over R:
   `T ⊗[R] I.Cotangent ≃ₗ[T] (I.map includeRight).Cotangent`. (For localization-vs-quotient comparison.)
6. The repo ALREADY has (DLNFibre/Core/SmoothPointRegular.lean) a worked conormal-sequence argument for
   the SMOOTH case: it builds `g : (maximalIdeal R).Cotangent →ₗ[R] (ResidueField R) ⊗[R] Ω[R⁄k]` for
   `R = Localization.AtPrime m` and proves it INJECTIVE (smooth), giving finrank ≤ n. My case is the
   EXACT (not just ≤) statement at an arbitrary (possibly singular) point, so I cannot use injectivity.
7. `Submodule.finrank_quotient_add_finrank`, `LinearMap.finrank_range_add_finrank_ker`,
   `Subspace.dual` / `Module.finrank_dual_eq`, etc. (cokernel ↔ ker-of-dual finrank bookkeeping).

UNCERTAIN / POSSIBLY ABSENT:
- Whether the cotangent of `B = k` over `A` (residue map) can be COMPUTED as the cokernel of the
  Jacobian WITHOUT smoothness. The exact sequence gives `m_A.Cotangent ↠ ker(mapBaseChange)` only on
  the quotient side; I need the full `m_A/m_A²` not just a quotient.
- Whether to work over `A = R⧸I` directly, or pull back to `R = MvPolynomial σ k` and use the
  `0 → I/(I∩m_R²) → m_R/m_R² → m_A/m_A² → 0` style sequence (the standard "conormal of the closed
  immersion" giving m_A/m_A² = m_R/m_R² / image(I)). The classical Jacobian criterion: with
  m_R/m_R² ≅ (σ→k) via the dx-basis at the rational point, and I/(I·m_R + ...) mapping by the gradient,
  m_A/m_A² = coker(Jacobianᵀ). I want to know which framing Mathlib supports with the fewest absent bricks.
- The localization step: relating CotangentSpace(Localization.AtPrime m_A) to m_A.Cotangent (over A).
  Is there a clean Mathlib lemma, or must I go via tensorCotangentEquiv with T = Localization (flat)?

WHAT I'VE PROVEN ELSEWHERE (so the numeric target is fixed): on a (2,2,2) example with σ of card 8,
m=6 generators (2 dets + 4 product entries), the answer is finrank = 5 = 8 − rank(J)=3.
</task>

<output_contract>
Respond in these sections, terse:

1. ROUTE CHOICE. Pick ONE of:
   (A) work in A = R⧸I via the KaehlerDifferential conormal sequence with B = k (residue map);
   (B) work in R = MvPolynomial via m_R/m_R² ≅ (σ→k) and quotient by image(I) = the gradient rows;
   (C) something else.
   State which has the FEWEST absent-brick risks and WHY. Be concrete about which Mathlib lemma carries
   each step.

2. THE KEY IDENTITY, precisely. Write the chain of iso/exact maps that ends at
   `finrank k (cotangent) = finrank k (ker jac)`. For each arrow name the exact Mathlib lemma (or flag
   "ABSENT — must prove by hand" with the precise goal it leaves).

3. LOCALIZATION. The cleanest way to get from CotangentSpace(Localization.AtPrime m_A) (local) to a
   finrank computable over A (global). Is there a finrank-preservation lemma, or is tensorCotangentEquiv
   (T = localization, flat) the route? If the latter, what's the residue-field bookkeeping (κ over the
   local ring vs A⧸m_A vs k)?

4. ABSENT-BRICK VERDICT. Is the whole lemma BOUNDED on the listed bricks, or does some step need a
   genuinely-absent sub-library? If absent, name the precise failing goal and estimate its size
   (lines / whether it is itself a multi-module sub-library). This verdict is the main thing I'm buying.

5. DECOMPOSITION. 4–8 intermediate Lean lemmas, each one a bounded step, in dependency order, that I
   should SPECIFY-with-sorry first.
</output_contract>

<grounding_rules>
- Distinguish: (i) Mathlib lemmas you are CONFIDENT exist at v4.29 from (ii) lemmas you THINK exist but
  are inferring. Tag each (ii) as "verify name". Do NOT invent lemma names with false confidence — a
  wrong name costs me a search.
- If a step needs a hand proof, say so plainly rather than gesturing at a lemma that may not exist.
- The verdict (section 4) is what I most need: be decisive about whether this is BOUNDED or hits an
  absent sub-library, and if the latter, exactly where.
</grounding_rules>
