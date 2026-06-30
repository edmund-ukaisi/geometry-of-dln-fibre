# Decorrelated review: k-rationality discharge over a non-algebraically-closed field

You are a decorrelated second mathematician reviewing a Lean 4 formalisation step. Answer
mathematically, from your own knowledge — do NOT defer to the description below; if it is wrong,
say so and explain why. Distinguish clearly what is a mathematical fact vs an inference.

## Setting

Field `k` (NOT assumed algebraically closed; the target application is `k = ℝ`, also `ℚ`). `k` is
perfect (`CharZero ⟹ PerfectField`) and infinite. We have a finite-type `k`-domain
`A = MvPolynomial σ k ⧸ I` (`σ` finite, `I` prime), the affine coordinate ring of an irreducible
affine variety `X = Spec A` over `k`.

There is a group `G = ∏_v GL_{d_v}(k)` of `k`-points (literal invertible matrices over `k`) acting
`k`-linearly on the ambient affine space, and `X` is the Zariski closure of a single orbit `O = G·M`
of `k`-rational points. Concretely:
- For each `P ∈ G`, the orbit point `μ(P) = canonicalCoord(P·M)` is a point of `(σ → k)` — a literal
  `k`-valued tuple.
- `I = vanishingIdeal(O)` (the ideal of polynomials vanishing on the orbit), prime (orbit irreducible).
- For each `P ∈ G`, evaluation at `μ(P)` descends to a SURJECTIVE `k`-algebra homomorphism
  `eval_P : A → k` (surjective because it splits the structure map `k → A`), with kernel a maximal
  ideal `m_P := ker(eval_P)`. By the first isomorphism theorem `A ⧸ m_P ≃ₐ[k] k`.

The goal: produce a point `m` of `Spec A` that is BOTH (a) smooth (the local ring `A_m` is
regular / formally smooth over `k`) AND (b) `k`-rational, meaning the residue field
`κ(m) := ResidueField(A_m) = Frac(A ⧸ m)` is `≃ₐ[k] k` (equal to `k`, NOT a nontrivial finite
extension).

## The discharge chain under review

1. **Density of orbit points.** The set `S = { m_P : P ∈ G }` of orbit-point maximal ideals is dense
   in `Spec A`: any `g ∈ A` vanishing at all `m_P` lies in `vanishingIdeal(O) ⧸ I = ⊥`, so the
   vanishing ideal of `S` is `⊥`, and `A` reduced (domain) gives closure `= Spec A`.
2. **Generic smoothness over a perfect field.** The smooth locus of the structure morphism
   `Spec A → Spec k` is OPEN and DENSE (uses `k` perfect + `A` reduced; `dense_smoothLocus_of_perfectField`).
   NO algebraic closedness assumed.
3. **Intersection.** Dense `S` meets open-dense smooth locus ⟹ ∃ `P` with `m_P` smooth.
4. **`k`-rationality of `m_P`.** Because `m_P = ker(eval_P)` with `eval_P : A → k` surjective
   `k`-algebra hom, `A ⧸ m_P ≃ₐ[k] k`. Since `A ⧸ m_P` is already a field (m_P maximal), its fraction
   field `κ(m_P) = ResidueField(A_{m_P})` equals it, so `κ(m_P) ≃ₐ[k] k`. Hence `m_P` is `k`-rational.
5. **Transport to a chosen base point.** A `G`-automorphism of `A` carries `m_P` to a fixed
   normal-form point `m_M`, preserving both smoothness (iso of local rings) and `k`-rationality.
6. **Cotangent dimension.** At the smooth `k`-rational point: `finrank_{κ(m)}(cotangent) = dim A_m`
   (regular local ring, M3); then `finrank_k(cotangent) = finrank_{κ}(cotangent)` BECAUSE `κ ≃ₐ[k] k`
   gives `[κ : k] = 1` (this is where `k`-rationality is load-bearing — over a degree-`e` extension it
   would be `e · dim`).

## Questions (answer each explicitly)

1. **Is the core claim sound?** Over a non-algebraically-closed field, does a dense set of
   `k`-RATIONAL points (orbit points, each with residue field exactly `k`) meeting the smooth locus
   yield a smooth point that is genuinely `k`-rational (residue field `= k`), as opposed to merely a
   smooth closed point whose residue field could be a nontrivial finite extension of `k`? Is the
   distinction handled correctly here, i.e. does taking the smooth point FROM the dense set of
   `k`-rational orbit points (rather than from an arbitrary closed point of the smooth locus) close
   the gap?

2. **Is `κ(m) ≃ₐ[k] k` (residue field equals `k`) the correct formalisation of "`k`-rational point"?**
   Are there pitfalls — e.g. is "closed point with residue field `k`" the same as "`k`-point" here, or
   could there be a subtlety (separability, the difference between a `k`-morphism `Spec k → X` and a
   closed point with residue field `k`)?

3. **Is step 4's first-iso argument airtight?** `eval_P : A → k` surjective `k`-algebra hom, kernel
   `m_P` maximal, `A ⧸ m_P ≃ₐ[k] k`, and the residue field of the localisation equals `A ⧸ m_P`
   because that quotient is already a field. Any gap?

4. **Is the `[κ:k] = 1` step in 6 the genuine and only place `k`-rationality is consumed?** Confirm
   that if the point were merely smooth-over-`k̄` (residue field a degree-`e > 1` extension), the
   cotangent-`finrank`-over-`k` would be `e · dim`, so the equality `finrank_k(cotangent) = dim` would
   FAIL — i.e. `k`-rationality is not decorative.

5. **Any smuggled algebraic-closedness?** Does any step secretly need `k` algebraically closed (or a
   stronger hypothesis than perfect+infinite)? In particular: generic smoothness density over a
   perfect (non-closed) field, and the existence of a `k`-rational point in the dense orbit.

Be concise and precise; flag any actual error or hidden assumption.
