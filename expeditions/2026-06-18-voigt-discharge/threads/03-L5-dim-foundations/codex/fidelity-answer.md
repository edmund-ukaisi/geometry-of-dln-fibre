**1. Q1-VERDICT:**
Yes. Textbook-standard: if `A → S` is integral and injective, then `dim S = dim A`. The inequality `dim S ≤ dim A` uses only integrality: strict chains of primes in `S` contract to strict chains in `A` by incomparability. The reverse inequality `dim A ≤ dim S` needs enough surjectivity on spectra to start lifting chains; injectivity is sufficient but not minimal. For integral maps, the standard weaker condition is `Spec S → Spec A` surjective, equivalently `ker f ⊆ nilrad(A)`. Injectivity enters only to ensure the first prime in a chain of `A` has some prime of `S` lying over it; going-up handles the rest.

**2. Q1-NONINJECTIVE:**
For an integral noninjective map, the correct general statement is `dim S = dim(A / ker f)`, not necessarily `dim A`. For example `A → A/I` is integral and can drop dimension. This does not contradict `dim S ≤ dim A`, since chains in `S` contract to chains in `A` lying inside `V(I)`.

**3. Q2-COUNTEREXAMPLE:**
No, `comap` is not order-reflecting for general integral injective extensions. Let `A = k[x]`, `S = k[x] × k[x]`, and let `f : A → S` be the diagonal map. This is finite, hence integral, and injective. Take primes
`a = (0) × k[x]` and `b = k[x] × (x)` in `S`. Then `f⁻¹(a) = (0) < (x) = f⁻¹(b)`, but `a` and `b` are incomparable in `S`, so certainly `a < b` is false.

**4. Q2-ROUTE:**
Yes. The sound textbook route for `dim A ≤ dim S` is direct chain lifting: start with `p₀ < ... < pₙ` in `A`, choose `Q₀` over `p₀` by lying-over, then use going-up inductively to get `Q₀ < ... < Qₙ` with `Qᵢ ∩ A = pᵢ`. Injectivity is used only to ensure every `p₀` contains `ker f`; more generally `ker f ⊆ nilrad(A)` or surjectivity of `Spec S → Spec A` suffices.
