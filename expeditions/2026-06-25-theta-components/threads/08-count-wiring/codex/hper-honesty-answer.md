1. **Q1.** `hper` is not derivable from `hdim + havoid`.  
   Concrete counterexample: let `A = k[t] × k[t]`, with `f = (t, 1)`. Then `dim A = 1`, and
   `S = A[1/f] ≅ k[t, t⁻¹] × k[t]`, so `dim S = 1`; hence `hdim` holds.  
   The top-dimensional minimal primes are `p₁ = (0) × k[t]` and `p₂ = k[t] × (0)`, both with quotient dimension `1`.  
   Also `f ∉ p₁` and `f ∉ p₂`, so `havoid` holds.  
   But for `p₁`, `A ⧸ p₁ ≅ k[t]` and `f̄ = t`, so `(A ⧸ p₁)[1/f̄] ≅ k[t, t⁻¹]`, whose Krull dimension is still `1`; this does **not** fail.  
   To get failure, use `A = k[t]_(t) × k[t]`, `f = (t, 1)`. Then `dim A = 1`, `S ≅ k(t) × k[t]`, so `dim S = 1`, and `havoid` holds for both top-dimensional minimal primes. For `p₁ = (0) × k[t]`, `A ⧸ p₁ ≅ k[t]_(t)` has dimension `1`, but inverting `t` gives `k(t)`, dimension `0`; hence `hper` fails.

2. **Q2.** `hper` is strong, but it is not circular. It does not mention primes of `S`, the map/comap correspondence, or cardinalities. It only says that on each already top-dimensional component `A ⧸ p`, the chosen element `f̄` does not lower Krull dimension after localization. Together with `hdim`, it implies that the localized component has dimension `dim S`, so the corresponding minimal prime of `S` is top-dimensional. That is exactly the local input needed for surjectivity, not the global conclusion itself.

3. **Q3.** Yes, the MapsTo squeeze is mathematically sound without `hper`, assuming the standard minimal-prime localization correspondence and quotient-localization identification. For `P ∈ TopDimMinPrimes S`, put `p = Pᶜ` in `A`; then `p` is minimal over `A`, and `S ⧸ P ≅ (A ⧸ p)[1/f̄]`. Since `P` is top-dimensional in `S`, `dim(S ⧸ P) = dim S = dim A` by `hdim`. The inequalities `dim((A ⧸ p)[1/f̄]) ≤ dim(A ⧸ p) ≤ dim A` then force `dim(A ⧸ p) = dim A`. No componentwise preservation hypothesis is being smuggled into that argument.

4. **Q4.** Yes, the lemma is a faithful statement of preservation of the count under avoidance plus componentwise no-drop. The counterexample in Q1 shows why `hdim + havoid` alone is insufficient: one top-dimensional component can drop while another keeps the ambient dimension unchanged. The hypotheses are not jointly vacuous; for instance, if `A` is a finitely generated `k`-domain and `f ≠ 0`, then the unique minimal prime is `(0)`, and standard affine-domain dimension theory gives `dim A[1/f] = dim A` under the usual positive-dimensional/non-field situations intended here. More generally, if every top-dimensional component is an affine domain and `f̄ ≠ 0` on each, then `hper` is exactly the expected no-drop input.

Verdict: `hper` is **required-and-honest**.