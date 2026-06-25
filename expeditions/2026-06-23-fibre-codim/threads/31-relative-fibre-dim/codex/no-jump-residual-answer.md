CRUX VERDICT: **no-jump WALLS for the closed-fibre route**: module generic freeness does not apply, and closed-fibre homogeneity alone does not identify the generic fibre. It is avoidable only by proving an explicit gauge/birational trivialization; that does **not** need algebra-case generic freeness, but the required product/base-change trdeg lemma is not packaged in Mathlib v4.29.

**Q1(a).** No. The landed theorem is finite-module generic freeness:

`Module.exists_free_localizedModule_of_isDomain` / `Module.exists_flat_localizedModule_of_isDomain`

It requires `Module.Finite R M`. For `O(Mat^{=r}) → O(Z₀)`, the target is finite type as an algebra, not finite as a module when relative dimension is positive. So the module theorem cannot fire on this map.

**Q1(b) / Q2.** Homogeneity of closed fibres is not enough by itself. It proves:

`∀ y : Mat^{=r}(k), (Z₀)_y ≅ (Z₀)_E`

for closed `k`-points, hence all closed rank-`r` fibres have the same dimension. But the generic fibre is over `Spec K(Mat^{=r})`, not over a `k`-point, so it is not literally obtained by translating `E`.

To turn this into generic-fibre equality you need one of:

1. a general fibre-dimension/no-jump theorem, typically via generic flatness for finite-type algebras or relative Noether normalization; this is the absent wall, or
2. an explicit local section/trivialization of the orbit map on a dense chart:
   `f⁻¹(U) ≃ U × F₀`.

The second proof does **not** re-incur algebra generic freeness. It is direct algebra from a chart isomorphism. But Mathlib v4.29 does not have a ready homogeneous-space lemma of the form “transitive equivariant morphism has generic fibre dimension equal to closed fibre dimension.”

**Q3.** Algebraically, the gauge-trivialization route is the clean dodge:

`Z₀|_U ≃ U × F₀`
implies
`K(Z₀) ≃ K(Mat^{=r})(F₀)`
and then
`trdeg_{K(Mat^{=r})} K(Z₀) = trdeg_k K(F₀) = dim F₀`.

This avoids semicontinuity and avoids algebra-case generic freeness. But it is not a v4.29 one-liner. I found the relevant present lemmas:

`trdeg_add_eq`  
`AlgEquiv.trdeg_eq`  
`MvPolynomial.trdeg_of_isDomain`

I did **not** find a packaged product/base-change trdeg lemma such as
`trdeg K (K ⊗[k] A) = trdeg k A`
or the corresponding fraction-field version. So Q3 is mathematically the right dodge, but in Lean it still costs a small custom algebra layer: chart ring isomorphism/localization, domain or geometric-integrality handling for the product chart, fraction-field identification, and a base-change trdeg invariance lemma assembled from the trdeg API.

Honest module count for the no-jump residual: closed-fibre route needs the absent algebra generic-freeness/relative-Noether-normalization style theorem. Gauge-trivialization route avoids that wall, but requires new local chart algebra plus a custom product/base-change trdeg lemma; it is not already landed in Mathlib v4.29.