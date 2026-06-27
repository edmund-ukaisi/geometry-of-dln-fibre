1. **Route Choice**

1. **FLOOR**: cheapest honest landing. It isolates the real missing input as a hypothesis: either `Algebra.IsSmoothAt k qSweep` or `IsUnit` of the chosen Jacobian minor.
2. **LEAD**: mathematically cleanest unconditional route, but Lean-costly because it needs tensor-local smoothness plus a local comparison between the reducible fibre and one orbit-closure component.
3. **FALLBACK**: direct but probably most expensive, since the hard step is exactly the thin Mathlib zone: determinantal rank/Jacobian minor formalisation.

2. **LEAD Soundness**

Yes, the mathematical chain is sound, but only if formulated with an actual prime of the tensor product.

Given `e : C ≃ₐ[k] A ⊗[k] B`, `[Smooth k A]`, a prime `P : Spec (A ⊗[k] B)`, and contraction `q` of `P` along `B →ₐ[k] A ⊗[k] B`, the desired lemma is essentially:

`Algebra.IsSmoothAt k q` for `B`  
`+ Smooth k A`  
`⇒ Algebra.IsSmoothAt k P` for `A ⊗[k] B`.

Then transfer across `e` by `FormallySmooth.of_equiv` / `iff_of_equiv`.

The wall is not “primes of tensor products are products”; avoid that formulation. The missing Lean lemma is a local base-change/localization statement, something like:

`Localization.AtPrime P` is a localization of  
`Localization.AtPrime q ⊗[k] A`

at the prime induced by `P`.

Naive `Localization.AtPrime P ≃ A ⊗[k] Localization.AtPrime q` is generally false or too weak; one must localize again at the induced tensor prime. That localization-of-base-change bookkeeping is the Mathlib wall.

3. **LEAD Crux**

Inference: `sweepFibreRing` is the whole reduced fibre ring, hence still reducible when `θ ≥ 2`. It is not globally a single shifted orbit-closure ring unless you have defined it componentwise.

So `OrbitSmooth` applies to one component ring `orbitRing M`, not directly to `sweepFibreRing`.

You need a local comparison lemma:

For a reduced finite union with ideal `I = ⋂ Iᵢ`, at a point/prime lying on component `I_M` and not on the other components,

`Localization.AtPrime m (R ⧸ I) ≃ₐ[k] Localization.AtPrime m_M (R ⧸ I_M)`.

Equivalently, for every other component `I_j`, produce `s_j ∈ I_j` with `s_j ∉ m`; after localizing at `m`, those other components become the unit ideal.

This is standard scheme-theoretically, but in Lean it is substantial unless already banked. The missing lemma is a quotient-by-intersection localization comparison, plus the geometric proof that the normal-form point for `M` is not on the other top components.

4. **Verdict**

Yes: the FLOOR is the rational bounded-tide landing.

Best conditional theorem names would be along the lines of:

`isSmoothAt_chart_of_isSmoothAt_sweepPoint`

or, for the submersion route,

`isSmoothAt_chart_of_subJacobian_isUnit`.

Cost to make LEAD unconditional: prove the tensor-local smoothness lemma from Q2, prove the component-localization equivalence from Q3, identify the shifted component ring with `orbitRing M`, transport `OrbitSmooth`, then transport across the chart iso.

Cost to make FALLBACK unconditional: formalise enough determinantal/Jacobian rank theory to prove the chosen minor is a unit at the target point, or import the Singular/rank certificate into Lean. That is likely heavier than the LEAD commutative-algebra plumbing.