**1. Ranking**

1. **C: bank C3, discharge C2(b), and leave only C2(a) as the named geometric conditional.**  
   **Estimate:** 250-450 lines.  
   **Best option.** This removes the fake open condition (b), banks the real chart transport, and isolates the true missing theorem.

2. **B: bank C3 and leave C2(a)+(b) as one conditional.**  
   **Estimate:** 150-300 lines.  
   Good, but less sharp: (b) is not genuinely open if the prime is the component generic point.

3. **A: attempt full C2(a)+(b) now.**  
   **Estimate:** 800-2000+ lines, high risk.  
   **Inference:** this is not just plumbing. It needs a fibre-component/orbit-closure theory not present in the current harness.

**2. C2(a)**

**Inference:** not reachable from only the count chain + B4 + `OrbitSmooth`.

The count chain proves cardinal equalities of `TopDimMinPrimes`; it does not label a given minimal prime of `sweepFibreRing` by an orbit closure. B4 gives fibre homogeneity under base change, but not decomposition of the model fibre into orbit-closure components.

Concrete missing lemma shape:

```lean
∀ I ∈ TopDimMinPrimes (sweepFibreRing k d r hp hq),
  ∃ M, Nonempty ((sweepFibreRing k d r hp hq ⧸ I) ≃ₐ[k] orbitRing M)
```

or ideal-level:

```lean
(I.comap (Ideal.Quotient.mk (vanishingIdeal k (sweepFibre k d r hp hq))))
  = orbitIdeal M
```

A weaker local-at-generic version would also suffice, but it is still the same geometric wall.

**3. C2(b)**

**Confirm.** For a component generic point, take `q := I_M` as an ideal of `R := sweepFibreRing ...`.

If `I_M ∈ minimalPrimes R`, then `I_M` is prime, `I_M ≤ q` is `rfl`, and

```lean
∀ J ∈ minimalPrimes R, J ≤ I_M → J = I_M
```

is trivial from minimality of `I_M`. This does **not** need reducedness.

Caveat: C1’ then asks for smoothness of `R ⧸ I_M` at

```lean
I_M.map (Ideal.Quotient.mk I_M) = ⊥
```

So after identifying the component with an orbit ring, `OrbitSmooth.isSmoothAt_normalFormIdeal` still needs a small “domain + smooth closed point implies smooth generic point” bridge. That bridge is small: use `Algebra.IsSmoothAt.exists_notMem_smooth`, domain implies `g ≠ 0`, then `Algebra.basicOpen_subset_smoothLocus_iff_smooth`.

**4. C3 Route**

**Checked Mathlib names:**  
`IsLocalization.tensorProduct_tensorProduct`, `IsLocalization.algEquivOfAlgEquiv`, `IsLocalization.ringEquivOfRingEquiv`, `Algebra.TensorProduct.comm`, `Algebra.TensorProduct.map`, `Algebra.basicOpen_subset_smoothLocus_iff_smooth`, `Algebra.IsSmoothAt.exists_notMem_smooth`, `Smooth.of_equiv`, `Algebra.FormallySmooth.iff_of_equiv`, `Algebra.FinitePresentation.baseChange`, `Algebra.FinitePresentation.trans`.

Clean route:

1. Prove a reusable equivalence

```lean
SchurLoc ⊗[k] Localization.Away g
  ≃ₐ[k] Localization.Away (Algebra.TensorProduct.includeRight g :
    SchurLoc ⊗[k] sweepFibreRing ...)
```

using `IsLocalization.tensorProduct_tensorProduct` plus tensor commutativity.

2. Transport

```lean
Smooth k (SchurLoc ⊗[k] Localization.Away g)
```

across that equivalence by `Smooth.of_equiv`.

3. Use the basic-open bridge already present as `isSmoothAt_of_smooth_localizationAway`.

4. Across `reducedFibre_chartDsig_tensorEquiv_reducedVariety`, either transport the basic open element back and use the same bridge, or build the AtPrime equivalence with `IsLocalization.ringEquivOfRingEquiv` and use `Algebra.FormallySmooth.iff_of_equiv`.

**Estimate:** 150-300 lines, mostly bookkeeping.

Yes: `IsSmoothAt` is preserved across the `Away g` basic open by `Algebra.basicOpen_subset_smoothLocus_iff_smooth`. Across an `AlgEquiv`, there is no need to rely on a pre-existing named `IsSmoothAt` lemma; it follows from AtPrime localization equivalence + `Algebra.FormallySmooth.iff_of_equiv`.

**5. Sharpest Check**

Try to state this exact probe:

```lean
theorem topDim_sweepFibre_component_equiv_orbitRing
    (I : Ideal (sweepFibreRing k d r hp hq))
    (hI : I ∈ TopDimMinPrimes (sweepFibreRing k d r hp hq)) :
    ∃ M, Nonempty ((sweepFibreRing k d r hp hq ⧸ I) ≃ₐ[k] orbitRing M)
```

If no existing theorem gives this, do **not** invest in full C2 this tide. Bank C3 + free generic-prime uniqueness, and leave this as the single named geometric conditional.