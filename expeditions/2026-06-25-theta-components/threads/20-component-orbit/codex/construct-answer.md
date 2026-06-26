**Verdict:** choose **(ii) pure smoothness transport through the chart**. Do not build the shifted-orbit iso `A ≅ C × A^δ` for this goal.

1. **`A ≅ C × A^δ` should not be treated as true.** The chart gives a **localized** product:
   `O(Σ̄^r)[1/dsig] ≃ SchurLoc ⊗ sweepFibreRing`, not a global component isomorphism. It also uses the **full-`d` sigma orbit** `(B)`, not the shifted `(d-r)` orbit `(C)`. Even if you later prove stable-looking facts like `B ≅ A × A^δ` and `B ≅ C × A^ε`, cancellation is not valid in this category. Dimension would force `ε = 2δ` in your numerical story, but that still would not imply `A ≅ C × A^δ`.

2. **Do not re-target the consumer at shifted `(C)`.** If you target `(B)`, avoid a global `MvPolynomial η (sweepFibreRing⧸I) ≃ orbitRing (realizerD m)` interface unless you actually prove that global unlocalized statement. The chart naturally supports a **localized pointed product** interface, which is enough for smoothness.

   The CA mechanism you want is:

   `formal smoothness descends along an algebra retract`.

   In Mathlib terms, package it using `Algebra.FormallySmooth.of_split`. Since
   `Algebra.IsSmoothAt k p` is just `Algebra.FormallySmooth k (Localization.AtPrime p)`, the local version is:

   If localized maps
   `A_p → B_Q → A_p`
   compose to `id`, and `B_Q` is formally smooth over `k`, then `A_p` is formally smooth over `k`.

   For polynomial/Schur factors this comes from the section “evaluate affine variables at a chosen `k`-point” and the inclusion of constants. Supporting transport lemmas are `Algebra.FormallySmooth.iff_of_equiv`, `Algebra.basicOpen_subset_smoothLocus_iff_smooth`, and `Algebra.IsSmoothAt.exists_notMem_smooth`.

3. **Clean rung sequence for unconditional fibre smoothness:**

   Let `R = sweepFibreRing`, `I ∈ TopDimMinPrimes R`.

   1. Extend `I` to the Schur-polynomial side: `P = Ideal.map C I` in `MvPolynomial SchurVar R`; use the landed W2/top-prime machinery and `chartGfib_not_mem...` to localize it.

   2. Transport `P[1/chartGfib]` across the chart equivalence to a prime on `Away chartDsig`.

   3. Contract that prime back to a sigma top component `q` of `O(Σ̄^r)`. The localization survival lemmas give top-dimensionality and `dsig ∉ q`.

   4. Apply the built sigma labeling:
      `(O(Σ̄^r) ⧸ q) ≃ₐ[k] orbitRing (realizerD m)` over the **full dimension vector `d`**.

   5. Use `OrbitSmooth.isSmoothAt_normalFormIdeal` plus the existing component bridge
      `isSmoothAt_minimalPrime_of_componentEquiv_domain`
      to get `Algebra.IsSmoothAt k q` on the sigma ring.

   6. Localize and transport smoothness through:
      sigma ring → `Away chartDsig` → chart product `SchurLoc ⊗ R`.

   7. Descend from the Schur product to `R` at `I` by the retract lemma above. If the smoothness is first obtained at the generic Schur prime, use `IsSmoothAt.exists_notMem_smooth` to get a smooth basic open, then choose a Schur `k`-point avoiding its witness; evaluation gives the split map and a fibre basic open `R_g` with `g ∉ I`.

Existing C3 is not the needed reverse direction; its headline assumes fibre smoothness to make the chart smooth, so using it here would be circular. Reuse its localization/product utilities, but add the reverse “smooth product chart ⇒ smooth fibre factor” retract descent.