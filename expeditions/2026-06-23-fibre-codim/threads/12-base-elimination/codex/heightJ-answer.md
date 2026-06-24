**VERDICT**
Route **C** is lowest-friction. Mathlib v4.29 does **not** appear to have a direct coordinate-ideal height theorem, but Route C reduces the job to one reusable local lemma; Routes A/B ask for broader dimension/catenary API that is more likely to sprawl.

**Chosen Route Lemmas**
1. Translation graph to coordinate ideal:
   - `AlgEquiv.ofAlgHom` `(confident-exists-v4.29)`
   - `MvPolynomial.algHom_ext` `(confident-exists-v4.29)`
   - `MvPolynomial.aeval_X` `(confident-exists-v4.29)`
   - `Ideal.map_span` `(confident-exists-v4.29)`
   - `RingEquiv.height_map` / `RingEquiv.height_comap` `(confident-exists-v4.29)`
   - `DLNFibre.Core.graphIdeal` `(LANDED/local)`
   - `DLNFibre.Core.graphIdeal_isPrime` `(LANDED/local)`

2. Coordinate ideal upper bound:
   - `Ideal.height_le_spanFinrank` `(confident-exists-v4.29)`
   - `Submodule.spanFinrank_span_le_ncard_of_finite` `(confident-exists-v4.29)`
   - `Set.ncard_range_of_injective` `(confident-exists-v4.29)`
   - `MvPolynomial.X_injective` `(confident-exists-v4.29)`

3. If proving coordinate height via landed catenary/unlocalization:
   - `height_add_ringKrullDim_quotient_eq_card` `(LANDED/local)`
   - `MvPolynomial.ringKrullDim_of_isNoetherianRing` `(confident-exists-v4.29)`
   - `ringKrullDim_eq_zero_of_field` `(confident-exists-v4.29)`
   - `ringKrullDim_eq_of_ringEquiv` `(confident-exists-v4.29)`
   - `IsLocalization.height_map_of_disjoint` `(confident-exists-v4.29)`
   - `DLNFibre.Core.graphIdealQuotientEquiv` `(LANDED/local)`

**THE WALL**
Missing/hard lemma:

```lean
coordinateIdeal_height :
  (Ideal.span (Set.range (MvPolynomial.X : ι → MvPolynomial ι R))).height
    = (Nat.card ι : ℕ∞)
```

No direct Mathlib v4.29 theorem found.

Cheapest workaround for your case: prove the coordinate ideal first before localization over
`MvPolynomial SchurVar k`, use `graphIdealQuotientEquiv (fun _ ↦ 0)` to identify the quotient with
`MvPolynomial SchurVar k`, apply landed `height_add_ringKrullDim_quotient_eq_card`, then transport
through localization with `IsLocalization.height_map_of_disjoint`. Disjointness is just
`detΔS ≠ 0` in the quotient domain.

**Route C Proof Sketch**
Build

```lean
translate c : MvPolynomial ι R ≃ₐ[R] MvPolynomial ι R
```

from `aeval (fun i ↦ X i - C (c i))` and inverse `aeval (fun i ↦ X i + C (c i))`, proving inverse laws by
`MvPolynomial.algHom_ext` and `MvPolynomial.aeval_X`. Then `Ideal.map_span` shows the coordinate
ideal maps to `graphIdeal c`, and `RingEquiv.height_map` transports height.

So: commit to **Route C**, but do not wait for a Mathlib coordinate-height lemma; add the local
coordinate-height lemma, preferably using the already-landed field catenary plus localization height
preservation.