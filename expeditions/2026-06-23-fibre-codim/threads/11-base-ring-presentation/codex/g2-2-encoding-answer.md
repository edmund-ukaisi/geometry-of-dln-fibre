**Recommendation:** use option **B**, but do not make `Ideal.quotientKerAlgEquivOfSurjective` the main proof. Build the Schur map
`ψ : A_eng →ₐ[k] S_d`, localize it to `ψd : A_d →ₐ[k] S_d`, quotient by the explicit graph ideal `J`, then build the inverse from free variables. Kernel-identification is more brittle than explicit inverse maps.

Use these rings:

```lean
A  := MvPolynomial (RepCoord ![q,p]) k
Ad := Localization.Away dA
S  := MvPolynomial (SchurVar r b c) k
Sd := Localization.Away dS

Iad := I.map (algebraMap A Ad)
J   := Ideal.span (Set.range fun ab : Fin b × Fin c =>
          algebraMap A Ad (relA ab))
```

where

```lean
relA (aβ) = dA * B22A aβ.1 aβ.2
            - (B21A * ΔA.adjugate * B12A) aβ.1 aβ.2
```

The primary map is:

```lean
ψ₀ : A →ₐ[k] Sd := MvPolynomial.aeval fun x =>
  match blockOfCoord x with
  | Δ i j    => algebraMap S Sd (X (Sum.inl (i,j)))
  | B12 i j  => algebraMap S Sd (X (Sum.inr (Sum.inl (i,j))))
  | B21 a i  => algebraMap S Sd (X (Sum.inr (Sum.inr (a,i))))
  | B22 a j  =>
      algebraMap S Sd ((B21S * ΔS.adjugate * B12S) a j)
        * IsLocalization.Away.invSelf dS
```

Then prove `ψ₀ dA = algebraMap S Sd dS` using `AlgHom.map_det`/`RingHom.map_det`, and localize with `IsLocalization.liftAlgHom` over `Submonoid.powers dA`.

For the quotient isomorphism, use:

- `Ideal.Quotient.liftₐ` to get `Ad ⧸ J →ₐ[k] Sd`.
- Build the inverse `S →ₐ[k] Ad ⧸ J` by sending the free Schur variables to the corresponding engine variables, then localize it to `Sd →ₐ[k] Ad ⧸ J`.
- Prove inverse laws with `IsLocalization.algHom_ext` and `MvPolynomial.algHom_ext`.

This avoids proving `ker ψd = J` directly.

For the Schur expression, yes: use `Matrix.adjugate`, not `Matrix.inv`, in polynomial/localized rings. Define the numerator in `S`, then map it:

```lean
schurNumS a j : S :=
  (B21S * ΔS.adjugate * B12S) a j

forcedB22 a j : Sd :=
  algebraMap S Sd (schurNumS a j) * IsLocalization.Away.invSelf dS
```

Useful lemmas: `Matrix.mul_adjugate`, `Matrix.adjugate_mul`, `RingHom.map_adjugate`, `AlgHom.map_adjugate`, `RingHom.map_det`, `AlgHom.map_det`, `IsLocalization.Away.mul_invSelf`, `IsLocalization.Away.algebraMap_isUnit`. For evaluated matrix inverses, use `Matrix.nonsing_inv_apply` or the landed `rank_fromBlocks_eq_card_iff_schur_inv`.

For `relA ∈ I`, do **not** rely on the “`det Δ = 0` is trivial” case split. It is not trivial for
`dA * B22 - B21 adj Δ B12`. Instead prove `relA` is the bordered `(r+1)×(r+1)` minor, up to sign, and use the rank-minor bridge directly. The repo already has the right API: `MvPolynomial.mem_vanishingIdeal_iff`, `DLNFibre.Core.submatrix_det_eq_zero_of_rank_le`, and `DLNFibre.Core.rank_le_iff_forall_submatrix_det_eq_zero`. If you still need “nonzero minor implies rank ≥ r”, prove it via `Matrix.isUnit_iff_isUnit_det`, `Ne.isUnit`, `Matrix.rank_of_isUnit`, and the custom `rank_submatrix_le_rank`; Mathlib v4.29 does not package that exact lemma.

For height transport:

```lean
have hdisj :
    Disjoint (Submonoid.powers dA : Set A) (I : Set A) :=
  (Ideal.disjoint_powers_iff_notMem dA hI.isRadical).2 hdA_notMem_I

have hIad :
    (I.map (algebraMap A Ad)).height = I.height :=
  IsLocalization.height_map_of_disjoint (Submonoid.powers dA) I hdisj
```

Other relevant names: `IsLocalization.height_comap`, `IsLocalization.primeHeight_comap`,
`IsLocalization.isPrime_of_isPrime_disjoint`, `IsLocalization.comap_map_of_isPrime_disjoint`,
`Ideal.height_strict_mono_of_is_prime`.

I would make the headline theorem the **ideal equality**

```lean
theorem localized_determinantal_ideal_eq_graph :
  Iad = J
```

and then expose the corollary

```lean
noncomputable def localizedBaseEquivSchur :
  (Ad ⧸ Iad) ≃ₐ[k] Sd
```

The equality is the robust API; the `AlgEquiv` is what downstream code composes with.

Biggest v4.29 friction risk: proving `height J = b*c`. There is no canned localized graph-ideal height theorem. Dodge it by first proving the reindexed presentation
`Ad ≃ₐ[k] MvPolynomial (Fin b × Fin c) Sd`, using `MvPolynomial.renameEquiv`, `MvPolynomial.sumAlgEquiv`, and localization transport, then show `J` is a translated coordinate ideal. Do not leave this as an implicit “dimension is obvious” step.