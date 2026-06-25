**Bottom Line**

Q3 does **not** work as stated. Krull gives only an upper bound:
`J.height ≤ C`. From `J ≤ Iad` and `Iad.height = C`, `Ideal.height_mono` gives the same direction:
`J.height ≤ Iad.height = C`. There is no lower bound, so no squeeze.

The lowest-friction route I would write is:

1. Use the block relabeling route.
2. Move to `MvPolynomial B22block Sd`, where `Sd := Localization.Away detΔS`.
3. Prove one reusable multivariable graph-ideal package.
4. Use `J.height = C`, `J.IsPrime`, `J ≤ Iad`, `Iad.IsPrime`, and `Ideal.height_strict_mono_of_is_prime`.

**Q1: Relabeling vs Per-Index `aeval`**

Use relabeling. It is lower friction.

Avoid the per-index `RepCoord` classifier. The `dStratum q p (Fin.castSucc 0) = q` facts may be `rfl`, but they do not flow well into `omega`, and you will pay that tax repeatedly.

Use:
- `Equiv.uniqueSigma` to remove `Σ _ : Fin 1, ...`
- `finCongr`
- `finSumFinEquiv.symm`
- `Equiv.prodCongr`
- `Equiv.sumProdDistrib`
- `Equiv.prodSumDistrib`
- `Equiv.sumAssoc`, `Equiv.sumComm`, `Equiv.sumCongr`
- `MvPolynomial.renameEquiv`
- `MvPolynomial.sumAlgEquiv`

Important orientation trap: `MvPolynomial.sumAlgEquiv R S₁ S₂` gives

```lean
MvPolynomial (S₁ ⊕ S₂) R ≃ₐ[R] MvPolynomial S₁ (MvPolynomial S₂ R)
```

so `S₁` is the outer variable block. For elimination, make the final sum `B22block ⊕ SchurVar`, not `SchurVar ⊕ B22block`, or insert `Equiv.sumComm`.

**Q2: Multivariable Graph Quotient**

Mathlib v4.29 has no canned multivariable analogue of:

```lean
Polynomial.quotientSpanXSubCAlgEquiv
```

The clean path is not Finset-iterating it manually. Prove the general kernel lemma once by finite induction:

```lean
theorem ker_aeval_eq_graphIdeal
    [CommRing R] [Finite ι] (c : ι → R) :
    RingHom.ker (MvPolynomial.aeval c : MvPolynomial ι R →ₐ[R] R).toRingHom =
      Ideal.span (Set.range fun i : ι =>
        MvPolynomial.X i - MvPolynomial.C (c i)) := ...
```

Use:
- `Finite.induction_empty_option`
- `MvPolynomial.isEmptyAlgEquiv`
- `MvPolynomial.optionEquivLeft`
- `Polynomial.ker_evalRingHom`
- `MvPolynomial.optionEquivLeft_X_none`
- `MvPolynomial.optionEquivLeft_X_some`
- `MvPolynomial.optionEquivLeft_C`

Then define:

```lean
def graphEval (forced : B22block → Sd) :
    MvPolynomial B22block Sd →ₐ[Sd] Sd :=
  MvPolynomial.aeval forced
```

Surjectivity is constants:

```lean
have hsurj : Function.Surjective (graphEval forced) :=
  fun y => ⟨MvPolynomial.C y, by simp [graphEval]⟩
```

Quotient iso:

```lean
noncomputable def graphQuotEquiv :
    MvPolynomial B22block Sd ⧸ graphIdeal forced ≃ₐ[Sd] Sd :=
  (Ideal.quotientEquivAlgOfEq Sd (ker_aeval_eq_graphIdeal forced).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hsurj)
```

Prime:

```lean
have hJprime : (graphIdeal forced).IsPrime := by
  rw [← ker_aeval_eq_graphIdeal forced]
  exact RingHom.ker_isPrime (graphEval forced)
```

This needs `IsDomain Sd`; use `IsLocalization.isDomain_of_le_nonZeroDivisors` plus
`powers_le_nonZeroDivisors_of_noZeroDivisors` and `detΔS ≠ 0`.

**Q3: Krull Bound**

The exact Mathlib lemmas are:

```lean
Ideal.height_le_spanRank_toENat
Ideal.height_le_spanFinrank
Ideal.height_le_spanRank
Ideal.height_le_card_of_mem_minimalPrimes_span_finset
Ideal.minimalPrimes_eq_subsingleton_self
```

Hypotheses: `[CommRing R] [IsNoetherianRing R]`, and for the direct `height_le_span...` lemmas, `I ≠ ⊤`.

For your localized polynomial ring, noetherianity comes from:
- polynomial noetherian instances,
- `IsLocalization.isNoetherianRing`.

But again: this only proves `J.height ≤ C`.

**Equality Path**

Prove or package:

```lean
(graphIdeal forced).height = (Nat.card B22block : ℕ∞)
```

Then transport it back through the relabel/localization equivalence to your `J`, rewrite
`Nat.card B22block = (p-r)*(q-r)`, and use:

```lean
Ideal.height_strict_mono_of_is_prime
Ideal.height_mono
Ideal.finiteHeight_of_isNoetherianRing
```

The final pattern is:

```lean
by
  apply le_antisymm hJI
  by_contra hnot
  have hlt : J < Iad := lt_of_le_of_ne hJI hnot
  have hstrict := Ideal.height_strict_mono_of_is_prime hlt
  rw [hJheight, hIadheight] at hstrict
  exact (lt_irrefl _ hstrict)
```

**Regular/Dim `δ`**

After `Iad = J`, use the quotient iso to identify:

```lean
A_loc ⧸ Iad ≃ₐ[k] Sd
```

For smoothness/regularity use:
- `Algebra.Smooth.of_isLocalization_Away`
- `Algebra.Smooth.comp`
- repo instance `smooth_mvPolynomial`
- `Algebra.Smooth.of_equiv`
- `smooth_point_isRegularLocalRing`
- `IsRegularLocalRing.of_ringEquiv`

Mathlib has `IsRegularLocalRing`, not a robust global `IsRegularRing` API. Lowest friction: expose the theorem locally, e.g. for every maximal ideal `m` of `A_loc ⧸ Iad`, `Localization.AtPrime m` is regular and has dimension `δ`. For local dimension, use localization height tools:
- `IsLocalization.AtPrime.ringKrullDim_eq_height`
- `IsLocalization.height_map_of_disjoint`
- `IsLocalization.isMaximal_iff_isMaximal_disjoint`
- `MvPolynomial.ringKrullDim_of_isNoetherianRing` after reindexing `SchurVar ≃ Fin δ`.