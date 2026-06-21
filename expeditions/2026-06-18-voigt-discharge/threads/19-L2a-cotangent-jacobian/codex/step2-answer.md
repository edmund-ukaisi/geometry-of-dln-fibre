**1. ROUTE**

Use the **explicit quotient equivalence** route. It is shorter/safer than finrank subtraction in Lean: no `Module.Finite` instances for the middle term, no `Nat` subtraction bookkeeping.

Lemma sequence:

```lean
hE  := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k R A hsurjRtoA
hS  := KaehlerDifferential.mapBaseChange_surjective k R A hsurjRtoA
hEt := lTensor_exact k hE hS
hSt := LinearMap.lTensor_surjective k hS
```

Then view the tensor maps as `k`-linear and use:

```lean
eExact :=
  (hEt_k : Function.Exact α β).linearEquivOfSurjective hSt_k
-- eExact : (Mid ⧸ LinearMap.range α) ≃ₗ[k] k ⊗[A] Ω[A⁄k]
```

After proving the range transport

```lean
hRange : (LinearMap.range α).map Ψ.toLinearMap =
  LinearMap.range (jacobianTranspose g a)
```

finish by:

```lean
let eQuot :=
  Submodule.Quotient.equiv
    (LinearMap.range α)
    (LinearMap.range (jacobianTranspose g a))
    Ψ hRange

exact (eExact.symm.trans eQuot).finrank_eq
```

Here `Ψ : Mid ≃ₗ[k] (σ → k)` is the cancel-base-change plus coordinate equivalence.

**2. THE RANGE/GENERATOR STEP**

Use this coordinate equivalence:

```lean
let bΩ := KaehlerDifferential.mvPolynomialBasis k σ

let coord : k ⊗[R] Ω[R⁄k] ≃ₗ[k] (σ → k) :=
  (bΩ.baseChange k).equivFun
```

This uses `Module.Basis.baseChange`, `Module.Basis.baseChange_repr_tmul`, `Basis.equivFun`, and internally `Finsupp.linearEquivFunOnFinite`.

For the middle term:

```lean
let Ψ : k ⊗[A] (A ⊗[R] Ω[R⁄k]) ≃ₗ[k] (σ → k) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange R A k k Ω[R⁄k]).trans coord
```

Generator skeleton:

```lean
let s : Fin m → I'.Cotangent :=
  fun i => I'.toCotangent ⟨g i, by simpa [I', hI'] using Ideal.subset_span ⟨i, rfl⟩⟩

have hsrc :
    Submodule.span k (Set.range fun i : Fin m => (1 : k) ⊗ₜ[A] s i) = ⊤ := by
  -- from `I = Ideal.span (Set.range g)` and `Ideal.toCotangent_surjective`
  -- use `Submodule.map_span` after rewriting the span of the `g i` in `I`.

have hgen (i : Fin m) :
    Ψ (α ((1 : k) ⊗ₜ[A] s i)) =
      jacobianTranspose g a (Pi.single i 1) := by
  ext x
  simp [
    α, Ψ, s, jacobianTranspose,
    KaehlerDifferential.kerCotangentToTensor_toCotangent,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    Module.Basis.baseChange_repr_tmul,
    Basis.equivFun_apply,
    KaehlerDifferential.mvPolynomialBasis_repr_apply,
    Pi.single_apply,
    Finset.sum_eq_single
  ]
```

Then:

```lean
have hBC :
    (LinearMap.range α).map Ψ.toLinearMap =
      Submodule.span k
        (Set.range fun i : Fin m => Ψ (α ((1 : k) ⊗ₜ[A] s i))) := by
  rw [LinearMap.range_eq_map, ← hsrc, Submodule.map_map, Submodule.map_span]
  simp [Set.image_image, Function.comp_def]

have hJ :
    LinearMap.range (jacobianTranspose g a) =
      Submodule.span k
        (Set.range fun i : Fin m =>
          jacobianTranspose g a (Pi.single i 1)) := by
  rw [LinearMap.range_eq_map]
  rw [show (⊤ : Submodule k (Fin m → k)) =
      Submodule.span k (Set.range fun i : Fin m => Pi.single i (1 : k)) by
        simpa [Pi.basisFun_apply] using (Pi.basisFun k (Fin m)).span_eq.symm]
  rw [Submodule.map_span]
  simp [Set.image_range]

exact hBC.trans <| by
  simpa [hgen] using hJ.symm
```

**3. PITFALLS**

1. **Scalar restriction.** `lTensor.equiv`/`lTensor_exact` may be over `A`, while the final finrank is over `k`. Prefer defining `α β` as `k`-linear maps via `.restrictScalars k`; use `LinearMap.range_restrictScalars`, `LinearMap.ker_restrictScalars`, and `Submodule.Quotient.restrictScalarsEquiv` if needed.

2. **`I' = I`.** Prove once and rewrite early:

```lean
have hI' : RingHom.ker (algebraMap R A) = I := by
  simpa using (Ideal.mk_ker (I := I))
```

or by `ext p; simp [Ideal.Quotient.eq_zero_iff_mem]`.

3. **Avoid finite-instance pain.** This is the main reason not to use finrank subtraction. If you do use it, create middle finiteness from `Ψ.symm` using `Module.Finite.of_surjective`; otherwise `LinearEquiv.finrank_eq` needs no such setup.