Use `Submodule.baseChange_span`, not `LinearMap.lTensor_range`, for the left side. In this context the range of the restricted `lTensor` is definitionally `K.baseChange k`.

Paste this over the `sorry`:

```lean
by
  let R := MvPolynomial σ k
  let B := MvPolynomial σ k ⧸ Ideal.span (Set.range g)
  let M := B ⊗[R] Ω[R⁄k]
  let K := LinearMap.ker (KaehlerDifferential.mapBaseChange k R B)
  let Iker : Ideal R := RingHom.ker (algebraMap R B)

  let sgen : Fin m → M :=
    fun i => (1 : B) ⊗ₜ[R] KaehlerDifferential.D k R (g i)
  let S : Set M := Set.range sgen
  let tgen : Fin m → k ⊗[B] M :=
    fun i => (1 : k) ⊗ₜ[B] sgen i
  let T : Set (k ⊗[B] M) := Set.range tgen
  let ugen : Fin m → (σ → k) :=
    fun i => jacobianTranspose g a (Pi.single i 1)
  let U : Set (σ → k) := Set.range ugen

  change (LinearMap.range ((LinearMap.lTensor k K.subtype).restrictScalars k)).map
      Ψ.toLinearMap = LinearMap.range (jacobianTranspose g a)

  have hsurjRB : Function.Surjective (algebraMap R B) := hsurj

  have hIker : Iker = Ideal.span (Set.range g) := by
    dsimp [Iker, B, R]
    rw [Ideal.mk_ker]

  have hgi_mem : ∀ i : Fin m, g i ∈ Iker := by
    intro i
    rw [hIker]
    exact Ideal.subset_span ⟨i, rfl⟩

  have hgenI :
      Submodule.span R
        (Set.range fun i : Fin m => (⟨g i, hgi_mem i⟩ : Iker)) = ⊤ := by
    rw [(Submodule.span_range_subtype_eq_top_iff Iker hgi_mem)]
    exact hIker.symm

  have hcotTop :
      Submodule.span R
        (Set.range fun i : Fin m =>
          Iker.toCotangent (⟨g i, hgi_mem i⟩ : Iker)) = ⊤ := by
    rw [← Iker.toCotangent_range]
    symm
    rw [← Submodule.map_top Iker.toCotangent, ← hgenI, Submodule.map_span]
    rw [← Set.range_comp Iker.toCotangent
      (fun i : Fin m => (⟨g i, hgi_mem i⟩ : Iker))]
    rfl

  have hconormalSpan :
      LinearMap.range (KaehlerDifferential.kerCotangentToTensor k R B) =
        Submodule.span R S := by
    rw [← Submodule.map_top (KaehlerDifferential.kerCotangentToTensor k R B),
      ← hcotTop, Submodule.map_span]
    dsimp [S, sgen]
    rw [← Set.range_comp (KaehlerDifferential.kerCotangentToTensor k R B)
      (fun i : Fin m => Iker.toCotangent (⟨g i, hgi_mem i⟩ : Iker))]
    congr 1

  have hK_R : K.restrictScalars R = Submodule.span R S := by
    exact
      (KaehlerDifferential.range_kerCotangentToTensor k R B hsurjRB).symm.trans
        hconormalSpan

  have hKspanB : K = Submodule.span B S := by
    apply Submodule.restrictScalars_injective R B M
    rw [hK_R, Submodule.restrictScalars_span R B hsurjRB]

  have hLeftRange :
      LinearMap.range ((LinearMap.lTensor k K.subtype).restrictScalars k) =
        Submodule.span k T := by
    change K.baseChange k = _
    rw [hKspanB]
    dsimp [T, S, tgen, sgen]
    rw [Submodule.baseChange_span]
    rw [← Set.range_comp ((TensorProduct.mk B k M) (1 : k)) sgen]
    rfl

  have hRhsSpan :
      LinearMap.range (jacobianTranspose g a) = Submodule.span k U := by
    have hdom :
        Submodule.span k
          (Set.range fun i : Fin m => (Pi.single i (1 : k) : Fin m → k)) = ⊤ := by
      rw [← (Pi.basisFun k (Fin m)).span_eq]
      congr 1
      ext v
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, by rw [Pi.basisFun_apply]⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i, by rw [Pi.basisFun_apply]⟩
    rw [← Submodule.map_top (jacobianTranspose g a), ← hdom, Submodule.map_span]
    dsimp [U, ugen]
    rw [← Set.range_comp (jacobianTranspose g a)
      (fun i : Fin m => (Pi.single i (1 : k) : Fin m → k))]
    rfl

  have hPsi_i : ∀ i : Fin m, Ψ.toLinearMap (tgen i) = ugen i := by
    intro i
    change Ψ (tgen i) = ugen i
    dsimp [tgen, sgen, ugen]
    ext x
    rw [Ψ_D (g i)]
    rw [jacobianTranspose_apply]
    simp [Pi.single_apply, aug_mk, Ideal.Quotient.algebraMap_eq]

  calc
    (LinearMap.range ((LinearMap.lTensor k K.subtype).restrictScalars k)).map Ψ.toLinearMap
        = (Submodule.span k T).map Ψ.toLinearMap := by
          exact congrArg
            (fun p : Submodule k (k ⊗[B] M) => p.map Ψ.toLinearMap)
            hLeftRange
    _ = Submodule.span k U := by
      apply le_antisymm
      · exact
          (Submodule.map_span_le Ψ.toLinearMap T (Submodule.span k U)).2
            (by
              intro y hy
              rcases hy with ⟨i, rfl⟩
              rw [hPsi_i i]
              exact Submodule.subset_span ⟨i, rfl⟩)
      · rw [Submodule.span_le]
        intro y hy
        rcases hy with ⟨i, rfl⟩
        rw [← hPsi_i i]
        exact Submodule.mem_map_of_mem (f := Ψ.toLinearMap)
          (Submodule.subset_span ⟨i, rfl⟩ :
            tgen i ∈ Submodule.span k T)
    _ = LinearMap.range (jacobianTranspose g a) := hRhsSpan.symm
```

The key lemmas are exactly:
`KaehlerDifferential.range_kerCotangentToTensor`,
`Ideal.mk_ker`,
`Submodule.span_range_subtype_eq_top_iff`,
`Submodule.restrictScalars_span`,
`Submodule.baseChange_span`,
`Submodule.map_span_le`,
and `Pi.basisFun_apply`.