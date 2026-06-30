**Best Route**

Rank:

1. **B, but structurally**: prove `∃ σ : Fin (flatDim M) ≃ Fin (flatDim M), composite = funCongrLeft σ`, without naming the final σ. Use a reusable “this LinearEquiv is just coordinates” predicate and closure under `trans`, `symm`, `prodCongr`, etc. Then feed `hreg_of_measurePreserving_comp`.
2. **D**: relative determinant via chosen bases. Viable, but you will build more custom determinant API.
3. **A**: explicit final σ. Works, but it is exactly the nested `Sigma/Sum/Fin` chase you want to avoid.
4. **C**: not available as stated. `det` is endomorphism-only; relative-det machinery is custom.
5. Naive “each constituent is MP”: **BLOCKED** unless you add/transport `MeasureSpace`/`volume` on the intermediate `StairProd`/`SchurInc`/product spaces.

Single best: **B with a structural coordinate-permutation predicate**.

**Confirmed Lemmas**

`CONFIRMED` from this repo’s v4.29-pinned source:

- `hreg_of_measurePreserving_comp`: project-local, exactly your banked bridge. See [RouteMTwoSidedReg.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-acc0e33b44d30d961/lean/DLNFibre/DLN/RLCT/Validate/RouteMTwoSidedReg.lean:42).
- `continuousLinearMap_abs_det_eq_one_of_measurePreserving`: project-local MP-to-abs-det bridge. See [ParamsReshapeMP.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-acc0e33b44d30d961/lean/DLNFibre/DLN/RLCT/Foundations/ParamsReshapeMP.lean:98).
- `volume_preserving_arrowCongr'`, `MeasurableEquiv.arrowCongr'`, `MeasurableEquiv.refl`, `MeasurePreserving.id`: Mathlib, used in existing v4.29 code. See [ParamsFlat.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-acc0e33b44d30d961/lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat.lean:100).
- `measurePreserving_piCurry`: **project-local**, not Mathlib; this repo explicitly calls it “the one Mathlib gap.” See [ParamsFlat.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-acc0e33b44d30d961/lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat.lean:38).
- Linear constructors used by your maps are confirmed in source: `LinearEquiv.funCongrLeft`, `LinearEquiv.piCurry`, `LinearEquiv.piFinTwo`, `LinearEquiv.sumArrowLequivProdArrow`, `LinearEquiv.curry`, `Matrix.ofLinearEquiv`, `Matrix.reindexLinearEquiv`, `LinearEquiv.prodComm`, `LinearEquiv.prodCongr`, `LinearEquiv.prodUnique`.

I would **not** rely on a guessed one-shot Mathlib theorem like “basis-permuting `LinearEquiv` has abs det 1”; I have no confirmed name for that in v4.29. Confirmed lower-level determinant tools include `LinearMap.det_comp`, `LinearMap.det_conj`, `LinearEquiv.isUnit_det'`, `LinearMap.det_toMatrix'`, `Matrix.det_permute'`, but they do not give your clean theorem directly.

**Reusable Lemma**

Use this predicate:

```lean
def IsCoordLE {X Y : Type*}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    {ι κ : Type*}
    (cx : X ≃ₗ[ℝ] (ι → ℝ)) (cy : Y ≃ₗ[ℝ] (κ → ℝ))
    (e : X ≃ₗ[ℝ] Y) : Prop :=
  ∃ σ : κ ≃ ι,
    ((cy : Y →ₗ[ℝ] (κ → ℝ)) ∘ₗ (e : X →ₗ[ℝ] Y) ∘ₗ
      (cx.symm : (ι → ℝ) →ₗ[ℝ] X))
    =
    ((LinearEquiv.funCongrLeft ℝ ℝ σ :
      (ι → ℝ) ≃ₗ[ℝ] (κ → ℝ)) : (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
```

Then prove once:

```lean
theorem hreg_of_exists_funCongrLeft {N n : ℕ}
    (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)]
    [∀ k, FiniteDimensional ℝ (V k)]
    (eIn eOut : (Fin N → ℝ) ≃ₗ[ℝ] StairProd V n)
    (hσ : ∃ σ : Fin N ≃ Fin N,
      ((eOut.symm : StairProd V n →ₗ[ℝ] (Fin N → ℝ)) ∘ₗ
        (eIn : (Fin N → ℝ) →ₗ[ℝ] StairProd V n))
      =
      ((LinearEquiv.funCongrLeft ℝ ℝ σ :
        (Fin N → ℝ) ≃ₗ[ℝ] (Fin N → ℝ)) :
        (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))) :
    |LinearMap.det ((eOut.symm : StairProd V n →ₗ[ℝ] (Fin N → ℝ)) ∘ₗ
      (eIn : (Fin N → ℝ) →ₗ[ℝ] StairProd V n))| = 1
```

Proof idea: rewrite by `hσ`; prove MP of `funCongrLeft σ` using `volume_preserving_arrowCongr' σ.symm (MeasurableEquiv.refl ℝ) (MeasurePreserving.id ...)`; apply `hreg_of_measurePreserving_comp`.

**Constituent Discharge**

For the coordinate predicate:

- `funCongrLeft`: witness is the given index equiv.
- `piCurry`, `piFinTwo`, `sumArrowLequivProdArrow`, `curry`, `Matrix.ofLinearEquiv`: choose coordinate charts so these are coordinate identity.
- `Matrix.reindexLinearEquiv`: witness is the row/column product index equiv.
- `prodCongr`: combine witnesses by `Equiv.sumCongr`.
- `prodComm`: witness is sum swap.
- `prodUnique` / `PUnit`: use empty index `Fin 0`; proof by subsingleton.
- `roleReorderLE`, `eInRearrange`: witnesses are small nested sum/product reassociation permutations; proof by `Prod.ext`, not entrywise `Fin`.
- `flatBlockLE.symm` in `packLayer0` is the only nontrivial atom: witness is the row/column `finSumFinEquiv` block split; reuse existing `flatBlock` round-trip/split lemmas.

For a constituent-by-constituent MP route, gaps remain: no confirmed direct MP lemma for `Matrix.ofLinearEquiv`, `Matrix.reindexLinearEquiv`, `LinearEquiv.prodComm`, `LinearEquiv.prodUnique`, `roleReorderLE`, `eInRearrange`, or `flatBlockLE.symm`. That route also needs intermediate measure instances, so it is the wrong route here.

**Verdict**

This is **BOUNDED**, not a wall: one `IsCoordLE` API, closure lemmas, and coordinate certificates for `eIn`/`eihdOut`. Expect roughly 120-220 lines the first time, depending on how much product/matrix chart API you already have. The giant explicit final σ is avoidable. The only place that can bite is `flatBlockLE.symm`; it is bounded block-split bookkeeping, not opaque-width enumeration.