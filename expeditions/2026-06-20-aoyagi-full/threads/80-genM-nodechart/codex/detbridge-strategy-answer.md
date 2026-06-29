**1. RANKED PLAN**

1. **Route B, but only in a derivative-identified form.** This is the better route for the determinant headline. Do not try to prove a global value equality `pack_M ∘ T_M = chartParamsGen`. Instead, prove a `HasFDerivAt`/`fderiv` identification for the actual target chart and then compute that linear map by `lowerTri_det`, `lowerTri3_det`, or an iterated version.

   What must be built:
   - a derivative candidate `Dφ_engine u` for the actual flat chart;
   - a proof
     ```lean
     HasFDerivAt phiGenFlat (Dφ_engine u) u
     ```
     or an equivalent `fderiv` equality;
   - product/role linear equivalences splitting the fixed flat space into radial + per-boundary Schur/LDU/lift pieces;
   - a lower-triangular staircase description whose diagonal blocks are radial, `schurFrameDeriv`, `lduCoreDeriv`, identity/spectator, and `chainUnitMap`;
   - determinant assembly by `LinearMap.det_comp`, local `lowerTri_det`, `lowerTri3_det`, `listProd_*` where the factors are genuine fixed-space endomorphisms.

   Casts bite at the block-read boundary: matching `Agen`/`Cgen` entries to the Schur/LDU variables through `Text`, `Wext`, `chainA`, `chainQ`, `finCongr`, and `paramsEquivFlat`. The biggest risk is accidentally proving the determinant of an engine surrogate rather than `fderiv` of the real `phiGen`.

2. **Route A, explicit `shear_M` plus `pack_M ∘ T_M = chartParamsGen`.** This is sound and conceptually clean, but more expensive.

   What must be built:
   - `pb_M`, `shear_M`, `bsubst_M`, `T_M`;
   - `shear_M` derivative and `fderiv_det_one_of_shear`;
   - `pack_M`/`QMcle` outer reshape with det `1`;
   - the full value-level bridge, proved by `funext s; ext i j`, unfolding `chartParamsGen → Agen → chainA`.

   Casts bite everywhere: `Fin.cast h (Fin.castAdd c i)`, `Fin.cast h (Fin.natAdd t a)`, `finSplit`, `Wext_apply`, `Text_succ`, `Matrix.reindex_apply`, `flatEquivOf_symm_coord`. The biggest risk is the opaque-width map equality itself: it is not a determinant theorem, it is a large coordinate theorem.

**2. THE CHEAPEST SOUND DECOMPOSITION**

You can avoid the explicit value-level bridge `pack_M ∘ T_M = chartParamsGen`, but you cannot avoid all target-identification. The cheapest sound version is:

```lean
-- schematic
def DphiEngine ... : (Fin (routeMAmbient M) → ℝ) →L[ℝ] (Fin (routeMAmbient M) → ℝ) := ...

theorem phiGen_hasFDerivAt_engine ... :
    HasFDerivAt phiGenFlat (DphiEngine ...) x := ...
```

Then prove that `DphiEngine`, after determinant-1 reshapes, is an iterated lower-triangular map with engine diagonal blocks. This replaces a nonlinear map equality by a first-order derivative equality.

The `Frame3333Deriv` route does not generalize as-is. It works because `Fin 27`, `frameB`, and the block reindex equivalences are hand-built at literal sizes, so `fin_cases`, `decide`, and `Matrix.det_fin_three` can close the block determinants. For general `M`, the chart-input grading and flat-output layer grading have different per-layer cardinalities; a single `Matrix.BlockTriangular` grading on `Fin N` is the wrong object. Generalizing `frameB` would amount to generating an aligned frame and proving the derivative bridge anyway.

**3. THE FIRST BANKABLE INCREMENT**

Bank the inverse form of `finSplit` once. This removes the repeated local `hidx` proofs currently appearing before every `chainA_apply_*`/`chainQ_apply_*` rewrite.

```lean
theorem finSplit_symm_apply
    {M' t c : ℕ} (h : t + c = M') (hle : t ≤ M')
    (x : Fin t ⊕ Fin (M' - t)) :
    (finSplit (M := M') (t := t) hle).symm x =
      Sum.elim
        (fun i : Fin t =>
          Fin.cast h (Fin.castAdd c i))
        (fun a : Fin (M' - t) =>
          Fin.cast h (Fin.natAdd t
            (Fin.cast (show M' - t = c by omega) a))) x
```

Then derive two `[simp]` corollaries for `Sum.inl` and `Sum.inr`. This is network-free, opaque-width, and directly reusable in `chainA`, `chainQ`, differentiability, and any derivative-block bridge.

**4. CAST-ZONE TACTICS**

Use `finSplit` as the only row/column split. Normalize indices to the exact `castAdd`/`natAdd` forms first, then rewrite with banked laws:

```lean
rw [show r = Fin.cast h (Fin.castAdd c i) from by
  apply Fin.ext
  simp]
rw [chainA_apply_castAdd]
```

For residual rows/columns, prefer the same shape every time:

```lean
rw [show r = Fin.cast h (Fin.natAdd t a) from by
  apply Fin.ext
  simp]
rw [chainA_apply_natAdd]
```

Use focused simp sets:
```lean
simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
  Equiv.refl_apply, Equiv.refl_symm, Equiv.symm_symm,
  finCongr_apply, finCongr_symm]
```

For products under reindex, use `Matrix.submatrix_mul_equiv` with the middle equivalence explicit. Do not expand the finite sum unless forced.

For determinants under coordinate reshapes, use existing `QMcle_abs_det` / `Matrix.det_submatrix_equiv_self`; avoid inventing a sign/permutation determinant route.

For opaque widths, avoid relying on `fin_cases` plus broad `simp`. In explicit anchors, prove entries at literal indices `⟨_, by decide⟩` as separate `have`s, then `exact` them into the dependent goal. For general `M`, split by `finSplit`, not by enumerating `Fin`.

At v4.29 in this repo, determinant of CLMs is read as:
```lean
LinearMap.det f.toLinearMap
```
not a separate `ContinuousLinearMap.det`.