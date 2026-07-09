**Rank:** A, then C, then B.

Use **(A) complement-subtype**. It keeps the only readback-sensitive map, the core forward map, completely explicit and layer-preserved. SPEC becomes “whatever is not REG or CORE”, so you avoid the interior `Σ`, the total cardinality proof, and the impossible “default spec inhabitant” problem. The only real proof is injectivity of `regCoreEmb`, and that can be done with a partial `FlatIdx → Option (Reg ⊕ Core)` classifier, not a full `flatToRole`.

**Winner Construction**
Define:
```lean
abbrev SpecIdxGen ... :=
  {x : FlatIdx H // x ∉ Set.range (regCoreEmb H r ι hι hL)}
```

Build:
```lean
regCoreEmb :
  (RegIdxGen H r ⊕ CoreIdxGen H r) → FlatIdx H
```
with branches:

- first-layer REG `₂₁`;
- last-layer REG `₁₁, ₁₂`;
- CORE:
```lean
| Sum.inr ⟨⟨s, i⟩, j⟩ =>
  ⟨⟨s, sumSplit (ι s.castSucc) (hι s.castSucc) (Sum.inr i)⟩,
      sumSplit (ι s.succ)     (hι s.succ)     (Sum.inr j)⟩
```

Then:
```lean
roleEquivGen :
  RegIdxGen H r ⊕ (CoreIdxGen H r ⊕ SpecIdxGen ...) ≃ FlatIdx H :=
  (Equiv.sumAssoc _ _ _).symm.trans <|
    ((Equiv.sumCongr regCoreRangeEquiv (Equiv.refl _)).trans
      (Equiv.sumCompl (fun x => x ∈ Set.range (regCoreEmb H r ι hι hL))))
```

I would define `regCoreRangeEquiv` locally rather than relying on `Equiv.ofInjective` if you want predictable reduction:
```lean
toFun x := ⟨regCoreEmb ... x, ⟨x, rfl⟩⟩
```
`Equiv.ofInjective` likely exists, but I did not verify it in v4.29 here.

Key simp facts: `Equiv.trans_apply`, `Equiv.sumCongr_apply`, `Sum.map_inl`, `Sum.map_inr`, `Equiv.sumAssoc_symm_apply_inr_inl`. Local code verifies those `sumAssoc` simp lemma names. `Equiv.sumCompl` is verified locally; its left/right application reduces to subtype coercion, usually by `rfl` after unfolding, though exact generated simp lemma names should be verified if you use them directly.

Core readback is not quite global `rfl`, but should be one small simp lemma:
```lean
theorem roleEquivGen_core (c : CoreIdxGen H r) :
    roleEquivGen ... (Sum.inr (Sum.inl c))
      = regCoreEmb ... (Sum.inr c) := by
  simp [roleEquivGen, regCoreRangeEquiv]
```

Then:
```lean
theorem e_idx_gen_core (n : Fin (flatDim (fun s => H s - r))) :
    e_idx_gen ... (Sum.inr (Sum.inl n))
      =
    Fintype.equivFin (FlatIdx H)
      (regCoreEmb ... (Sum.inr ((Fintype.equivFin (CoreIdxGen H r)).symm n))) := by
  simp [e_idx_gen, roleEquivGen_core]
```

After `splitOfPartition_core`, the coordinate becomes exactly the `₂₂` coordinate by unfolding `regCoreEmb`; the remaining step is the same as L=2:
```lean
rw [paramsEquivFlat_symm_entry, splitMPGen_core, e_idx_gen_core,
    Equiv.symm_apply_apply]
simp [regCoreEmb]
```
The final flat index is the desired
```lean
⟨⟨s, sumSplit (ι s.castSucc) _ (Sum.inr i)⟩,
    sumSplit (ι s.succ) _ (Sum.inr j)⟩
```

**Hard Obligation**
Prove injectivity of `regCoreEmb` via a partial classifier:
```lean
flatToRegCore? : FlatIdx H → Option (RegIdxGen H r ⊕ CoreIdxGen H r)
```

Classifier shape:

- classify row/column by
```lean
(sumSplit (ι s.castSucc) _).symm i
(sumSplit (ι s.succ) _).symm j
```
- `inr, inr` gives `some (Sum.inr core)` for every layer;
- `inr, inl` gives first-layer REG if `s = firstLayer hL`, else `none`;
- `inl, _` gives last-layer REG if `s = lastLayer hL`, else `none`;
- everything else is `none`.

Then prove:
```lean
theorem flatToRegCore?_regCoreEmb :
    flatToRegCore? ... (regCoreEmb ... x) = some x := by
  rcases x with (ρ | c)
  · rcases ρ with ⟨a,k⟩ | ⟨k, cc⟩
    · simp [regCoreEmb, flatToRegCore?, Equiv.symm_apply_apply]
    · cases cc <;> simp [regCoreEmb, flatToRegCore?, Equiv.symm_apply_apply]
  · rcases c with ⟨⟨s,i⟩,j⟩
    simp [regCoreEmb, flatToRegCore?, Equiv.symm_apply_apply]
```
Finally:
```lean
intro x y h
have hx := flatToRegCore?_regCoreEmb ... x
have hy := flatToRegCore?_regCoreEmb ... y
simpa [h, hy] using hx
```

**First/Last Indexing**
Use the existing local idiom:
```lean
def firstLayer (hL : 1 ≤ L) : Fin L := ⟨0, by omega⟩
def lastLayer  (hL : 1 ≤ L) : Fin L := ⟨L - 1, by omega⟩

theorem firstLayer_castSucc :
    (firstLayer hL).castSucc = (0 : Fin (L + 1)) := by
  apply Fin.ext
  simp [firstLayer, Fin.castSucc]

theorem lastLayer_succ :
    (lastLayer hL).succ = Fin.last L := by
  apply Fin.ext
  simp [lastLayer, Fin.succ, Fin.last]
  omega
```

Carry `hL : 1 ≤ L` at minimum. If you need the displayed first/interior/last table literally with distinct endpoints, carry `hL2 : 2 ≤ L`. For the `H (lastLayer hL).succ` versus `H (Fin.last L)` gap, make one helper:
```lean
theorem H_lastLayer_succ :
    H ((lastLayer hL).succ) = H (Fin.last L) := by
  congr 1
  exact lastLayer_succ hL
```
Then use `finCongr (by rw [H_lastLayer_succ H hL])` for the `Fin (H _ - r)` casts. Do not scatter raw `▸` casts through the role map.

**Traps**
- Put `classical` around `SpecIdxGen`/`specDimGen`/`sumCompl`; the complement subtype needs decidability for `Fintype`.
- Use exactly the same predicate in `SpecIdxGen` and `Equiv.sumCompl`; otherwise the complement subtype will not be defeq.
- Avoid Sigma equality in the injectivity proof; the `Option` classifier dodges `HEq` pain.
- `Fintype.equivFin` order is arbitrary. Always read core through `Equiv.symm_apply_apply`, not by numeric `Fin` expectations.
- Do not unfold `sumSplit`; use `Equiv.symm_apply_apply`.
- `L = 0` cannot support this partition. Handle or exclude it explicitly.