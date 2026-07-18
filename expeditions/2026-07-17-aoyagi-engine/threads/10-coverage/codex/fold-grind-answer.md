## A

### Proof architecture

A `mutual theorem` block with equation-style clauses is the standard and cleanest v4.29 idiom here:

```lean
mutual
theorem imgAcc (acc : Params M → Params M) :
    ∀ t : ResolutionTree M, ... 
  | .leaf l => by ...
  | .branch n edges => by
      simpa only [ResolutionTree.leafPaths, leafPathImages]
        using imgEdgesAcc acc edges

theorem imgEdgesAcc (acc : Params M → Params M) :
    ∀ edges : List (Edge M), ...
  | [] => by ...
  | .mk _ s c :: es => by ...
end
```

This mirrors the already-accepted mutual definitions, so Lean’s structural termination checker sees the child/tree and tail/list decreases. A manual recursor is worse: the generated mutual recursor concerns `ResolutionTree`/`Edge`, while the companion recursion is over `List (Edge M)`. A single non-mutual proof merely hides the same two inductions.

Use the identical pattern for

```lean
(leafPaths acc t).map Prod.fst = leaves t
```

and its edge-list companion. Its cons case is only `List.map_append` plus the two IHs.

### Exact set lemmas

There is no dedicated List-biUnion append theorem. The robust append identity is:

```lean
by
  simp only [List.mem_append, Set.iUnion_or, Set.iUnion_union_distrib]
```

For List cons and singleton:

```lean
-- ⋃ p ∈ a :: A, F p
simp only [List.mem_cons, Set.iUnion_iUnion_eq_or_left]

-- ⋃ p ∈ [a], F p
simp only [List.mem_singleton, Set.iUnion_iUnion_eq_left]
```

`Set.biUnion_insert` and `Set.biUnion_singleton` exist, but concern genuine `Set` indices, not Lists.

The relevant image signatures are:

```lean
Set.image_comp (f : β → γ) (g : α → β) (s : Set α) :
  (f ∘ g) '' s = f '' (g '' s)

Set.image_image (g : β → γ) (f : α → β) (s : Set α) :
  g '' (f '' s) = (fun x => g (f x)) '' s

Set.image_union (f : α → β) (s t : Set α) :
  f '' (s ∪ t) = f '' s ∪ f '' t

Set.image_id (s : Set α) :
  id '' s = s
```

Thus Lemma A closes in the required orientation with:

```lean
simpa only [Set.image_id] using
  (imgAcc (M := M) (id : Params M → Params M) t).symm
```

### Recommended cons case

Avoid asking `rw` to infer the higher-order arguments of `Set.image_comp`. Pin the application first:

```lean
| .mk _ s c :: es => by
    simp only [ResolutionTree.edgesLeafPaths, edgesImages,
      List.mem_append, Set.iUnion_or, Set.iUnion_union_distrib]
    rw [imgAcc (acc ∘ s.localSub) c, imgEdgesAcc acc es]
    have hcomp :
        (acc ∘ s.localSub) '' leafPathImages c =
          acc '' (s.localSub '' leafPathImages c) :=
      Set.image_comp acc s.localSub (leafPathImages c)
    rw [hcomp, Set.image_union]
```

This is preferable to `simp only [Set.image_comp]`: that still invokes higher-order matching. `Set.image_image` points in the reverse direction and produces a lambda rather than a syntactic composition, so it is not the better escape hatch.

## B

### Work in split flat coordinates

Conjugation is the correct eventual definition, but the cover proof should happen entirely in flat, center–spectator product coordinates and be transported once.

For `S : Fin d ↪ Fin N`, construct a homeomorphism

```lean
split : (Fin N → ℝ) ≃ₜ
  (Fin d → ℝ) × ({k : Fin N // k ∉ Set.range S} → ℝ)
```

from:

- `Equiv.ofInjective S S.injective`,
- `Homeomorph.piEquivPiSubtypeProd`,
- `Homeomorph.piCongrLeft`,
- `Homeomorph.prodCongr`.

Then combine it with flattening:

```lean
q := (paramsEquivFlatCLE M).toHomeomorph.trans split
```

In product coordinates define

```lean
P i := Prod.map (pivotChart i) id
D i := pivotChartDom i R ×ˢ Set.univ
```

and only then define the `Params M` data:

```lean
Φ i := q.symm ∘ P i ∘ q
Dₚ i := q ⁻¹' D i
```

This is the same conjugation strategy as `e.symm ∘ flat ∘ e`, but `q` absorbs both flattening and coordinate splitting.

### Slab equality

The product-coordinate calculation is short:

```lean
⋃ i, P i '' D i
  = ⋃ i, (pivotChart i '' pivotChartDom i R) ×ˢ Set.univ
  = (⋃ i, pivotChart i '' pivotChartDom i R) ×ˢ Set.univ
  = cubeBox d R ×ˢ Set.univ
```

The exact facts are:

- `Set.prodMap_image_prod`,
- `Set.image_id`,
- `Set.iUnion_prod_const` used backwards,
- `iUnion_pivotChart_image_eq_cubeBox`.

This is substantially cleaner than using `Function.update` to reconstruct spectator coordinates.

Transport gives:

```lean
⋃ i, Φ i '' Dₚ i
  = q.symm '' (cubeBox d R ×ˢ Set.univ)
  = q ⁻¹' (cubeBox d R ×ˢ Set.univ)
```

Use per-chart `Set.image_comp` plus `q.image_preimage`, then `Set.image_iUnion`, and finally `q.toEquiv.image_symm_eq_preimage`.

For openness, put

```lean
O := Set.univ.pi (fun _ : Fin d => Set.Ioo (-R) R)
U := q ⁻¹' (O ×ˢ Set.univ)
```

Then:

- `isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)`,
- `q.isOpen_preimage.mpr`,
- `Set.pi_mono (fun _ _ => Set.Ioo_subset_Icc_self)`,
- `Set.prod_mono`,
- `Set.preimage_mono`

give openness and `U ⊆` the closed slab cover. To contain the center, you need `0 < R`, not merely the atom’s `0 ≤ R`.

### Transport API

The clean v4.29 facts are:

```lean
Equiv.image_eq_preimage_symm
Equiv.image_symm_eq_preimage

Homeomorph.isOpen_image
Homeomorph.isOpen_preimage

ContinuousLinearEquiv.image_eq_preimage_symm
ContinuousLinearEquiv.image_symm_eq_preimage
ContinuousLinearEquiv.toHomeomorph
```

For subset chains, ordinary `Set.preimage_mono` is usually simpler than equivalence-specific subset lemmas.

### Main risk

The current placeholder

```lean
(pivotComplete : True)
```

makes `node_pivotCover_of_atom` false: take `edges = []` and nonempty `V`. No coordinate proof can repair that.

The cheapest de-risking is:

1. Prove a standalone generic `embeddedPivotCover` using `q`, independent of trees.
2. Replace `True` by a contract supplying:
   - `0 < d`, `0 < R`,
   - `V ⊆` the chosen open slab,
   - realization of the full `Fin d` chart family inside  
     `⋃ e ∈ edges, e.subst.localSub '' childRegion e`.

That separates the elementary geometric atom from the genuinely construction-specific edge-completeness obligation.