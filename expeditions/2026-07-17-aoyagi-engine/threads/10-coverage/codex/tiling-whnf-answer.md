1. The likely blowup is higher-order inference of the implicit biUnion family `s` in `Set.subset_iUnion₂`, not the index set or the final `rfl`. Lean must reconstruct `s`, reduce `s chosen hmem`, and compare the resulting `.subst.localSub`/`.child` expression, exposing the heavy definitions. The inline `List.mem_map.mpr ... rfl` aggravates expected-type inference but is not intrinsically expensive.

2. Pin the mapped function and the complete biUnion body, then use `Set.subset_iUnion₂_of_subset`:

```lean
      have hp : i - offset <
          dCenterOfEdge n (Edge.mk c s ch) := by omega
      have hi' : offset + (i - offset) = i := by omega

      let p : Fin (dCenterOfEdge n (Edge.mk c s ch)) :=
        ⟨i - offset, hp⟩
      let fan : Fin (dCenterOfEdge n (Edge.mk c s ch)) → Edge M := fun p =>
        Edge.mk c
          { s with
            localSub :=
              geoChartMap (dCenterOfNode M) (qNodeOf M)
                ⟨n, Edge.mk c s ch, offset + (p : ℕ)⟩ }
          (tGeo
            (acc ∘ geoChartMap (dCenterOfNode M) (qNodeOf M)
              ⟨n, Edge.mk c s ch, offset + (p : ℕ)⟩)
            ch)

      change _ ⊆
        ⋃ e ∈
          (List.finRange
            (dCenterOfEdge n (Edge.mk c s ch))).map fan,
          e.subst.localSub '' leafPathImages e.child

      have hp_mem :
          p ∈ List.finRange (dCenterOfEdge n (Edge.mk c s ch)) :=
        List.mem_finRange p
      have he_mem :
          fan p ∈
            (List.finRange
              (dCenterOfEdge n (Edge.mk c s ch))).map fan :=
        List.mem_map_of_mem hp_mem

      refine Set.subset_iUnion₂_of_subset
        (t := fun (e : Edge M)
          (_ : e ∈
            (List.finRange
              (dCenterOfEdge n (Edge.mk c s ch))).map fan) =>
          e.subst.localSub '' leafPathImages e.child)
        (fan p) he_mem ?_

      simp only [fan, p, Edge.subst, Edge.child, Fin.val_mk, hi',
        geoChartMap_on_cone n (Edge.mk c s ch) i hd hi]
      exact Set.image_mono
        (hcov (Edge.mk c s ch) (List.mem_cons_self ..)
          (acc ∘ geoChartMap (dCenterOfNode M) (qNodeOf M)
            ⟨n, Edge.mk c s ch, i⟩))
```

Important v4.29 detail: `List.mem_map_of_mem` takes only the membership proof; its map function is implicit. Passing `fan` explicitly causes the reported type mismatch.

Verified names: `List.mem_finRange`, `List.mem_map_of_mem`, `Set.subset_iUnion₂_of_subset`, `Set.subset_biUnion_of_mem`, and `Set.mem_biUnion`. The block itself is inferred from the local source, not compile-tested here.

3. Seal the outer abstraction boundary: primarily `geoChartMap`, `tGeo`, and `qNodeOf`. Sealing only `qOfCenter`/`centerPerm` stops the deepest explosion after Lean has already unfolded the outer machinery; keeping them locally irreducible too is harmless but usually redundant.

`with_reducible` can guard the displayed `refine` after the explicit `change`, but it does not replace pinning `t`. Pointwise `Set.mem_biUnion (t := ...)` is equally sound. Moving to `Finset` will not address the higher-order body inference and may introduce `DecidableEq (Edge M)` overhead.