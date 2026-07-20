<task>
Lean 4 (Mathlib, toolchain v4.29). I am proving a "tiling" subset lemma but hit repeated
`(deterministic) timeout at whnf` / `isDefEq` (200000 heartbeats) at ONE tactic step, caused by
heavy noncomputable defs in the term being unified. I need the IDIOM to close this subset without
the timeout. The math is trivial; the fight is purely elaboration/unification over heavy terms.

CONTEXT. Types: `Edge M` is `inductive Edge | mk (case : StepCase) (subst : ChartSubst M) (child : ResolutionTree M)`,
with accessors `Edge.subst`, `Edge.child`. `leafPathImages : ResolutionTree M → Set (Params M)`.
Heavy defs (their whnf explodes: `geoChartMap` unfolds into `qNodeOf`→`qOfCenter`→`centerPerm`→
`Equiv.ofInjective`/`Equiv.sumCompl`; `tGeo` is a mutual noncomputable recursion):
  `geoChartMap (dCenterOfNode M) (qNodeOf M) ⟨n, e, k⟩ : Params M → Params M`
  `tGeo (acc) (t) : ResolutionTree M`

The GOAL at the stuck step (after `rw [fannedEdges]; simp only [List.mem_append, Set.iUnion_or,
Set.iUnion_union_distrib]; rw [if_neg hne]; refine Set.subset_union_of_subset_left ?_ _`):

    (fun w => (qNodeOf M n hd).symm (Prod.map (pivotChart ⟨i, hi⟩) id (qNodeOf M n hd w)))
        '' (⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) 1)
      ⊆ ⋃ e ∈ (List.finRange (dCenterOfEdge n (Edge.mk c s ch))).map
              (fun p => Edge.mk c
                 { s with localSub := geoChartMap (dCenterOfNode M) (qNodeOf M)
                            ⟨n, Edge.mk c s ch, offset + (p:ℕ)⟩ }
                 (tGeo (acc ∘ geoChartMap (dCenterOfNode M) (qNodeOf M)
                            ⟨n, Edge.mk c s ch, offset + (p:ℕ)⟩) ch)),
          e.subst.localSub '' leafPathImages e.child

In scope: `hp : i - offset < dCenterOfEdge n (Edge.mk c s ch)`, `hi' : offset + (i - offset) = i`,
`hd : dCenterOfNode M n ≤ flatDim M`, `hi : i < dCenterOfNode M n`,
`hcov : ∀ e ∈ (Edge.mk c s ch :: es), ∀ a, (⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) 1) ⊆ leafPathImages (tGeo a e.child)`.
A rewrite lemma `geoChartMap_on_cone n (Edge.mk c s ch) i hd hi :
  geoChartMap (dCenterOfNode M) (qNodeOf M) ⟨n, Edge.mk c s ch, i⟩
    = fun w => (qNodeOf M n hd).symm (Prod.map (pivotChart ⟨i,hi⟩) id (qNodeOf M n hd w))`
is available (syntactic rw; cheap).

MATH: the pivot `p := ⟨i - offset, hp⟩` gives the fanned edge whose `.subst.localSub` (after `hi'` +
`geoChartMap_on_cone`) equals the LHS chart, and whose `.child = tGeo (acc∘…) ch` covers the flat cube
by `hcov`. So `image_mono (hcov …)` closes it once I select that fanned edge in the biUnion.

WHAT FAILS. Selecting the fanned edge via `Set.subset_iUnion₂ _ (List.mem_map.mpr ⟨⟨i-offset,hp⟩,
List.mem_finRange _, rfl⟩)` → whnf/isDefEq timeout. `attribute [local irreducible] geoChartMap tGeo
qNodeOf qOfCenter centerPerm` (in a `section` around the lemma) moved `whnf`→`isDefEq` timeout but
still times out at the `Set.subset_iUnion₂`/`List.mem_map.mpr rfl` line. `List.mem_map_of_mem` gave a
type mismatch. `set_option maxHeartbeats` bump not yet decisive.
</task>

<output_contract>
Give, in order:
1. The single most likely ROOT of the isDefEq blowup here (index-set unification vs the `rfl` in
   mem_map vs the biUnion body function `s`), one paragraph.
2. The RECOMMENDED idiom to close the subset without the timeout — concrete Lean 4 tactic block.
   Prefer approaches that (a) reindex `⋃ e ∈ l.map fn, F e` to `⋃ p ∈ l, F (fn p)` (clean Fin index),
   or (b) provide the biUnion witness so no higher-order unification over `fn` happens, or (c) a
   `show`/`change` that pins the target before selecting. Name exact Mathlib v4.29 lemmas.
3. Whether `irreducible` should be on `qOfCenter`/`centerPerm` (the true whnf source) vs `geoChartMap`,
   and whether `with_reducible`/`Set.mem_biUnion`/`Finset` would help.
Keep it tight; I will run every suggestion locally before trusting it.
</output_contract>

<grounding_rules>
Flag any lemma name you are not sure exists at Mathlib v4.29 as "verify". Distinguish "this will
compile" (inference) from "this is the standard idiom" (knowledge).
</grounding_rules>
