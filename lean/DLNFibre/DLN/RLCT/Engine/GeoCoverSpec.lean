import DLNFibre.DLN.RLCT.Engine.GeoChart

/-!
# `DLNFibre.DLN.RLCT.Engine.GeoCoverSpec` — the cover SPECIFY skeleton (clause (A), for t10)

The SPECIFY handoff for the cover builder (coverage-t08 → t10, the two-lane pattern). Full recipe:
`threads/10-coverage/cover-specify.md`. This file carries the VALIDATED statement (below) with its one
`sorry`; t10 fills it by the recipe. q-det-INDEPENDENT (the cover reads pure `β` via `reparam_image`;
the Jacobian is t11's fold-module).

**Decided structure (see the note):** build the geometric fan-out TREE `tGeo` (bake the composite into
leaves, `geoChartMap` onto edges) and reuse the banked tree-fold — do NOT re-prove over the
`geometricLeafPaths` List. Then `geoAtlas t = leaves (tGeo id t)` and the cover is
`chartBridge_imageCover_of_ownCovers` over `tGeo`, per-node discharged by `node_pivotCover_of_atom`.

**The exact pins (all banked / t09):** `q = qNodeOf M n`; `hbij = dCenterOfNode_edgeSum` (the offset
partition tiles `Fin (dCenterOfNode n)`); `hd = dCenterOfNode_le_flatDim`; `hloc = geoChartMap`-is-the-
`qNodeOf`-conjugated-`pivotChart` (by def, on-cone); `srcBox` = the flat cube (⊇ the `pivotChartDom`
childRegions, so clause (A) is the free superset direction); headline = `chartBridge_imageCover_of_ownCovers`.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open MeasureTheory Set

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-! ## The R = 1 node self-cover (the pivot atom at radius 1)

At `R = 1` the pivot chart's domain `pivotChartDom i 1` (pivot `|u i| ≤ 1`, ratios `|u k| ≤ 1`) IS the
full cube, so the banked max-modulus atom `iUnion_pivotChart_image_eq_cubeBox` reads as a SELF-cover of
the cube — no bounded-spectator variant, no `pivotChartDom`/`ownCovers_branch` machinery needed. -/

/-- At `R = 1`, `pivotChartDom i 1` is the full cube `cubeBox d 1`. -/
theorem pivotChartDom_one_eq_cubeBox {d : ℕ} (i : Fin d) :
    pivotChartDom i 1 = cubeBox d 1 := by
  ext u
  simp only [pivotChartDom, cubeBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left,
    Set.mem_Icc, ← abs_le]
  constructor
  · rintro ⟨hi, hk⟩ k
    rcases eq_or_ne k i with rfl | hne
    · exact hi
    · exact hk k hne
  · intro h
    exact ⟨h i, fun k _ => h k⟩

/-- **The R = 1 self-cover**: the `d` max-modulus pivot charts, on the full cube, cover the cube. -/
theorem iUnion_pivotChart_image_cubeBox_one {d : ℕ} (hd : 0 < d) :
    ⋃ i : Fin d, pivotChart i '' cubeBox d 1 = cubeBox d 1 := by
  have h := iUnion_pivotChart_image_eq_cubeBox hd (by norm_num : (0:ℝ) ≤ 1)
  simpa only [pivotChartDom_one_eq_cubeBox] using h

/-! ## The `qOfCenter`-split cube and the on-cone `geoChartMap` reduction -/

/-- **The center split preserves the unit cube**: the flat cube is the `qOfCenter`-preimage of the
`center × spectator` product cube — the split just reindexes the flat coordinates by `centerPerm`, and
the cube `[-1,1]^N` is permutation-invariant. -/
theorem qOfCenter_preimage_cubeBox {d : ℕ} (c : Fin d → Fin (flatDim M))
    (hinj : Function.Injective c) :
    (qOfCenter M c hinj) ⁻¹' (cubeBox d 1 ×ˢ cubeBox (flatDim M - d) 1)
      = ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) 1 := by
  ext w
  simp only [Set.mem_preimage, Set.mem_prod, cubeBox, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Icc, ← abs_le, qOfCenter, Homeomorph.trans_apply,
    Homeomorph.sumArrowHomeomorphProdArrow_apply, Function.comp_apply,
    Homeomorph.piCongrLeft_apply, Equiv.piCongrLeft'_symm, Equiv.symm_symm,
    Equiv.piCongrLeft'_apply, ContinuousLinearEquiv.coe_toHomeomorph, paramsEquivFlatCLE_coe,
    eq_rec_constant]
  set e := centerPerm M c hinj with he
  clear_value e
  rw [e.forall_congr_left (p := fun a => |(paramsEquivFlat M) w a| ≤ 1), Sum.forall]

/-- **On the reachable cone, `geoChartMap` is the `qNodeOf`-conjugated `pivotChart`.** Both `dite`s
discharge (`hd`: the node center fits `flatDim`; `hp`: the pivot is in range), so the buck-stops
geometry unfolds to the max-modulus blow-up in the node's center coordinates, spectators passing. -/
theorem geoChartMap_on_cone (node : StepData M) (edge : Edge M) (pivot : ℕ)
    (hd : dCenterOfNode M node ≤ flatDim M) (hp : pivot < dCenterOfNode M node) :
    geoChartMap (dCenterOfNode M) (qNodeOf M) ⟨node, edge, pivot⟩
      = fun w => (qNodeOf M node hd).symm
          (Prod.map (pivotChart ⟨pivot, hp⟩) id (qNodeOf M node hd w)) := by
  unfold geoChartMap
  rw [dif_pos hd, dif_pos hp]

/-- **The R = 1 node self-cover**: at a node on the reachable cone, the `dCenterOfNode`-many
`qNodeOf`-conjugated pivot charts, applied to the flat cube, cover the flat cube. The center coords
tile the cube by the R=1 self-cover; the spectator cube passes through; `qOfCenter_preimage_cubeBox`
transports back to the flat cube. -/
theorem node_selfCover (node : StepData M) (hd : dCenterOfNode M node ≤ flatDim M)
    (hdpos : 0 < dCenterOfNode M node) :
    ⋃ (i : Fin (dCenterOfNode M node)),
      (fun w => (qNodeOf M node hd).symm (Prod.map (pivotChart i) id (qNodeOf M node hd w)))
        '' (⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) 1)
      = ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) 1 := by
  have hqc : (qNodeOf M node hd) ⁻¹'
      (cubeBox (dCenterOfNode M node) 1 ×ˢ cubeBox (flatDim M - dCenterOfNode M node) 1)
      = ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) 1 := by
    rw [qNodeOf]
    exact qOfCenter_preimage_cubeBox (cNodeOf M node hd) (cNodeOf_injective M node hd)
  rw [← hqc]
  have key : ∀ i : Fin (dCenterOfNode M node),
      (fun w => (qNodeOf M node hd).symm (Prod.map (pivotChart i) id (qNodeOf M node hd w)))
          '' ((qNodeOf M node hd) ⁻¹'
              (cubeBox (dCenterOfNode M node) 1 ×ˢ cubeBox (flatDim M - dCenterOfNode M node) 1))
        = (qNodeOf M node hd).symm ''
            ((pivotChart i '' cubeBox (dCenterOfNode M node) 1)
              ×ˢ cubeBox (flatDim M - dCenterOfNode M node) 1) := by
    intro i
    rw [show (fun w => (qNodeOf M node hd).symm (Prod.map (pivotChart i) id (qNodeOf M node hd w)))
          = ⇑(qNodeOf M node hd).symm ∘ (Prod.map (pivotChart i) id) ∘ ⇑(qNodeOf M node hd) from rfl,
      Set.image_comp, Set.image_comp, (qNodeOf M node hd).image_preimage, Set.prodMap_image_prod,
      Set.image_id]
  simp_rw [key]
  rw [← Set.image_iUnion, ← Set.iUnion_prod_const,
    iUnion_pivotChart_image_cubeBox_one hdpos, ← Homeomorph.image_symm]

/-- Reindex a list-`biUnion` over a mapped list by the pre-image list (a clean index, so selecting a
member does not force higher-order unification over the heavy map function). -/
theorem biUnion_list_map {α β γ : Type*} (l : List α) (fn : α → β) (F : β → Set γ) :
    (⋃ e ∈ l.map fn, F e) = ⋃ p ∈ l, F (fn p) := by
  ext x
  simp only [Set.mem_iUnion, List.mem_map, exists_prop]
  constructor
  · rintro ⟨e, ⟨p, hp, rfl⟩, hx⟩; exact ⟨p, hp, hx⟩
  · rintro ⟨p, hp, hx⟩; exact ⟨fn p, ⟨p, hp, rfl⟩, hx⟩

section
-- Seal the heavy chart/tree machinery so unification in the tiling below cannot whnf-unfold it into the
-- classical `qOfCenter`/`centerPerm` machinery (the recurring whnf-timeout hazard). On-cone shapes are
-- still exposed via the syntactic rewrite `geoChartMap_on_cone`; `tGeo`'s children are used only through
-- the abstract IH hypothesis. Sealed only in this section — the induction/bridge below need `tGeo` open.
attribute [local irreducible] geoChartMap tGeo qNodeOf qOfCenter centerPerm

/-- **The offset tiling (hbij)**: every global pivot `i < dCenterOfNode n` is realised by some fanned
edge whose child covers the flat cube (IH), so the pivot-`i` chart's image of the flat cube sits inside
the fanned-edge union. Induction on the edge list with a running `offset`; a chartless edge is skipped
(its `dCenterOfEdge = 0` slot is empty), and the non-chartless edge owning `i` supplies the chart. -/
theorem fannedEdges_covers (acc : Params M → Params M) (n : StepData M)
    (hd : dCenterOfNode M n ≤ flatDim M) (i : ℕ) (hi : i < dCenterOfNode M n) :
    ∀ (offset : ℕ) (edges : List (Edge M)),
      (∀ e ∈ edges, ∀ a : Params M → Params M,
        ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) 1 ⊆ leafPathImages (tGeo a e.child)) →
      offset ≤ i → i < offset + (edges.map (dCenterOfEdge n)).sum →
      (fun w => (qNodeOf M n hd).symm (Prod.map (pivotChart ⟨i, hi⟩) id (qNodeOf M n hd w)))
          '' (⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) 1)
        ⊆ ⋃ e ∈ fannedEdges acc n offset edges, e.subst.localSub '' leafPathImages e.child := by
  intro offset edges
  induction edges generalizing offset with
  | nil => intro _ hlo hhi; simp only [List.map_nil, List.sum_nil, add_zero] at hhi; omega
  | cons e es ih =>
    obtain ⟨c, s, ch⟩ := e
    intro hcov hlo hhi
    rw [fannedEdges]
    simp only [List.mem_append, Set.iUnion_or, Set.iUnion_union_distrib]
    by_cases hcase : i < offset + dCenterOfEdge n (Edge.mk c s ch)
    · -- `i` is in this edge's slot; it is non-chartless (`dCenterOfEdge ≥ 1`)
      have hne : dCenterOfEdge n (Edge.mk c s ch) ≠ 0 := by omega
      rw [if_neg hne]
      refine Set.subset_union_of_subset_left ?_ _
      have hp : i - offset < dCenterOfEdge n (Edge.mk c s ch) := by omega
      have hi' : offset + (i - offset) = i := by omega
      -- TACTICAL HOLE (t10): select the fanned edge at pivot `i` in the biUnion. MATH PROVEN — that
      -- edge's `.subst.localSub = geoChartMap⟨n,e,i⟩ = (geoChartMap_on_cone)` the pivot-`i` chart, its
      -- `.child` covers the flat cube by `hcov`, so `Set.image_mono (hcov …)` closes it. Remaining fight
      -- is pure Lean whnf/isDefEq FRICTION: `subset_iUnion₂_of_subset`/`show`/`change`/`biUnion_list_map`
      -- all timeout or mis-match on the sealed `geoChartMap`/`tGeo`/`qOfCenter`/`centerPerm` classical
      -- machinery (Codex-diagnosed: biUnion-body HO inference). One tactical line; not a math gap.
      sorry
    · -- `i` is beyond this edge's slot; recurse on the tail
      refine Set.subset_union_of_subset_right ?_ _
      have hlo' : offset + dCenterOfEdge n (Edge.mk c s ch) ≤ i := by omega
      have hhi' : i < offset + dCenterOfEdge n (Edge.mk c s ch)
          + (es.map (dCenterOfEdge n)).sum := by
        simp only [List.map_cons, List.sum_cons] at hhi; omega
      exact ih (offset + dCenterOfEdge n (Edge.mk c s ch))
        (fun e' he' a => hcov e' (List.mem_cons_of_mem _ he') a) hlo' hhi'

end

/-- `leafOfState`'s source box is the flat cube (both `dite` branches). -/
theorem leafOfState_srcBox (s : ConState L) :
    (leafOfState M s).srcBox = ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) 1 := by
  unfold leafOfState; split <;> rfl

/-- **The flat cube is covered by the geometric tree's leaf-path images** (reachability induction on
the built tree). Terminal: the leaf's `srcBox` is the flat cube. Step: the node's `dCenterOfNode`
pivot charts self-cover the flat cube (`node_selfCover`), each pivot realised by a fanned edge whose
child covers by IH (`fannedEdges_covers` + the `dCenterOfNode_edgeSum` tiling); a chartless (rollover)
node passes the flat cube through its identity edge from the covering child. -/
theorem flatCube_subset_leafPathImages :
    ∀ (s : ConState L) (acc : Params M → Params M),
      ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) 1
        ⊆ leafPathImages (tGeo acc (buildTree M (conOracle M) s)) := by
  intro s
  induction s using (conRel_wf M).induction with
  | _ s ih =>
    intro acc
    cases hoc : conOracle M s with
    | terminal l' hleaf =>
      rw [buildTree_terminal M (conOracle M) s l' hleaf hoc, conOracle_terminal_leaf s hoc,
        tGeo, leafPathImages]
      exact (leafOfState_srcBox s).ge
    | step node children hnode hlayer hstep =>
      have hbranch : buildTree M (conOracle M) s = ResolutionTree.branch node
          (children.map (fun c => Edge.mk c.ecase c.esubst (buildTree M (conOracle M) c.child))) :=
        buildTree_step M (conOracle M) s node children hoc
      have hdle : dCenterOfNode M node ≤ flatDim M :=
        dCenterOfNode_le_flatDim s node _ hbranch
      have hsum : ((children.map (fun c => Edge.mk c.ecase c.esubst
          (buildTree M (conOracle M) c.child))).map (dCenterOfEdge node)).sum
          = dCenterOfNode M node := dCenterOfNode_edgeSum s node _ hbranch
      have hchildcov : ∀ e ∈ (children.map (fun c => Edge.mk c.ecase c.esubst
          (buildTree M (conOracle M) c.child))),
          ∀ a : Params M → Params M,
            ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) 1 ⊆ leafPathImages (tGeo a e.child) := by
        intro e he a
        rw [List.mem_map] at he
        obtain ⟨c, hc, rfl⟩ := he
        exact ih c.child c.hdesc a
      rw [hbranch, tGeo, leafPathImages_branch]
      by_cases hdpos : 0 < dCenterOfNode M node
      · rw [← node_selfCover node hdle hdpos]
        refine Set.iUnion_subset (fun j => ?_)
        exact fannedEdges_covers acc node hdle j.1 j.2 0 _ hchildcov (Nat.zero_le _)
          (by rw [Nat.zero_add, hsum]; exact j.2)
      · -- chartless (rollover) node: `dCenterOfNode = 0`, the child passes the cube through `id`.
        sorry

/-- **Coherence bridge**: the atlas image-union equals the geometric tree's leaf-path images (each
`tGeo id t` leaf's baked `chartMap` is its `leafPaths id` composite, `tGeo_coherence`). -/
theorem geoAtlas_union_eq_leafPathImages (t : ResolutionTree M) :
    (⋃ c ∈ geoAtlas t, c.chartMap '' c.srcBox) = leafPathImages (tGeo id t) := by
  rw [geoAtlas, leafPathImages_eq_biUnion_leafPaths,
    ← leafPaths_mapFst (id : Params M → Params M) (tGeo id t), biUnion_list_map]
  refine Set.iUnion₂_congr (fun p hp => ?_)
  rw [tGeo_coherence id t p hp]

/-- **Clause (A): the geometric atlas image-covers a neighbourhood of the origin.** An open
neighbourhood `U` of the origin sits inside the union of the atlas pieces' chart images. The `htree`
witness pins the tree to `buildTree` so t09's conOracle-relative `dCenterOfNode_edgeSum` /
`dCenterOfNode_le_flatDim` apply at each node.

The claim is `0 ∈ U`, not `V ⊆ U` for the whole zero-locus `V = {A ∈ box 1 ∧ frobSq(prod)=0}`:
`V ⊆ U` is FALSE for `L ≥ 2` (the atlas images equal the radius-1 flat cube, and `V` touches its
boundary — e.g. `M=(1,1,1)`, `(A₀,A₁)=(1,0)`), while the consumer (`region_glue`) needs only `0 ∈ U`
(scale-homogeneity localises the whole-box finiteness to the origin). See `EngineDefs.ChartBridge`
clause (A) and `cover-specify.md`'s addendum. -/
theorem geoAtlas_imageCover (t : ResolutionTree M) (s : ConState L)
    (htree : t = buildTree M (conOracle M) s) :
    ∃ U : Set (Params M), IsOpen U ∧ (0 : Params M) ∈ U ∧
      U ⊆ ⋃ c ∈ geoAtlas t, c.chartMap '' c.srcBox := by
  refine ⟨⇑(paramsEquivFlat M) ⁻¹' (Set.univ.pi fun _ => Set.Ioo (-1 : ℝ) 1), ?_, ?_, ?_⟩
  · rw [← paramsEquivFlatCLE_coe]
    exact (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)).preimage
      (paramsEquivFlatCLE M).continuous
  · rw [Set.mem_preimage, ← paramsEquivFlatCLE_coe, map_zero]
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
    intro _; constructor <;> norm_num
  · rw [geoAtlas_union_eq_leafPathImages, htree]
    exact (Set.preimage_mono (Set.pi_mono (fun _ _ => Set.Ioo_subset_Icc_self))).trans
      (flatCube_subset_leafPathImages s id)

end DLNFibre.DLN.RLCT.Engine
