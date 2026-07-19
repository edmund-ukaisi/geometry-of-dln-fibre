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

/-- **The offset tiling — MEMBERSHIP form (hbij, List-level)**: every global pivot `i` in the node's
range is realised by a fanned edge — the edge owning `i` (via the `dCenterOfNode_edgeSum` offset
partition), with the pivot-`i` `geoChartMap`. Stated + proved at the `List.mem` level (induction on the
edge list + `rw [fannedEdges]`), AWAY from the `iUnion` body, so the heavy `geoChartMap`/`tGeo` are only
rewritten syntactically (no whnf/defeq fight). -/
theorem fannedEdges_pivot_mem (acc : Params M → Params M) (n : StepData M) (i : ℕ) :
    ∀ (offset : ℕ) (edges : List (Edge M)),
      offset ≤ i → i < offset + (edges.map (dCenterOfEdge n)).sum →
      ∃ (c : StepCase) (s : ChartSubst M) (ch : ResolutionTree M),
        Edge.mk c s ch ∈ edges ∧
        Edge.mk c { s with localSub := geoChartMap (dCenterOfNode M) (qNodeOf M) ⟨n, Edge.mk c s ch, i⟩ } (tGeo (acc ∘ geoChartMap (dCenterOfNode M) (qNodeOf M) ⟨n, Edge.mk c s ch, i⟩) ch)
          ∈ fannedEdges acc n offset edges := by
  intro offset edges
  induction edges generalizing offset with
  | nil => intro hlo hhi; simp only [List.map_nil, List.sum_nil, add_zero] at hhi; omega
  | cons e es ih =>
    obtain ⟨c, s, ch⟩ := e
    intro hlo hhi
    by_cases hcase : i < offset + dCenterOfEdge n (Edge.mk c s ch)
    · have hne : dCenterOfEdge n (Edge.mk c s ch) ≠ 0 := by omega
      have hp : i - offset < dCenterOfEdge n (Edge.mk c s ch) := by omega
      have hi' : offset + (i - offset) = i := by omega
      refine ⟨c, s, ch, List.mem_cons_self .., ?_⟩
      -- TACTICAL HOLE (t10, isolated to this List-level line): the fanned edge at pivot `i` is in the
      -- pivot-fan `(finRange d).map (fun p => …offset + ↑p…)`, picking `p = ⟨i-offset, hp⟩` (then
      -- `offset + (i-offset) = i`). The `↑p` (Fin→ℕ) coercion makes `mem_map`/`simp` HO-factor the map
      -- as `((finRange d).map ↑).map …`, so the `∃` reindexes to `ℕ` and the witness type won't align.
      -- MATH TRIVIAL; needs the coercion-aware List idiom (fresh-eyes per controller). Everything else
      -- (the tail recursion here, and `fannedEdges_covers` applying this lemma) is green.
      sorry
    · have hlo' : offset + dCenterOfEdge n (Edge.mk c s ch) ≤ i := by omega
      have hhi' : i < offset + dCenterOfEdge n (Edge.mk c s ch)
          + (es.map (dCenterOfEdge n)).sum := by
        simp only [List.map_cons, List.sum_cons] at hhi; omega
      obtain ⟨c', s', ch', hmem, hfmem⟩ := ih (offset + dCenterOfEdge n (Edge.mk c s ch)) hlo' hhi'
      exact ⟨c', s', ch', List.mem_cons_of_mem _ hmem, by rw [fannedEdges]; exact List.mem_append_right _ hfmem⟩

section
-- Seal the heavy chart/tree machinery so `subset_iUnion₂_of_subset` cannot whnf-unfold it into the
-- classical `qOfCenter`/`centerPerm` machinery (the recurring whnf-timeout hazard). On-cone shape is
-- exposed via the syntactic rewrite `geoChartMap_on_cone`. Sealed only in this section.
attribute [local irreducible] geoChartMap tGeo qNodeOf qOfCenter centerPerm

/-- **The offset tiling (hbij)**: the pivot-`i` chart's image of the flat cube sits inside the
fanned-edge union — the fanned edge realising `i` (`fannedEdges_pivot_mem`) has `localSub = geoChartMap
⟨n,e,i⟩ = (geoChartMap_on_cone)` the pivot-`i` chart, and its child covers the flat cube by IH. -/
theorem fannedEdges_covers (acc : Params M → Params M) (n : StepData M)
    (hd : dCenterOfNode M n ≤ flatDim M) (i : ℕ) (hi : i < dCenterOfNode M n)
    (offset : ℕ) (edges : List (Edge M))
    (hcov : ∀ e ∈ edges, ∀ a : Params M → Params M,
      ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) 1 ⊆ leafPathImages (tGeo a e.child))
    (hlo : offset ≤ i) (hhi : i < offset + (edges.map (dCenterOfEdge n)).sum) :
    (fun w => (qNodeOf M n hd).symm (Prod.map (pivotChart ⟨i, hi⟩) id (qNodeOf M n hd w)))
        '' (⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) 1)
      ⊆ ⋃ e ∈ fannedEdges acc n offset edges, e.subst.localSub '' leafPathImages e.child := by
  obtain ⟨c', s', ch', hmemedge, hfmem⟩ := fannedEdges_pivot_mem acc n i offset edges hlo hhi
  refine Set.subset_iUnion₂_of_subset (t := fun (e : Edge M)
      (_ : e ∈ fannedEdges acc n offset edges) => e.subst.localSub '' leafPathImages e.child)
    _ hfmem ?_
  simp only [Edge.subst, Edge.child, geoChartMap_on_cone n (Edge.mk c' s' ch') i hd hi]
  exact Set.image_mono (hcov (Edge.mk c' s' ch') hmemedge _)

end

/-- `leafOfState`'s source box is the flat cube (both `dite` branches). -/
theorem leafOfState_srcBox (s : ConState L) :
    (leafOfState M s).srcBox = ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) 1 := by
  unfold leafOfState; split <;> rfl

/-- **A `conOracle` step has a nonempty child list** — every step branch (rollover / case-1 / case-2)
emits ≥1 child; the terminal branches are not steps. Needed for the `dCenterOfNode = 0` (chartless)
node in the cover: the identity passthrough of one covering child carries the flat cube. -/
theorem conOracle_step_children_ne_nil (s : ConState L) (node : StepData M)
    (children : List (StepChild M s)) {hn hl hs}
    (hoc : conOracle M s = ConDecision.step node children hn hl hs) : children ≠ [] := by
  by_cases h1 : L ≤ s.layer
  · rw [conOracle, dif_pos h1] at hoc; exact absurd hoc (by simp [oracleTerminal])
  · by_cases h2 : widthMinUpto M (s.layer + 1) ≤ s.cleared
    · have horacle : conOracle M s = rolloverDecision M s (le_of_lt (not_le.mp h1)) h2 := by
        unfold conOracle; rw [dif_neg h1, dif_pos h2]
      rw [horacle] at hoc
      have h := congrArg ConDecision.stepChildren hoc
      simp only [rolloverDecision, ConDecision.stepChildren] at h
      rw [← h]; exact List.cons_ne_nil _ _
    · have hlt : s.cleared < widthMinUpto M (s.layer + 1) := not_le.mp h2
      have hcap : s.cleared < layerCap M := lt_of_lt_of_le hlt (widthMinUpto_le_layerCap M _)
      have hL1 : s.layer + 1 < L + 1 := by omega
      rcases hmin : ((List.finRange s.numDiv).filterMap (fun k =>
          if s.cleared + 1 ≤ s.divTilde k ∧ s.divTilde k + 1 ≤ widthMinUpto M s.layer
          then some (s.divTilde k) else none)).min? with _ | target
      · have horacle : conOracle M s = case2Decision M s
            (widthMinUpto M s.layer - s.cleared) (M ⟨s.layer + 1, hL1⟩ - s.cleared) hcap := by
          unfold conOracle; rw [dif_neg h1, dif_neg h2]; split <;> simp_all only [reduceCtorEq]
        rw [horacle] at hoc
        have h := congrArg ConDecision.stepChildren hoc
        simp only [case2Decision, ConDecision.stepChildren] at h
        rw [← h]; exact List.cons_ne_nil _ _
      · rcases hf : chooseMin s target with _ | f
        · have horacle : conOracle M s = oracleTerminal M s := by
            unfold conOracle; rw [dif_neg h1, dif_neg h2]
            split <;> simp_all only [reduceCtorEq, Option.some.injEq]
            all_goals (try subst_vars)
            all_goals (try (split <;> simp_all only [reduceCtorEq]))
          rw [horacle] at hoc; exact absurd hoc (by simp [oracleTerminal])
        · have hgt : s.cleared < target := by
            obtain ⟨hmemtar, -⟩ := List.min?_eq_some_iff.mp hmin
            rw [List.mem_filterMap] at hmemtar
            obtain ⟨k0, -, hk0⟩ := hmemtar
            by_cases hc0 : s.cleared + 1 ≤ s.divTilde k0 ∧ s.divTilde k0 + 1 ≤ widthMinUpto M s.layer
            · rw [if_pos hc0] at hk0; have := Option.some.inj hk0; omega
            · rw [if_neg hc0] at hk0; exact absurd hk0 (by simp)
          have horacle : conOracle M s = case1Decision M s f (target - s.cleared)
              (widthMinUpto M s.layer - s.cleared) (M ⟨s.layer + 1, hL1⟩ - s.cleared)
              (not_le.mp h1) (by omega) (by rw [(chooseMin_spec s target hf).1]; omega) hcap := by
            unfold conOracle; rw [dif_neg h1, dif_neg h2]
            split
            · rename_i target' heq
              obtain rfl : target' = target := Option.some.inj (heq ▸ hmin)
              split
              · rename_i f' hf'; obtain rfl : f' = f := Option.some.inj (hf' ▸ hf); rfl
              · rename_i hf'; exact absurd (hf' ▸ hf) (by simp)
            · rename_i heq; exact absurd (heq ▸ hmin) (by simp)
          rw [horacle] at hoc
          have h := congrArg ConDecision.stepChildren hoc
          simp only [case1Decision, ConDecision.stepChildren] at h
          rw [← h]; exact List.cons_ne_nil _ _

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
      · -- chartless node (`dCenterOfNode = 0`: rollover or zero-block case-2): all edges are
        -- chartless, so the identity passthrough of the first (covering) child carries the flat cube.
        have hdz : dCenterOfNode M node = 0 := by omega
        obtain ⟨c₀, cs, hcons⟩ :=
          List.exists_cons_of_ne_nil (conOracle_step_children_ne_nil s node children hoc)
        subst hcons
        have he0 : dCenterOfEdge node
            (Edge.mk c₀.ecase c₀.esubst (buildTree M (conOracle M) c₀.child)) = 0 := by
          rw [hdz] at hsum; simp only [List.map_cons, List.sum_cons] at hsum; omega
        rw [List.map_cons, fannedEdges, if_pos he0]
        refine Set.subset_iUnion₂_of_subset
          (Edge.mk c₀.ecase { c₀.esubst with localSub := id }
            (tGeo acc (buildTree M (conOracle M) c₀.child)))
          (List.mem_append_left _ (List.mem_singleton_self _)) ?_
        simp only [Edge.subst, Edge.child, Set.image_id]
        exact hchildcov (Edge.mk c₀.ecase c₀.esubst (buildTree M (conOracle M) c₀.child))
          (by rw [List.map_cons]; exact List.mem_cons_self ..) acc

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
