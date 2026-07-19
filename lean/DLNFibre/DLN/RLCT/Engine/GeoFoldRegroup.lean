import DLNFibre.DLN.RLCT.Engine.GeoDiagSwap
import DLNFibre.DLN.RLCT.Engine.DivBirthReach

/-!
# `DLNFibre.DLN.RLCT.Engine.GeoFoldRegroup` — the fold-Jacobian regrouping cocycle machinery (t14)

The internal machinery for `geoAtlas_fold_det` (`GeoLeafJacobian`). Following the t11 handoff addendum
(§HANDOFF) and cert §1/§2 (`threads/18-fold-regroup/cert-fold-regroup.md`):

* **Differentiability** of the normalized chart `geoChartMapNorm (fun _ => id)` (so the parametric
  chain-rule fold `abs_det_fderiv_foldr_comp` applies).
* **(α) the §0 chart-action** of `geoChartMapNorm` on flat coordinates (the workhorse for the regroup).
* **(β) the coherence** `divCoord = diagTargetOf` (the leaf ledger names the same diagonal cell the chart
  reads).
* the **leafPaths → foldr bridge** + the **cocycle maintenance** (threaded ledger, innermost-first).

Built incrementally, banking greens. The headline is scoped to `conRoot` (t14 correction, ruling A).
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- **`geoChartMapNorm (fun _ => id)` is differentiable everywhere.** On-cone it is the composite
`geoChartMap g ∘ S ∘ id` (`geoChartMap_differentiable` + `flatSwapCLE_differentiable`); off-cone / out of
range it is `id`. So any list of these charts satisfies the `abs_det_fderiv_foldr_comp` hypothesis. -/
theorem geoChartMapNorm_differentiable (g : GeoChart M) :
    Differentiable ℝ (geoChartMapNorm (fun _ => id) g) := by
  unfold geoChartMapNorm
  by_cases hd : dCenterOfNode M g.node ≤ flatDim M
  · rw [dif_pos hd]
    by_cases hp : g.pivot < dCenterOfNode M g.node
    · rw [dif_pos hp]
      exact (geoChartMap_differentiable g).comp
        ((flatSwapCLE_differentiable M _ _).comp differentiable_id)
    · rw [dif_neg hp]; exact differentiable_id
  · rw [dif_neg hd]; exact differentiable_id

/-! ## (α) The §0 chart-action of `geoChartMap`/`geoChartMapNorm` on flat coordinates -/

/-- **The second component of `qOfCenterCLE` reads the complement coordinate** (`_snd`, mirror of the
banked `qOfCenterCLE_fst_apply`): `(q y).2 j = z_{centerPerm.symm (inr j)}(y)`. -/
theorem qOfCenterCLE_snd_apply (M : Fin (L + 1) → ℕ) {d : ℕ} (c : Fin d → Fin (flatDim M))
    (hinj : Function.Injective c) (w : Params M) (j : Fin (flatDim M - d)) :
    (qOfCenterCLE M c hinj w).2 j = paramsEquivFlat M w ((centerPerm M c hinj).symm (Sum.inr j)) := by
  have hcoe : ⇑(LinearEquiv.piCongrLeft ℝ (fun _ : Fin d ⊕ Fin (flatDim M - d) => ℝ)
      (centerPerm M c hinj)) = ⇑(Equiv.piCongrLeft (fun _ : Fin d ⊕ Fin (flatDim M - d) => ℝ)
      (centerPerm M c hinj)) := rfl
  unfold qOfCenterCLE
  simp only [ContinuousLinearEquiv.trans_apply, LinearEquiv.coe_toContinuousLinearEquiv',
    paramsEquivFlatCLE_coe, LinearEquiv.sumArrowLequivProdArrow_apply_snd, hcoe]
  conv_lhs => rw [show (Sum.inr j : Fin d ⊕ Fin (flatDim M - d))
        = centerPerm M c hinj ((centerPerm M c hinj).symm (Sum.inr j)) from
      (Equiv.apply_symm_apply _ _).symm]
  rw [Equiv.piCongrLeft_apply_apply]

/-- **The master flat read** of the `qOfCenterCLE` split: every flat coordinate `cc` is read off the
split by routing through `centerPerm` — center cells (`inl`) from the first factor, spectators (`inr`)
from the second. `z_cc(y) = Sum.elim (q y).1 (q y).2 (centerPerm cc)`. -/
theorem qOfCenterCLE_flat_read (M : Fin (L + 1) → ℕ) {d : ℕ} (c : Fin d → Fin (flatDim M))
    (hinj : Function.Injective c) (y : Params M) (cc : Fin (flatDim M)) :
    paramsEquivFlat M y cc
      = Sum.elim (qOfCenterCLE M c hinj y).1 (qOfCenterCLE M c hinj y).2
          (centerPerm M c hinj cc) := by
  rcases h : centerPerm M c hinj cc with i | j
  · have hcc : cc = c i := by
      rw [← centerPerm_symm_inl M c hinj i, ← h, Equiv.symm_apply_apply]
    rw [Sum.elim_inl, hcc, qOfCenterCLE_fst_apply]
  · have hcc : cc = (centerPerm M c hinj).symm (Sum.inr j) := by
      rw [← h, Equiv.symm_apply_apply]
    rw [Sum.elim_inr, hcc, qOfCenterCLE_snd_apply]

/-- `centerPerm` sends a center cell `c i` to `Sum.inl i` (inverse of `centerPerm_symm_inl`). -/
theorem centerPerm_apply_c (M : Fin (L + 1) → ℕ) {d : ℕ} (c : Fin d → Fin (flatDim M))
    (hinj : Function.Injective c) (i : Fin d) : centerPerm M c hinj (c i) = Sum.inl i := by
  rw [← centerPerm_symm_inl M c hinj i, Equiv.apply_symm_apply]

/-- **`q` conjugates `geoChartMap` to the block map**: on-cone, `q (geoChartMap g x) = (pivotChart ⟨pivot⟩ ×
id) (q x)` — the chart acts as `pivotChart` on the center block and identity on the rest, read through the
`q`-split (`conjBlockMap` + `apply_symm_apply`). -/
theorem q_comp_geoChartMap (g : GeoChart M) (x : Params M)
    (hd : dCenterOfNode M g.node ≤ flatDim M) (hp : g.pivot < dCenterOfNode M g.node) :
    qOfCenterCLE M (cNodeOf M g.node hd) (cNodeOf_injective M g.node hd)
        (geoChartMap (dCenterOfNode M) (qNodeOf M) g x)
      = Prod.map (pivotChart (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node))) id
          (qOfCenterCLE M (cNodeOf M g.node hd) (cNodeOf_injective M g.node hd) x) := by
  have hfun : geoChartMap (dCenterOfNode M) (qNodeOf M) g
      = conjBlockMap (qOfCenterCLE M (cNodeOf M g.node hd) (cNodeOf_injective M g.node hd))
          (pivotChart (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node))) := by
    unfold geoChartMap qNodeOf conjBlockMap
    rw [dif_pos hd, dif_pos hp]; rfl
  rw [hfun]
  simp only [conjBlockMap, ContinuousLinearEquiv.apply_symm_apply]

/-- **The master flat action of `geoChartMap`** (on-cone): every flat coordinate `cc` of the image is
read through the `q`-split — center cells go through `pivotChart`, spectators pass through. -/
theorem paramsEquivFlat_geoChartMap (g : GeoChart M) (x : Params M)
    (hd : dCenterOfNode M g.node ≤ flatDim M) (hp : g.pivot < dCenterOfNode M g.node)
    (cc : Fin (flatDim M)) :
    paramsEquivFlat M (geoChartMap (dCenterOfNode M) (qNodeOf M) g x) cc
      = Sum.elim (pivotChart (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node))
            (qOfCenterCLE M (cNodeOf M g.node hd) (cNodeOf_injective M g.node hd) x).1)
          (qOfCenterCLE M (cNodeOf M g.node hd) (cNodeOf_injective M g.node hd) x).2
          (centerPerm M (cNodeOf M g.node hd) (cNodeOf_injective M g.node hd) cc) := by
  rw [qOfCenterCLE_flat_read M (cNodeOf M g.node hd) (cNodeOf_injective M g.node hd)
      (geoChartMap (dCenterOfNode M) (qNodeOf M) g x) cc, q_comp_geoChartMap g x hd hp]
  rfl

/-- **(α)-pivot** (the pivot coordinate is FREE): `z_{c ⟨pivot⟩}(geoChartMap g x) = z_{c ⟨pivot⟩}(x)`. -/
theorem geoChartMap_flat_pivot (g : GeoChart M) (x : Params M)
    (hd : dCenterOfNode M g.node ≤ flatDim M) (hp : g.pivot < dCenterOfNode M g.node) :
    paramsEquivFlat M (geoChartMap (dCenterOfNode M) (qNodeOf M) g x)
        (cNodeOf M g.node hd (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node)))
      = paramsEquivFlat M x (cNodeOf M g.node hd (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node))) := by
  rw [paramsEquivFlat_geoChartMap g x hd hp, centerPerm_apply_c, Sum.elim_inl, pivotChart,
    if_pos rfl, qOfCenterCLE_fst_apply]

/-- **(α)-center** (a non-pivot center cell is SCALED by the pivot): for `i ≠ ⟨pivot⟩`,
`z_{c i}(geoChartMap g x) = z_{c ⟨pivot⟩}(x) · z_{c i}(x)`. -/
theorem geoChartMap_flat_center (g : GeoChart M) (x : Params M)
    (hd : dCenterOfNode M g.node ≤ flatDim M) (hp : g.pivot < dCenterOfNode M g.node)
    (i : Fin (dCenterOfNode M g.node)) (hi : i ≠ (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node))) :
    paramsEquivFlat M (geoChartMap (dCenterOfNode M) (qNodeOf M) g x) (cNodeOf M g.node hd i)
      = paramsEquivFlat M x (cNodeOf M g.node hd (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node)))
        * paramsEquivFlat M x (cNodeOf M g.node hd i) := by
  rw [paramsEquivFlat_geoChartMap g x hd hp, centerPerm_apply_c, Sum.elim_inl, pivotChart,
    if_neg hi, qOfCenterCLE_fst_apply, qOfCenterCLE_fst_apply]

/-- **(α)-spectator** (a non-center cell is FIXED): if `cc` is not a center cell (`∀ i, c i ≠ cc`),
`z_cc(geoChartMap g x) = z_cc(x)`. -/
theorem geoChartMap_flat_spectator (g : GeoChart M) (x : Params M)
    (hd : dCenterOfNode M g.node ≤ flatDim M) (hp : g.pivot < dCenterOfNode M g.node)
    (cc : Fin (flatDim M)) (hcc : ∀ i, cNodeOf M g.node hd i ≠ cc) :
    paramsEquivFlat M (geoChartMap (dCenterOfNode M) (qNodeOf M) g x) cc
      = paramsEquivFlat M x cc := by
  rw [paramsEquivFlat_geoChartMap g x hd hp]
  rcases h : centerPerm M (cNodeOf M g.node hd) (cNodeOf_injective M g.node hd) cc with i | j
  · exact absurd (by rw [← centerPerm_symm_inl M (cNodeOf M g.node hd)
        (cNodeOf_injective M g.node hd) i, ← h, Equiv.symm_apply_apply] :
        cNodeOf M g.node hd i = cc) (hcc i)
  · rw [Sum.elim_inr, qOfCenterCLE_snd_apply]
    congr 1
    rw [← h, Equiv.symm_apply_apply]

/-- **`geoChartMapNorm (fun _ => id)` on-cone unfolds to `geoChartMap ∘ S`** (the diagonal-normalization
swap composed inside, gauge `= id`). The bridge that lets the `(α)` `geoChartMap` reads + `flatSwapCLE`
relabel compute the normalized chart's flat action. -/
theorem geoChartMapNorm_apply_oncone (g : GeoChart M) (x : Params M)
    (hd : dCenterOfNode M g.node ≤ flatDim M) (hp : g.pivot < dCenterOfNode M g.node) :
    geoChartMapNorm (fun _ => id) g x
      = geoChartMap (dCenterOfNode M) (qNodeOf M) g
          (flatSwapCLE M (cNodeOf M g.node hd (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node)))
            (diagTargetOf M g.node g.edge (by omega)) x) := by
  unfold geoChartMapNorm
  rw [dif_pos hd, dif_pos hp]
  rfl

/-! ## (β) The coherence `divCoord = diagTargetOf` (kernel: `birthFlatCoord` is a `flatCoordOf`-diagonal) -/

/-- **(β)-kernel**: on a valid birth corner, `birthFlatCoord` IS the diagonal `flatCoordOf` cell
`(a, b, b)`. This is the shared form of both the leaf ledger's `divCoord` (`= birthFlatCoord ∘ divBirthCoord`,
`EngineConstruction:1796`) and the chart's `diagTargetOf` (`= flatCoordOf` of the divisor's `divBirthCoord`,
`GeoChart`) — so the two name the SAME diagonal cell, which the regrouping needs. -/
theorem birthFlatCoord_eq_flatCoordOf (M : Fin (L + 1) → ℕ) (s : ConState L) (k : Fin s.numDiv)
    (h : 0 < flatDim M) (hv : CornerValid M (s.divBirthCoord k)) :
    ∃ (hL : (s.divBirthCoord k).1 < L)
      (hi : (s.divBirthCoord k).2 < M (Fin.castSucc ⟨(s.divBirthCoord k).1, hL⟩))
      (hj : (s.divBirthCoord k).2 < M (Fin.succ ⟨(s.divBirthCoord k).1, hL⟩)),
      birthFlatCoord M s k h
        = flatCoordOf M ⟨(s.divBirthCoord k).1, hL⟩ ⟨(s.divBirthCoord k).2, hi⟩
            ⟨(s.divBirthCoord k).2, hj⟩ := by
  obtain ⟨hL, hi, hj, heq⟩ := birthFlatCoord_of_valid (h := h) hv
  exact ⟨hL, hi, hj, by rw [heq, flatCoordOf]⟩

/-! ## Bridge: `tGeo`-leaf composites are differentiable (the `abs_det_fderiv_foldr_comp` hypothesis) -/

mutual
/-- **Every `tGeo acc t` leaf composite is differentiable** (given `acc` differentiable): each fanned
edge composes a differentiable `geoChartMapNorm` (or `id`) onto the accumulator. Mirrors `tGeo_coherence`.
The differentiability the chain-rule fold consumes at every leaf. -/
theorem tGeo_composite_differentiable (acc : Params M → Params M) (hacc : Differentiable ℝ acc) :
    ∀ t : ResolutionTree M, ∀ p ∈ ResolutionTree.leafPaths acc (tGeo acc t), Differentiable ℝ p.2
  | .leaf _ => by
      intro p hp
      rw [tGeo, ResolutionTree.leafPaths] at hp
      simp only [List.mem_singleton] at hp
      subst hp; exact hacc
  | .branch n edges => by
      intro p hp
      rw [tGeo, ResolutionTree.leafPaths] at hp
      exact tGeo_edges_composite_differentiable acc hacc n 0 edges p hp
/-- Companion of `tGeo_composite_differentiable` over an edge list. -/
theorem tGeo_edges_composite_differentiable (acc : Params M → Params M) (hacc : Differentiable ℝ acc)
    (n : StepData M) (offset : ℕ) :
    ∀ edges : List (Edge M),
      ∀ p ∈ ResolutionTree.edgesLeafPaths acc (fannedEdges acc n offset edges), Differentiable ℝ p.2
  | [] => by intro p hp; rw [fannedEdges] at hp; simp [ResolutionTree.edgesLeafPaths] at hp
  | .mk c s ch :: es => by
      intro p hp
      rw [fannedEdges, edgesLeafPaths_append, List.mem_append] at hp
      rcases hp with hp | hp
      · by_cases hz : dCenterOfEdge n (Edge.mk c s ch) = 0
        · rw [if_pos hz] at hp
          simp only [ResolutionTree.edgesLeafPaths, List.append_nil] at hp
          exact tGeo_composite_differentiable acc hacc ch p hp
        · rw [if_neg hz, edgesLeafPaths_mapMk, List.mem_flatMap] at hp
          obtain ⟨i, _, hp⟩ := hp
          exact tGeo_composite_differentiable _
            (hacc.comp (geoChartMapNorm_differentiable _)) ch p hp
      · exact tGeo_edges_composite_differentiable acc hacc n
          (offset + dCenterOfEdge n (Edge.mk c s ch)) es p hp
end

/-! ## Det-fold: materialize the per-leaf chart LIST, then the chain-rule fold -/

/-- `foldr (·∘·)` with a nonidentity base splits off the base on the right. -/
theorem foldr_comp_base (l : List (Params M → Params M)) (g : Params M → Params M) :
    l.foldr (· ∘ ·) g = l.foldr (· ∘ ·) id ∘ g := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [List.foldr_cons, ih]; rfl

/-- Appending a single map to a `foldr (·∘·) id` list composes it on the inner (right) end. -/
theorem foldr_comp_append_single (acc : List (Params M → Params M)) (ls : Params M → Params M) :
    (acc ++ [ls]).foldr (· ∘ ·) id = acc.foldr (· ∘ ·) id ∘ ls := by
  rw [List.foldr_append]
  exact foldr_comp_base acc _

mutual
/-- **The list-carrying `leafPaths`**: like `leafPaths` but accumulating the LIST of per-edge `localSub`s
(root→leaf), so `abs_det_fderiv_foldr_comp` can consume it. Its `foldr (·∘·) id` is the `leafPaths`
composite (`leafPathsList_coherence`). -/
def leafPathsList (acc : List (Params M → Params M)) :
    ResolutionTree M → List (LeafData M × List (Params M → Params M))
  | .leaf l => [(l, acc)]
  | .branch _ edges => edgesLeafPathsList acc edges
/-- Companion of `leafPathsList` over an edge list. -/
def edgesLeafPathsList (acc : List (Params M → Params M)) :
    List (Edge M) → List (LeafData M × List (Params M → Params M))
  | [] => []
  | .mk _ s c :: es => leafPathsList (acc ++ [s.localSub]) c ++ edgesLeafPathsList acc es
end

mutual
/-- **`leafPathsList` coherence with `leafPaths`**: folding each carried list recovers the `leafPaths`
composite (with `acc`'s fold as the outer prefix). -/
theorem leafPathsList_coherence (acc : List (Params M → Params M)) :
    ∀ t : ResolutionTree M,
      (leafPathsList acc t).map (fun p => (p.1, p.2.foldr (· ∘ ·) id))
        = ResolutionTree.leafPaths (acc.foldr (· ∘ ·) id) t
  | .leaf l => by simp [leafPathsList, ResolutionTree.leafPaths]
  | .branch n edges => by
      rw [leafPathsList, ResolutionTree.leafPaths]
      exact edgesLeafPathsList_coherence acc edges
/-- Companion of `leafPathsList_coherence` over an edge list. -/
theorem edgesLeafPathsList_coherence (acc : List (Params M → Params M)) :
    ∀ edges : List (Edge M),
      (edgesLeafPathsList acc edges).map (fun p => (p.1, p.2.foldr (· ∘ ·) id))
        = ResolutionTree.edgesLeafPaths (acc.foldr (· ∘ ·) id) edges
  | [] => by simp [edgesLeafPathsList, ResolutionTree.edgesLeafPaths]
  | .mk c s ch :: es => by
      rw [edgesLeafPathsList, ResolutionTree.edgesLeafPaths, List.map_append,
        leafPathsList_coherence, edgesLeafPathsList_coherence, foldr_comp_append_single]
end

/-- `edgesLeafPathsList` distributes over list append. -/
theorem edgesLeafPathsList_append (acc : List (Params M → Params M)) (l1 l2 : List (Edge M)) :
    edgesLeafPathsList acc (l1 ++ l2)
      = edgesLeafPathsList acc l1 ++ edgesLeafPathsList acc l2 := by
  induction l1 with
  | nil => simp [edgesLeafPathsList]
  | cons e es ih =>
      obtain ⟨c, s, ch⟩ := e
      simp only [List.cons_append, edgesLeafPathsList, ih, List.append_assoc]

/-- `edgesLeafPathsList` of a `.mk`-built mapped edge-list is the `flatMap` of the per-element list. -/
theorem edgesLeafPathsList_mapMk {α : Type*} (acc : List (Params M → Params M)) (g : α → StepCase)
    (sub : α → ChartSubst M) (chi : α → ResolutionTree M) (l : List α) :
    edgesLeafPathsList acc (l.map (fun a => Edge.mk (g a) (sub a) (chi a)))
      = l.flatMap (fun a => leafPathsList (acc ++ [(sub a).localSub]) (chi a)) := by
  induction l with
  | nil => simp [edgesLeafPathsList]
  | cons a as ih =>
      simp only [List.map_cons, edgesLeafPathsList, ih, List.flatMap_cons]

mutual
/-- **Every carried `leafPathsList` chart (over `tGeo`) is differentiable** — each accumulated element is
a `geoChartMapNorm` (or `id`); the `abs_det_fderiv_foldr_comp` hypothesis for the materialized list. -/
theorem leafPathsList_tGeo_diff (acc : List (Params M → Params M)) (accf : Params M → Params M)
    (hacc : ∀ f ∈ acc, Differentiable ℝ f) :
    ∀ t : ResolutionTree M, ∀ p ∈ leafPathsList acc (tGeo accf t), ∀ f ∈ p.2, Differentiable ℝ f
  | .leaf _ => by
      intro p hp
      rw [tGeo, leafPathsList] at hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact hacc
  | .branch n edges => by
      intro p hp
      rw [tGeo, leafPathsList] at hp
      exact leafPathsList_edges_tGeo_diff acc accf hacc n 0 edges p hp
/-- Companion of `leafPathsList_tGeo_diff` over an edge list. -/
theorem leafPathsList_edges_tGeo_diff (acc : List (Params M → Params M)) (accf : Params M → Params M)
    (hacc : ∀ f ∈ acc, Differentiable ℝ f) (n : StepData M) (offset : ℕ) :
    ∀ edges : List (Edge M),
      ∀ p ∈ edgesLeafPathsList acc (fannedEdges accf n offset edges), ∀ f ∈ p.2, Differentiable ℝ f
  | [] => by intro p hp; rw [fannedEdges] at hp; simp [edgesLeafPathsList] at hp
  | .mk c s ch :: es => by
      intro p hp
      rw [fannedEdges, edgesLeafPathsList_append, List.mem_append] at hp
      rcases hp with hp | hp
      · by_cases hz : dCenterOfEdge n (Edge.mk c s ch) = 0
        · rw [if_pos hz] at hp
          simp only [edgesLeafPathsList, List.append_nil] at hp
          refine leafPathsList_tGeo_diff (acc ++ [id]) accf (fun f hf => ?_) ch p hp
          rcases List.mem_append.mp hf with h | h
          · exact hacc f h
          · simp only [List.mem_singleton] at h; subst h; exact differentiable_id
        · rw [if_neg hz, edgesLeafPathsList_mapMk, List.mem_flatMap] at hp
          obtain ⟨i, _, hp⟩ := hp
          refine leafPathsList_tGeo_diff _ _ (fun f hf => ?_) ch p hp
          rcases List.mem_append.mp hf with h | h
          · exact hacc f h
          · simp only [List.mem_singleton] at h; subst h; exact geoChartMapNorm_differentiable _
      · exact leafPathsList_edges_tGeo_diff acc accf hacc n
          (offset + dCenterOfEdge n (Edge.mk c s ch)) es p hp
end

/-- **The det-fold** (the bridge's payoff): for every materialized leaf `(c, cs)` of the built atlas,
`|det D(c.chartMap) w|` is the intermediate-point per-factor product `foldrCompAbsDet cs w` — i.e. the
chart determinant equals the chain-rule fold of its path charts. Combines `leafPathsList_coherence` +
`tGeo_coherence` (`c.chartMap = foldr cs`), `leafPathsList_tGeo_diff` (each `cs` chart differentiable),
and the banked `abs_det_fderiv_foldr_comp`. The regrouping cocycle then rewrites the RHS onto the leaf
ledger `∏_k |z_{c.divCoord k}|^{c.divExp k − 1}`. -/
theorem tGeo_absdet_foldrList (t : ResolutionTree M) (w : Params M)
    (p : LeafData M × List (Params M → Params M)) (hp : p ∈ leafPathsList [] (tGeo id t)) :
    |(fderiv ℝ p.1.chartMap w).det| = foldrCompAbsDet p.2 w := by
  have hmap : (p.1, p.2.foldr (· ∘ ·) id) ∈ ResolutionTree.leafPaths id (tGeo id t) := by
    have hm : (p.1, p.2.foldr (· ∘ ·) id)
        ∈ (leafPathsList ([] : List (Params M → Params M)) (tGeo id t)).map
            (fun q => (q.1, q.2.foldr (· ∘ ·) id)) :=
      List.mem_map.mpr ⟨p, hp, rfl⟩
    rwa [leafPathsList_coherence, List.foldr_nil] at hm
  have hchart : p.1.chartMap = p.2.foldr (· ∘ ·) id := tGeo_coherence id t _ hmap
  have hdiff : ∀ f ∈ p.2, Differentiable ℝ f :=
    leafPathsList_tGeo_diff [] id (by intro g hg; simp at hg) t p hp
  rw [hchart, abs_det_fderiv_foldr_comp p.2 hdiff w]

/-- **Every `geoAtlas` leaf is a materialized `leafPathsList` leaf** (`geoAtlas t = leaves (tGeo id t) =
(leafPathsList [] (tGeo id t)).map Prod.fst`, via `leafPaths_mapFst` + `leafPathsList_coherence`). The
bridge that carries the det-fold onto the atlas pieces the headline quantifies over. -/
theorem geoAtlas_mem_leafPathsList (t : ResolutionTree M) (c : LeafData M) (hc : c ∈ geoAtlas t) :
    ∃ cs : List (Params M → Params M), (c, cs) ∈ leafPathsList [] (tGeo id t) := by
  have h1 : (leafPathsList ([] : List (Params M → Params M)) (tGeo id t)).map Prod.fst
      = ResolutionTree.leaves (tGeo id t) := by
    have hco := leafPathsList_coherence ([] : List (Params M → Params M)) (tGeo id t)
    rw [List.foldr_nil] at hco
    rw [← leafPaths_mapFst id (tGeo id t), ← hco, List.map_map]
    rfl
  rw [geoAtlas, ← h1, List.mem_map] at hc
  obtain ⟨p, hp, hpc⟩ := hc
  exact ⟨p.2, by rw [← hpc]; exact hp⟩

/-- **The det-fold over the atlas** (headline-facing): for every `geoAtlas` leaf `c`, its chart
determinant equals the intermediate-point chain-rule fold of a materialized path-chart list. The
remaining regrouping cocycle rewrites `foldrCompAbsDet cs` onto the leaf ledger. -/
theorem geoAtlas_absdet_foldr (t : ResolutionTree M) (c : LeafData M) (hc : c ∈ geoAtlas t)
    (w : Params M) :
    ∃ cs : List (Params M → Params M), (c, cs) ∈ leafPathsList [] (tGeo id t) ∧
      |(fderiv ℝ c.chartMap w).det| = foldrCompAbsDet cs w := by
  obtain ⟨cs, hcs⟩ := geoAtlas_mem_leafPathsList t c hc
  exact ⟨cs, hcs, tGeo_absdet_foldrList t w (c, cs) hcs⟩

/-! ## Per-edge atom in `geoChartMapNorm` form (the `foldrCompAbsDet` factors) -/

/-- **The per-edge det of the normalized chart** (on-cone): `|det D(geoChartMapNorm (fun _ => id) g) y|
= |z_{diagTargetOf}(y)|^{dCN − 1}` — the banked per-edge atom read through the diagonal-normalizing swap
(`geoChartMap_swap_fderiv_det` + the `β∘S` reduction). Each `foldrCompAbsDet` factor is this. -/
theorem geoChartMapNorm_fderiv_det (g : GeoChart M) (w : Params M)
    (hd : dCenterOfNode M g.node ≤ flatDim M) (hp : g.pivot < dCenterOfNode M g.node) :
    |(fderiv ℝ (geoChartMapNorm (fun _ => id) g) w).det|
      = |paramsEquivFlat M w (diagTargetOf M g.node g.edge (by omega))|
          ^ (dCenterOfNode M g.node - 1) := by
  have hfun : geoChartMapNorm (fun _ => id) g
      = geoChartMap (dCenterOfNode M) (qNodeOf M) g ∘
          ⇑(flatSwapCLE M (cNodeOf M g.node hd (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node)))
            (diagTargetOf M g.node g.edge (by omega))) := by
    funext x; rw [geoChartMapNorm_apply_oncone g x hd hp]; rfl
  rw [hfun, geoChartMap_swap_fderiv_det g w hd hp]

/-- **The per-edge det off-cone / out-of-range**: `geoChartMapNorm (fun _ => id) g = id`, so its
Fréchet-derivative determinant has modulus `1` (the `id`-passthrough / rollover factor). -/
theorem geoChartMapNorm_fderiv_det_offcone (g : GeoChart M) (w : Params M)
    (h : ¬ (dCenterOfNode M g.node ≤ flatDim M ∧ g.pivot < dCenterOfNode M g.node)) :
    |(fderiv ℝ (geoChartMapNorm (fun _ => id) g) w).det| = 1 := by
  have hid : geoChartMapNorm (fun _ => id) g = id := by
    unfold geoChartMapNorm
    split_ifs with hd hp
    · exact absurd ⟨hd, hp⟩ h
    · rfl
    · rfl
  rw [hid, fderiv_id]
  rw [show (ContinuousLinearMap.id ℝ (Params M)).det
      = LinearMap.det (ContinuousLinearMap.id ℝ (Params M)).toLinearMap from rfl]
  simp [LinearMap.det_id]

/-! ## The one-step cocycle (determinant half) — cert §2 -/

/-- **Chain-rule determinant split** on `Params M`: `|det D(f ∘ g) w| = |det Df (g w)| · |det Dg w|`
for differentiable `f`, `g`. The general (no-gauge) form of `abs_det_fderiv_comp_det_one_gauge`. -/
theorem abs_det_fderiv_comp (f g : Params M → Params M) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (w : Params M) :
    |(fderiv ℝ (f ∘ g) w).det| = |(fderiv ℝ f (g w)).det| * |(fderiv ℝ g w).det| := by
  have hgw : HasFDerivAt g (fderiv ℝ g w) w := (hg w).hasFDerivAt
  have hfgw : HasFDerivAt f (fderiv ℝ f (g w)) (g w) := (hf (g w)).hasFDerivAt
  have hcomp : HasFDerivAt (f ∘ g) ((fderiv ℝ f (g w)).comp (fderiv ℝ g w)) w := hfgw.comp w hgw
  rw [hcomp.fderiv, clm_det_comp, abs_mul]

/-- **The one-step cocycle** (cert §2, determinant half): adding an on-cone edge chart `B =
geoChartMapNorm (fun _ => id) g` at the innermost position to an accumulated fold `acc` multiplies the
Jacobian modulus by the edge atom `|z_{diagTargetOf}(w)|^{dCN−1}` read at the SOURCE `w`, times `acc`'s
Jacobian modulus read at the INTERMEDIATE point `B w`. The ledger-threading of the intermediate factor
`|det D acc (B w)|` (the §3 per-case work) is what supplies the case-1(2) inheritance locally. -/
theorem geoChartMapNorm_cocycle_step (acc : Params M → Params M) (hacc : Differentiable ℝ acc)
    (g : GeoChart M) (w : Params M) (hd : dCenterOfNode M g.node ≤ flatDim M)
    (hp : g.pivot < dCenterOfNode M g.node) :
    |(fderiv ℝ (acc ∘ geoChartMapNorm (fun _ => id) g) w).det|
      = |(fderiv ℝ acc (geoChartMapNorm (fun _ => id) g w)).det|
        * |paramsEquivFlat M w (diagTargetOf M g.node g.edge (by omega))|
            ^ (dCenterOfNode M g.node - 1) := by
  rw [abs_det_fderiv_comp acc _ hacc (geoChartMapNorm_differentiable g) w,
    geoChartMapNorm_fderiv_det g w hd hp]

/-! ## The full-ledger monomial + the terminal bridge to the analytic (`leafOfState`) product -/

/-- **The full-ledger monomial** `L(s)(w) := ∏_{k : s.numDiv} |z_{birthFlatCoord s k}(w)|^{s.divExp k − 1}`
— over ALL divisors of `s` (not just the t̃=0 analytic ones). This is the cocycle invariant's RHS
(`Inv(acc, s) : |det D acc w| = ledgerMonomial s w`); the fold covers every full-divisor birth/merge, so
it is what the Jacobian equals. -/
noncomputable def ledgerMonomial (M : Fin (L + 1) → ℕ) (s : ConState L) (h : 0 < flatDim M)
    (w : Params M) : ℝ :=
  ∏ k : Fin s.numDiv, |paramsEquivFlat M w (birthFlatCoord M s k h)| ^ (s.divExp k - 1)

/-- **`birthFlatCoord` depends only on the birth-corner value** — equal `divBirthCoord` entries give
equal flat coordinates (the ledger-delta lemmas transport it across `snoc`/`update`/`rollover`). -/
theorem birthFlatCoord_congr (M : Fin (L + 1) → ℕ) {s s' : ConState L} (h : 0 < flatDim M)
    {k : Fin s.numDiv} {k' : Fin s'.numDiv} (heq : s'.divBirthCoord k' = s.divBirthCoord k) :
    birthFlatCoord M s' k' h = birthFlatCoord M s k h := by
  unfold birthFlatCoord; rw [heq]

/-- **Rollover is ledger-neutral**: `stepRollover` carries `numDiv`/`divExp`/`divBirthCoord`, so the
full-ledger monomial is unchanged. -/
theorem ledgerMonomial_stepRollover (M : Fin (L + 1) → ℕ) (s : ConState L) (h : 0 < flatDim M)
    (w : Params M) : ledgerMonomial M s.stepRollover h w = ledgerMonomial M s h w := rfl

/-- **The birth ledger-delta** (`case-2` / `case-1(2)` at the ConState level): `stepAppendAdvance e t₀`
appends one divisor of exponent `e` at the fresh corner, so the full-ledger monomial gains exactly the
factor `|z_{fresh}(w)|^{e−1}` (carried divisors unchanged, `snoc_castSucc`). -/
theorem ledgerMonomial_stepAppendAdvance (M : Fin (L + 1) → ℕ) (s : ConState L) (h : 0 < flatDim M)
    (e : ℕ) (t₀ : Fin L → ℕ) (w : Params M) :
    ledgerMonomial M (s.stepAppendAdvance e t₀) h w
      = ledgerMonomial M s h w
        * |paramsEquivFlat M w (birthFlatCoord M (s.stepAppendAdvance e t₀) (Fin.last s.numDiv) h)|
            ^ (e - 1) := by
  rw [ledgerMonomial]
  show (∏ k : Fin (s.numDiv + 1),
      |paramsEquivFlat M w (birthFlatCoord M (s.stepAppendAdvance e t₀) k h)|
        ^ ((s.stepAppendAdvance e t₀).divExp k - 1)) = _
  rw [Fin.prod_univ_castSucc, ledgerMonomial]
  congr 1
  · refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [birthFlatCoord_congr M h
        (show (s.stepAppendAdvance e t₀).divBirthCoord (Fin.castSucc k) = s.divBirthCoord k by
          simp [ConState.stepAppendAdvance])]
    have hexp : (s.stepAppendAdvance e t₀).divExp (Fin.castSucc k) = s.divExp k := by
      simp [ConState.stepAppendAdvance]
    rw [hexp]
  · have hexp : (s.stepAppendAdvance e t₀).divExp (Fin.last s.numDiv) = e := by
      simp [ConState.stepAppendAdvance]
    rw [hexp]

/-- **The geometric spectator step** (cert §3, case-2 / the non-`mergeIdx` divisors of case-1): if
every divisor's diagonal `birthFlatCoord s k` is a SPECTATOR of the new chart `B = geoChartMapNorm g`
(not a center cell of `B`, and not `B`'s diagonal target), then the incoming ledger pulls back
UNCHANGED: `ledgerMonomial s (B w) = ledgerMonomial s w`. Via the (α) `geoChartMap_flat_spectator` +
the swap relabel `flatSwapCLE_apply_flat` (the swap fixes a cell distinct from both its targets). The
two disjointness hypotheses are the construction-freshness content, discharged per case from
`DivBirthInv` + `realCNode`/`resBlockCenterIndices` structure (the isolated crux of the geometric half). -/
theorem ledgerMonomial_comp_spectator (M : Fin (L + 1) → ℕ) (s : ConState L) (h : 0 < flatDim M)
    (g : GeoChart M) (w : Params M) (hd : dCenterOfNode M g.node ≤ flatDim M)
    (hp : g.pivot < dCenterOfNode M g.node)
    (hspec : ∀ (k : Fin s.numDiv) (i : Fin (dCenterOfNode M g.node)),
      cNodeOf M g.node hd i ≠ birthFlatCoord M s k h)
    (hdt : ∀ k : Fin s.numDiv,
      birthFlatCoord M s k h ≠ diagTargetOf M g.node g.edge (by omega)) :
    ledgerMonomial M s h (geoChartMapNorm (fun _ => id) g w) = ledgerMonomial M s h w := by
  rw [ledgerMonomial, ledgerMonomial]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  congr 2
  rw [geoChartMapNorm_apply_oncone g w hd hp,
    geoChartMap_flat_spectator g _ hd hp (birthFlatCoord M s k h) (fun i => hspec k i),
    flatSwapCLE_apply_flat,
    Equiv.swap_apply_of_ne_of_ne (hspec k ⟨g.pivot, hp⟩).symm (hdt k)]

/-- **The weak no-stranded fact** (team-lead sharpening, pnp-fold adjudicating): a stranded (t̃ ≠ 0)
divisor has exponent `1`, so its ledger factor `|z|^{1−1} = 1` is harmless. Threaded as an open
hypothesis until pnp-fold's dichotomy (strong all-t̃=0 / this weak form / false-with-witness) returns. -/
def WeakNoStrand {L : ℕ} (s : ConState L) : Prop :=
  ∀ k : Fin s.numDiv, s.divTilde k ≠ 0 → s.divExp k = 1

/-- **The terminal bridge**: at a terminal state `s`, the full-ledger monomial equals the ANALYTIC
`leafOfState` product (headline RHS) — the stranded (t̃ ≠ 0) divisors drop out because `WeakNoStrand`
gives them exponent `1` (factor `|z|^0 = 1`). Reindexes the t̃=0 sublist (`t0Indices`) to `Finset.univ`
via `List.prod_toFinset` + `Finset.prod_subset`. This is the ONLY place the no-stranded gap enters. -/
theorem leafOfState_prod_eq_ledgerMonomial (M : Fin (L + 1) → ℕ) (s : ConState L) (h : 0 < flatDim M)
    (w : Params M) (hweak : WeakNoStrand s) :
    (∏ k : Fin (leafOfState M s).numDiv,
        |paramsEquivFlat M w ((leafOfState M s).divCoord k)| ^ ((leafOfState M s).divExp k - 1))
      = ledgerMonomial M s h w := by
  have hnodup : (t0Indices s).Nodup :=
    (List.nodup_finRange s.numDiv).filter (fun k => decide (s.divTilde k = 0))
  rw [ledgerMonomial, leafOfState, dif_pos h]
  simp only [List.get_eq_getElem]
  rw [Fin.prod_univ_fun_getElem (t0Indices s)
        (fun k => |paramsEquivFlat M w (birthFlatCoord M s k h)| ^ (s.divExp k - 1)),
    ← List.prod_toFinset _ hnodup]
  have htf : (t0Indices s).toFinset = Finset.univ.filter (fun k => s.divTilde k = 0) := by
    ext k
    simp only [List.mem_toFinset, mem_t0Indices, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [htf]
  refine Finset.prod_subset (Finset.filter_subset _ _) (fun k _ hk => ?_)
  have hne : s.divTilde k ≠ 0 := fun h0 => hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, h0⟩)
  rw [hweak k hne]; simp

/-- **Base of the cocycle**: at `conRoot` (`numDiv = 0`) the full-ledger monomial is the empty product
`1`. So `Inv(id, conRoot)` is `|det D id w| = 1`. -/
theorem ledgerMonomial_conRoot (M : Fin (L + 1) → ℕ) (h : 0 < flatDim M) (w : Params M) :
    ledgerMonomial M (conRoot : ConState L) h w = 1 := by
  simp [ledgerMonomial, conRoot]

/-- **The weak no-stranded fact, expressed on a leaf's FULL ledger fields** (so it threads through the
`leaves` of `buildTree` without a separate reachability predicate). For `leafOfState s` this is
defeq to `WeakNoStrand s`. -/
def WeakNoStrandLeaf {L : ℕ} {M : Fin (L + 1) → ℕ} (l : LeafData M) : Prop :=
  ∀ k : Fin l.fullNumDiv, tildeOf (l.fullDivProfile k) ≠ 0 → l.fullDivExp k = 1

/-- **The fold-Jacobian cocycle** (the WF walk, `Inv(acc, s)` threaded down `buildTree`). Given the
incoming full-ledger invariant `|det D acc w| = ledgerMonomial s w`, `DivBirthInv M s`, and the weak
no-stranded fact on the terminal leaves, every geometric atlas leaf of the subtree from `s` has the
analytic headline determinant. The headline is the `s = conRoot`, `acc = id` instance. -/
theorem geoAtlas_cocycle (h : 0 < flatDim M) :
    ∀ (s : ConState L), DivBirthInv M s →
      (∀ l ∈ ResolutionTree.leaves (buildTree M (conOracle M) s), WeakNoStrandLeaf l) →
      ∀ (acc : Params M → Params M), Differentiable ℝ acc →
        (∀ w, |(fderiv ℝ acc w).det| = ledgerMonomial M s h w) →
        ∀ p ∈ ResolutionTree.leaves (tGeo acc (buildTree M (conOracle M) s)), ∀ w,
          |(fderiv ℝ p.chartMap w).det|
            = ∏ k : Fin p.numDiv, |paramsEquivFlat M w (p.divCoord k)| ^ (p.divExp k - 1) := by
  intro s
  induction s using (conRel_wf M).induction with
  | _ s ih =>
    intro inv hweak acc haccdiff haccdet p hp w
    cases hoc : conOracle M s with
    | terminal l' hleaf =>
      have hbt : buildTree M (conOracle M) s = ResolutionTree.leaf (leafOfState M s) := by
        rw [buildTree_terminal M (conOracle M) s l' hleaf hoc, conOracle_terminal_leaf s hoc]
      have hmem : leafOfState M s ∈ ResolutionTree.leaves (buildTree M (conOracle M) s) := by
        rw [hbt]; exact List.mem_singleton.mpr rfl
      have hws : WeakNoStrand s := by
        intro k hk
        have hwl := hweak (leafOfState M s) hmem
        unfold WeakNoStrandLeaf at hwl
        rw [leafOfState, dif_pos h] at hwl
        exact hwl k hk
      rw [hbt, tGeo] at hp
      simp only [ResolutionTree.leaves, List.mem_singleton] at hp
      subst hp
      show |(fderiv ℝ acc w).det|
        = ∏ k : Fin (leafOfState M s).numDiv,
            |paramsEquivFlat M w ((leafOfState M s).divCoord k)| ^ ((leafOfState M s).divExp k - 1)
      rw [haccdet w, ← leafOfState_prod_eq_ledgerMonomial M s h w hws]
    | step node children hnode hlayer hstep =>
      sorry

end DLNFibre.DLN.RLCT.Engine
