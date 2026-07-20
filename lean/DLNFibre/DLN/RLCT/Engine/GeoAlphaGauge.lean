-- ⛔ RETIRED CHART ROUTE — DO NOT FILL THE `sorry`s IN THIS MODULE. ⛔
-- This is the α source-gauge of the abandoned CHART route. Its `LeafPullback` / value hole
-- (`leafDiagFrob_geoAtlasNorm`, ~:667) is CATEGORY-FALSE for ALL det-1 charts (no chart bounds the
-- residual core; diagonalising a generic product needs a det-0 projection). It looks fillable and is
-- not — it drove the second expedition drift. See `expeditions/.../charter.md` §3. The replacement is
-- charter Object B (the IDEAL-level resolution `⟨∏C⟩ = ⟨diag bᵢ⟩`); reusable tree/det pieces are
-- salvaged into B deliberately, NEVER by closing a chart hole. Off the deliverable path (nothing the
-- proven headline needs imports this).
import DLNFibre.DLN.RLCT.Engine.GeoChart
import DLNFibre.DLN.RLCT.Engine.EngineDefs
import DLNFibre.DLN.RLCT.Engine.GeoJacobianFold

/-!
# `DLNFibre.DLN.RLCT.Engine.GeoAlphaGauge` — the α source-gauge + LeafPullback (loss-t15, PHASE 1)

**STATEMENT-FIRST SKELETON (team-lead gated, `design-alpha-gauge-t15.md`).** This module
instantiates the parametric det-1 source-gauge SLOT of `geoChartMapNorm` (`GeoChart.lean`) with the
incidence/Q,P Schur shear `α` and states the three PHASE-1 obligations (α det-1, the srcBox
transform, the `LeafPullback` squeeze over the α-normalized atlas). All three proofs are the `sorry`
frontier; PHASE 2 fills det-1 + srcBox (banked-atom-shaped), PHASE 3 the squeeze.

ADDITIVE ONLY (coordination note): the α-atlas is a NEW definition (`geoAtlasNorm`, a
gauge-parametric copy of `tGeo`/`fannedEdges`); the existing `geoAtlas` (gauge = `fun _ => id`) is
untouched, so the
landed cover/fold lanes (t10/t14) keep consuming it. The transfer lemmas
(`geoAtlas = geoAtlasNorm (fun _ => id)`, cover image-invariance, fold det-1-transparency) come
AFTER both lanes land.

* `flatElemShear a b c` — the banked `elemShear` (`ShearReconcile`) conjugated by `paramsEquivFlat`:
  acts as `x_a ↦ x_a − x_b·x_c` on the flat weight coordinates. Since `qNodeOf`/`flatSwapCLE` are
  coordinate permutations, this flat shear acts through them as the center-frame Schur the cert
  needs.
* `alphaGauge` — the per-edge source gauge: `id` on case-1(1)/rollover (`α_u = refl`); the interior
  residual-block Schur fold on case-1(2)/case-2 (`α_d`, `cert-psi-mix` §R-b).
* `geoAtlasNorm gauge t` — the gauge-parametric flat virtual-leaf atlas; the loss atlas is
  `geoAtlasNorm alphaGauge (buildTree …)`.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open MeasureTheory Set
open scoped BigOperators

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-! ## The flat Schur atom -/

/-- **The flat elementary Schur shear** on `Params M`: `elemShear a b c` (banked, `ShearReconcile`)
conjugated by `paramsEquivFlat` — reads `w` in flat coordinates, shifts `x_a ↦ x_a − x_b·x_c`,
writes back. A polynomial det-1 homeomorphism (PHASE-2 lemmas). -/
noncomputable def flatElemShear (a b c : Fin (flatDim M)) : Params M → Params M :=
  fun w => (paramsEquivFlat M).symm (elemShear a b c (paramsEquivFlat M w))

/-- The CLE inverse has the same underlying function as the measurable-equiv inverse (both are the
unique inverse of the shared forward flattening). -/
theorem paramsEquivFlatCLE_symm_coe (H : Fin (L + 1) → ℕ) :
    ⇑(paramsEquivFlatCLE H).symm = ⇑(paramsEquivFlat H).symm := by
  funext x
  apply (paramsEquivFlat H).injective
  rw [MeasurableEquiv.apply_symm_apply, ← paramsEquivFlatCLE_coe,
    ContinuousLinearEquiv.apply_symm_apply]

/-- **The flat read of `flatElemShear`**: `z_·(flatElemShear a b c w) = elemShear a b c (z_·(w))`
— the shear acts as `x_a ↦ x_a − x_b·x_c` on the flat coordinates. -/
theorem flatElemShear_flat_read (a b c : Fin (flatDim M)) (w : Params M) :
    paramsEquivFlat M (flatElemShear a b c w) = elemShear a b c (paramsEquivFlat M w) := by
  rw [flatElemShear, MeasurableEquiv.apply_symm_apply]

/-- `(paramsEquivFlat M).symm` has constant fderiv the inverse reindex CLM (it is ℝ-linear). -/
theorem hasFDerivAt_paramsEquivFlat_symm (x : Fin (flatDim M) → ℝ) :
    HasFDerivAt (⇑(paramsEquivFlat M).symm)
      ((paramsEquivFlatCLE M).symm.toContinuousLinearMap) x := by
  have h : HasFDerivAt (⇑(paramsEquivFlatCLE M).symm)
      ((paramsEquivFlatCLE M).symm.toContinuousLinearMap) x :=
    (paramsEquivFlatCLE M).symm.hasFDerivAt
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with y
  rw [paramsEquivFlatCLE_symm_coe]

/-- **`flatElemShear` is Fréchet-differentiable** with derivative the CLE-conjugated
`elemShearDeriv` — chain rule over `E.symm ∘ elemShear ∘ E` (`E = paramsEquivFlatCLE`, linear). -/
theorem flatElemShear_hasFDerivAt (a b c : Fin (flatDim M)) (w : Params M) :
    HasFDerivAt (flatElemShear a b c)
      ((paramsEquivFlatCLE M).symm.toContinuousLinearMap.comp
        ((elemShearDeriv a b c (paramsEquivFlat M w)).comp
          (paramsEquivFlatCLE M).toContinuousLinearMap)) w := by
  have hInner : HasFDerivAt (⇑(paramsEquivFlat M))
      ((paramsEquivFlatCLE M).toContinuousLinearMap) w := hasFDerivAt_paramsEquivFlat M w
  have hMid : HasFDerivAt (elemShear a b c) (elemShearDeriv a b c (paramsEquivFlat M w))
      (paramsEquivFlat M w) := elemShear_hasFDerivAt a b c (paramsEquivFlat M w)
  have hOuter : HasFDerivAt (⇑(paramsEquivFlat M).symm)
      ((paramsEquivFlatCLE M).symm.toContinuousLinearMap)
      (elemShear a b c (paramsEquivFlat M w)) := hasFDerivAt_paramsEquivFlat_symm _
  have h1 : HasFDerivAt (fun x => elemShear a b c (paramsEquivFlat M x))
      ((elemShearDeriv a b c (paramsEquivFlat M w)).comp
        (paramsEquivFlatCLE M).toContinuousLinearMap) w := hMid.comp w hInner
  exact hOuter.comp w h1

/-- **`flatElemShear` is differentiable everywhere**. -/
theorem flatElemShear_differentiable (a b c : Fin (flatDim M)) :
    Differentiable ℝ (flatElemShear a b c) :=
  fun w => (flatElemShear_hasFDerivAt a b c w).differentiableAt

/-- **`flatElemShear` is det-1** (given the `elemShear` side conditions `a ≠ b`, `a ≠ c`): the CLE
conjugation preserves the determinant (`LinearMap.det_conj`), and `elemShearDeriv_det = 1`. -/
theorem flatElemShear_abs_det_one (a b c : Fin (flatDim M)) (hab : a ≠ b) (hac : a ≠ c)
    (w : Params M) : |(fderiv ℝ (flatElemShear a b c) w).det| = 1 := by
  rw [(flatElemShear_hasFDerivAt a b c w).fderiv]
  have hconj : ((paramsEquivFlatCLE M).symm.toContinuousLinearMap.comp
        ((elemShearDeriv a b c (paramsEquivFlat M w)).comp
          (paramsEquivFlatCLE M).toContinuousLinearMap)).det
      = (elemShearDeriv a b c (paramsEquivFlat M w)).det := by
    change LinearMap.det ((paramsEquivFlatCLE M).symm.toContinuousLinearMap.comp
        ((elemShearDeriv a b c (paramsEquivFlat M w)).comp
          (paramsEquivFlatCLE M).toContinuousLinearMap)).toLinearMap = _
    have heq : ((paramsEquivFlatCLE M).symm.toContinuousLinearMap.comp
          ((elemShearDeriv a b c (paramsEquivFlat M w)).comp
            (paramsEquivFlatCLE M).toContinuousLinearMap)).toLinearMap
        = ((paramsEquivFlatCLE M).symm.toLinearEquiv : (Fin (flatDim M) → ℝ) →ₗ[ℝ] Params M) ∘ₗ
            (elemShearDeriv a b c (paramsEquivFlat M w)).toLinearMap ∘ₗ
            ((paramsEquivFlatCLE M).symm.toLinearEquiv.symm :
              Params M →ₗ[ℝ] (Fin (flatDim M) → ℝ)) :=
      rfl
    rw [heq, LinearMap.det_conj (elemShearDeriv a b c (paramsEquivFlat M w)).toLinearMap
      (paramsEquivFlatCLE M).symm.toLinearEquiv]
  rw [hconj, elemShearDeriv_det a b c hab hac (paramsEquivFlat M w), abs_one]

/-- **The interior residual cells** of a d-family blow-up at `node` with block `rows × cols`: the
triples `(a, b, c) = ((i,j), (i,piv), (piv,j))` in flat coordinates, `piv = (J,J)` the diagonal
pivot (`= diagTargetOf`), `(i,j)` over the interior sub-block `i,j > J`. `α_d` clears each such cell
via `r_{ij} ↦ r_{ij} − r_{i,piv}·r_{piv,j}`. Off the reachable cone (guard false) the list is empty
(the chart is `id` there anyway). The interior condition `i,j > J` gives `a ≠ b`, `a ≠ c` (the
`elemShear` side conditions) and makes the cells disjoint from the pivot row/col — so the shears are
independent (each touches a distinct `a`, reads only pivot-row/col `b,c`). -/
noncomputable def schurCells (node : StepData M) (rows cols : ℕ) :
    List (Fin (flatDim M) × Fin (flatDim M) × Fin (flatDim M)) :=
  if h : ∃ hs : node.layer < L,
      node.cleared + rows ≤ M (⟨node.layer, hs⟩ : Fin L).castSucc ∧
      node.cleared + cols ≤ M (⟨node.layer, hs⟩ : Fin L).succ then
    (List.finRange (rows - 1)).flatMap fun (i' : Fin (rows - 1)) =>
      (List.finRange (cols - 1)).map fun (j' : Fin (cols - 1)) =>
        (flatCoordOf M ⟨node.layer, h.choose⟩
            ⟨node.cleared + 1 + (i' : ℕ), by have := i'.isLt; have := h.choose_spec.1; omega⟩
            ⟨node.cleared + 1 + (j' : ℕ), by have := j'.isLt; have := h.choose_spec.2; omega⟩,
          flatCoordOf M ⟨node.layer, h.choose⟩
            ⟨node.cleared + 1 + (i' : ℕ), by have := i'.isLt; have := h.choose_spec.1; omega⟩
            ⟨node.cleared, by have := j'.isLt; have := h.choose_spec.2; omega⟩,
          flatCoordOf M ⟨node.layer, h.choose⟩
            ⟨node.cleared, by have := i'.isLt; have := h.choose_spec.1; omega⟩
            ⟨node.cleared + 1 + (j' : ℕ), by have := j'.isLt; have := h.choose_spec.2; omega⟩)
  else []

/-- The per-cell shear maps of a d-family blow-up (each an interior-cell `flatElemShear`). -/
noncomputable def schurMaps (node : StepData M) (rows cols : ℕ) : List (Params M → Params M) :=
  (schurCells node rows cols).map fun abc => flatElemShear abc.1 abc.2.1 abc.2.2

/-- **The interior-block Schur fold** (`α_d`): compose `flatElemShear` over `schurCells`. -/
noncomputable def residualSchurShear (node : StepData M) (rows cols : ℕ) : Params M → Params M :=
  (schurMaps node rows cols).foldr (· ∘ ·) id

/-- **The interior cells are valid `elemShear` triples**: `a ≠ b` and `a ≠ c` — the interior cell
`(i,j)` (`i,j > J`) differs from the pivot column `(i,J)` in the column and from the pivot row
`(J,j)` in the row (`flatCoordOf` injective). -/
theorem schurCells_ne (node : StepData M) (rows cols : ℕ) :
    ∀ abc ∈ schurCells node rows cols, abc.1 ≠ abc.2.1 ∧ abc.1 ≠ abc.2.2 := by
  intro abc hmem
  rw [schurCells] at hmem
  split at hmem
  · rw [List.mem_flatMap] at hmem
    obtain ⟨i', _, hmem⟩ := hmem
    rw [List.mem_map] at hmem
    obtain ⟨j', _, rfl⟩ := hmem
    refine ⟨fun heq => ?_, fun heq => ?_⟩
    · obtain ⟨_, hj⟩ := flatCoordOf_injective M _ heq
      rw [Fin.mk.injEq] at hj; omega
    · obtain ⟨hi, _⟩ := flatCoordOf_injective M _ heq
      rw [Fin.mk.injEq] at hi; omega
  · exact (List.not_mem_nil hmem).elim

/-- **The pivot row/col coordinates are never an interior `a`** (cross-cell): every cell's `b`
(pivot column, `col = J`) and `c` (pivot row, `row = J`) differs from every cell's `a` (interior,
`row,col > J`). So the pivot row/col coordinates pass through the whole fold unchanged. -/
theorem schurCells_snd_ne (node : StepData M) (rows cols : ℕ) :
    ∀ abc ∈ schurCells node rows cols, ∀ abc' ∈ schurCells node rows cols,
      abc'.1 ≠ abc.2.1 ∧ abc'.1 ≠ abc.2.2 := by
  intro abc hmem abc' hmem'
  rw [schurCells] at hmem hmem'
  by_cases hguard : ∃ hs : node.layer < L,
      node.cleared + rows ≤ M (⟨node.layer, hs⟩ : Fin L).castSucc ∧
      node.cleared + cols ≤ M (⟨node.layer, hs⟩ : Fin L).succ
  · rw [dif_pos hguard] at hmem hmem'
    rw [List.mem_flatMap] at hmem; obtain ⟨i', _, hmem⟩ := hmem
    rw [List.mem_map] at hmem; obtain ⟨j', _, rfl⟩ := hmem
    rw [List.mem_flatMap] at hmem'; obtain ⟨i'', _, hmem'⟩ := hmem'
    rw [List.mem_map] at hmem'; obtain ⟨j'', _, rfl⟩ := hmem'
    refine ⟨fun heq => ?_, fun heq => ?_⟩
    · obtain ⟨_, hcol⟩ := flatCoordOf_injective M _ heq
      rw [Fin.mk.injEq] at hcol; omega
    · obtain ⟨hrow, _⟩ := flatCoordOf_injective M _ heq
      rw [Fin.mk.injEq] at hrow; omega
  · rw [dif_neg hguard] at hmem; exact (List.not_mem_nil hmem).elim

/-- **The interior `a`-coordinates are pairwise distinct**: distinct interior cells `(i,j)` map to
distinct flat coordinates (`flatCoordOf` injective), so no coordinate is written by two shears.
Proven via `nodup_flatMap` (rows separate the fan-out branches, columns the inner ones). -/
theorem schurCells_pairwise (node : StepData M) (rows cols : ℕ) :
    List.Pairwise (fun x y => x.1 ≠ y.1) (schurCells node rows cols) := by
  have hnodup : ((schurCells node rows cols).map Prod.fst).Nodup := by
    rw [schurCells]
    by_cases hguard : ∃ hs : node.layer < L,
        node.cleared + rows ≤ M (⟨node.layer, hs⟩ : Fin L).castSucc ∧
        node.cleared + cols ≤ M (⟨node.layer, hs⟩ : Fin L).succ
    · rw [dif_pos hguard, List.map_flatMap, List.nodup_flatMap]
      refine ⟨fun i' _ => ?_, ?_⟩
      · simp only [List.map_map]
        refine List.Nodup.map (fun j'₁ j'₂ heq => ?_) (List.nodup_finRange _)
        simp only [Function.comp_apply] at heq
        obtain ⟨_, hcol⟩ := flatCoordOf_injective M _ heq
        rw [Fin.mk.injEq] at hcol; exact Fin.ext (by omega)
      · refine (List.nodup_finRange _).imp fun {i'₁ i'₂} hne x hx₁ hx₂ => ?_
        simp only [List.map_map, List.mem_map, Function.comp_apply] at hx₁ hx₂
        obtain ⟨j'₁, _, rfl⟩ := hx₁
        obtain ⟨j'₂, _, heq⟩ := hx₂
        obtain ⟨hrow, _⟩ := flatCoordOf_injective M _ heq
        rw [Fin.mk.injEq] at hrow
        exact hne (Fin.ext (show (i'₁ : ℕ) = i'₂ by omega))
    · rw [dif_neg hguard]; simp
  rwa [List.Nodup, List.pairwise_map] at hnodup

/-- **Conjugation of the fold**: the flat read of `residualSchurShear` is the fold of the bare
`elemShear`s on the flat coordinates (the inner `paramsEquivFlat`/`.symm` pairs cancel). -/
theorem residualSchur_flat_read (node : StepData M) (rows cols : ℕ) (w : Params M) :
    paramsEquivFlat M (residualSchurShear node rows cols w)
      = ((schurCells node rows cols).map fun abc => elemShear abc.1 abc.2.1 abc.2.2).foldr
          (· ∘ ·) id (paramsEquivFlat M w) := by
  rw [residualSchurShear, schurMaps]
  induction schurCells node rows cols with
  | nil => rfl
  | cons abc rest ih =>
    rw [List.map_cons, List.map_cons, List.foldr_cons, List.foldr_cons, Function.comp_apply,
      Function.comp_apply, flatElemShear_flat_read, ih]

/-- **Coordinates that are never a shear's target `a` are unchanged by the fold** (each `elemShear`
only updates its own `a`). The independence workhorse: the pivot row/col coordinates (never an
interior `a`) pass through the interior-block Schur fold untouched. -/
theorem elemShearFold_fixed
    (cells : List (Fin (flatDim M) × Fin (flatDim M) × Fin (flatDim M)))
    (X : Fin (flatDim M) → ℝ) (k : Fin (flatDim M)) (hk : ∀ abc ∈ cells, abc.1 ≠ k) :
    (cells.map fun abc => elemShear abc.1 abc.2.1 abc.2.2).foldr (· ∘ ·) id X k = X k := by
  induction cells with
  | nil => rfl
  | cons abc rest ih =>
    rw [List.map_cons, List.foldr_cons, Function.comp_apply, elemShear,
      Function.update_of_ne (Ne.symm (hk abc List.mem_cons_self))]
    exact ih (fun a ha => hk a (List.mem_cons_of_mem abc ha))

/-- **The fold's value at a target coordinate `a`**: `= X a − X b · X c`. Given the `a`-coordinates
are pairwise distinct (`hpair`, so `a` is written once) and every `b`, `c` is never a target
(`hb`/`hc`, so they pass through unchanged), the interior-block Schur fold reads its two source
ratios at their original values. -/
theorem elemShearFold_at_a
    (cells : List (Fin (flatDim M) × Fin (flatDim M) × Fin (flatDim M)))
    (X : Fin (flatDim M) → ℝ) (abc : Fin (flatDim M) × Fin (flatDim M) × Fin (flatDim M))
    (hmem : abc ∈ cells) (hpair : List.Pairwise (fun x y => x.1 ≠ y.1) cells)
    (hb : ∀ abc' ∈ cells, abc'.1 ≠ abc.2.1) (hc : ∀ abc' ∈ cells, abc'.1 ≠ abc.2.2) :
    (cells.map fun q => elemShear q.1 q.2.1 q.2.2).foldr (· ∘ ·) id X abc.1
      = X abc.1 - X abc.2.1 * X abc.2.2 := by
  induction cells with
  | nil => exact (List.not_mem_nil hmem).elim
  | cons abc₀ rest ih =>
    obtain ⟨hhead, hrestpair⟩ := List.pairwise_cons.mp hpair
    rw [List.map_cons, List.foldr_cons, Function.comp_apply]
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · rw [elemShear, Function.update_self,
        elemShearFold_fixed rest X abc.1 (fun a ha => Ne.symm (hhead a ha)),
        elemShearFold_fixed rest X abc.2.1
          (fun a ha => hb a (List.mem_cons_of_mem abc ha)),
        elemShearFold_fixed rest X abc.2.2
          (fun a ha => hc a (List.mem_cons_of_mem abc ha))]
    · rw [elemShear, Function.update_of_ne (Ne.symm (hhead abc hmem'))]
      exact ih hmem' hrestpair (fun abc' ha => hb abc' (List.mem_cons_of_mem abc₀ ha))
        (fun abc' ha => hc abc' (List.mem_cons_of_mem abc₀ ha))

/-- **The α source-gauge** (the incidence/Q,P Schur; `cert-psi-mix` §R-b): edge-class dispatch —
`id` on the case-1(1) merge (`α_u = refl`) and rollover; the interior residual Schur fold on the
case-1(2) d-family (`rows = runLen`) and case-2 (`rows = resRows`) residual births. Feeds the
`geoChartMapNorm` gauge slot. -/
noncomputable def alphaGauge : GeoChart M → Params M → Params M := fun g =>
  match g.edge.case with
  | StepCase.case11 => id
  | StepCase.rollover => id
  | StepCase.case12 => residualSchurShear g.node g.edge.subst.runLen g.node.resCols
  | StepCase.case2 => residualSchurShear g.node g.node.resRows g.node.resCols

/-! ## The gauge-parametric α-atlas (additive copy of `tGeo`/`fannedEdges`) -/

mutual
/-- Gauge-parametric `tGeo`: refine each branch by fanning edges into their `dCenterOfEdge` pivot
charts, threading `gauge` through `geoChartMapNorm` (the originals hardcode `fun _ => id`). -/
noncomputable def tGeoG (gauge : GeoChart M → Params M → Params M) (acc : Params M → Params M) :
    ResolutionTree M → ResolutionTree M
  | .leaf l => .leaf { l with chartMap := acc }
  | .branch n edges => .branch n (fannedEdgesG gauge acc n 0 edges)
/-- Companion of `tGeoG` over an edge list (per-edge fan-out, global pivot offset). -/
noncomputable def fannedEdgesG (gauge : GeoChart M → Params M → Params M)
    (acc : Params M → Params M) (n : StepData M) (offset : ℕ) :
    List (Edge M) → List (Edge M)
  | [] => []
  | .mk c s ch :: es =>
      (if dCenterOfEdge n (Edge.mk c s ch) = 0 then
        [Edge.mk c { s with localSub := id } (tGeoG gauge acc ch)]
      else
        (List.finRange (dCenterOfEdge n (Edge.mk c s ch))).map (fun p =>
          Edge.mk c { s with localSub := geoChartMapNorm gauge
                               ⟨n, Edge.mk c s ch, offset + (p : ℕ)⟩ }
            (tGeoG gauge (acc ∘ geoChartMapNorm gauge
                      ⟨n, Edge.mk c s ch, offset + (p : ℕ)⟩) ch)))
      ++ fannedEdgesG gauge acc n (offset + dCenterOfEdge n (Edge.mk c s ch)) es
end

/-- **The α-normalized flat virtual-leaf atlas**: the leaves of the gauge-parametric fan-out tree.
The loss atlas is `geoAtlasNorm alphaGauge (buildTree M (conOracle M) conRoot)`; the existing
`geoAtlas t = geoAtlasNorm (fun _ => id) t` (transfer lemma, later). -/
noncomputable def geoAtlasNorm (gauge : GeoChart M → Params M → Params M) (t : ResolutionTree M) :
    List (LeafData M) :=
  ResolutionTree.leaves (tGeoG gauge id t)

/-! ### `tGeoG` preserves the leaf ledger `resRank` (`resRank = 0` transfer) -/

/-- `edgesLeaves` distributes over list append. -/
theorem edgesLeaves_append (l1 l2 : List (Edge M)) :
    ResolutionTree.edgesLeaves (l1 ++ l2)
      = ResolutionTree.edgesLeaves l1 ++ ResolutionTree.edgesLeaves l2 := by
  induction l1 with
  | nil => simp [ResolutionTree.edgesLeaves]
  | cons e es ih =>
      obtain ⟨c, s, ch⟩ := e
      simp only [List.cons_append, ResolutionTree.edgesLeaves, ih, List.append_assoc]

/-- `edgesLeaves` of a `.mk`-built mapped edge-list is the `flatMap` of the child leaves. -/
theorem edgesLeaves_mapMk {α : Type*} (g : α → StepCase) (sub : α → ChartSubst M)
    (chi : α → ResolutionTree M) (l : List α) :
    ResolutionTree.edgesLeaves (l.map fun a => Edge.mk (g a) (sub a) (chi a))
      = l.flatMap fun a => ResolutionTree.leaves (chi a) := by
  induction l with
  | nil => simp [ResolutionTree.edgesLeaves]
  | cons a as ih =>
      simp only [List.map_cons, ResolutionTree.edgesLeaves, ih, List.flatMap_cons]

mutual
/-- **`tGeoG` preserves leaf `resRank`**: every `tGeoG gauge acc t` leaf's `resRank` occurs among
the `resRank`s of `t`'s leaves (`tGeoG` only rewrites `chartMap`). -/
theorem tGeoG_leaves_resRank (gauge : GeoChart M → Params M → Params M)
    (acc : Params M → Params M) :
    ∀ t : ResolutionTree M, ∀ l ∈ ResolutionTree.leaves (tGeoG gauge acc t),
      l.resRank ∈ (ResolutionTree.leaves t).map (·.resRank)
  | .leaf l₀ => by
      intro l hl
      rw [tGeoG] at hl
      simp only [ResolutionTree.leaves, List.mem_singleton] at hl
      subst hl
      simp [ResolutionTree.leaves]
  | .branch n edges => by
      intro l hl
      rw [tGeoG] at hl
      simp only [ResolutionTree.leaves] at hl ⊢
      exact fannedEdgesG_leaves_resRank gauge acc n 0 edges l hl
/-- Companion of `tGeoG_leaves_resRank` over an edge list. -/
theorem fannedEdgesG_leaves_resRank (gauge : GeoChart M → Params M → Params M)
    (acc : Params M → Params M) (n : StepData M) (offset : ℕ) :
    ∀ edges : List (Edge M),
      ∀ l ∈ ResolutionTree.edgesLeaves (fannedEdgesG gauge acc n offset edges),
        l.resRank ∈ (ResolutionTree.edgesLeaves edges).map (·.resRank)
  | [] => by intro l hl; rw [fannedEdgesG] at hl; simp [ResolutionTree.edgesLeaves] at hl
  | .mk c s ch :: es => by
      intro l hl
      rw [fannedEdgesG, edgesLeaves_append, List.mem_append] at hl
      simp only [ResolutionTree.edgesLeaves, List.map_append, List.mem_append]
      rcases hl with hl | hl
      · left
        by_cases hz : dCenterOfEdge n (Edge.mk c s ch) = 0
        · rw [if_pos hz] at hl
          simp only [ResolutionTree.edgesLeaves, List.append_nil] at hl
          exact tGeoG_leaves_resRank gauge acc ch l hl
        · rw [if_neg hz, edgesLeaves_mapMk, List.mem_flatMap] at hl
          obtain ⟨p, _, hl⟩ := hl
          exact tGeoG_leaves_resRank gauge _ ch l hl
      · exact Or.inr (fannedEdgesG_leaves_resRank gauge acc n
          (offset + dCenterOfEdge n (Edge.mk c s ch)) es l hl)
end

/-- **`resRank = 0` at every α-atlas leaf** (transfer of `leaves_resRank_zero` through `tGeoG`). -/
theorem geoAtlasNorm_resRank_zero (gauge : GeoChart M → Params M → Params M) (s : ConState L)
    (l : LeafData M) (hl : l ∈ geoAtlasNorm gauge (buildTree M (conOracle M) s)) :
    l.resRank = 0 := by
  have hmem := tGeoG_leaves_resRank gauge id (buildTree M (conOracle M) s) l hl
  rw [List.mem_map] at hmem
  obtain ⟨l₀, hl₀, hres⟩ := hmem
  rw [← hres]
  exact leaves_resRank_zero s l₀ hl₀

/-- The intermediate-point det product of a list of valid interior-cell shears is `1` (each factor
is det-1 everywhere). -/
theorem foldrCompAbsDet_flatElemShear
    (cells : List (Fin (flatDim M) × Fin (flatDim M) × Fin (flatDim M)))
    (hne : ∀ abc ∈ cells, abc.1 ≠ abc.2.1 ∧ abc.1 ≠ abc.2.2) (w : Params M) :
    foldrCompAbsDet (cells.map fun abc => flatElemShear abc.1 abc.2.1 abc.2.2) w = 1 := by
  induction cells with
  | nil => rfl
  | cons abc rest ih =>
    rw [List.map_cons, foldrCompAbsDet]
    obtain ⟨hab, hac⟩ := hne abc (List.mem_cons_self)
    rw [flatElemShear_abs_det_one abc.1 abc.2.1 abc.2.2 hab hac,
      ih (fun x hx => hne x (List.mem_cons_of_mem abc hx)), one_mul]

/-- **The interior-block Schur fold is det-1** — a composition of valid `flatElemShear`s. -/
theorem residualSchurShear_abs_det_one (node : StepData M) (rows cols : ℕ) (w : Params M) :
    |(fderiv ℝ (residualSchurShear node rows cols) w).det| = 1 := by
  rw [residualSchurShear, schurMaps,
    abs_det_fderiv_foldr_comp _
      (by
        intro f hf
        rw [List.mem_map] at hf
        obtain ⟨abc, _, rfl⟩ := hf
        exact flatElemShear_differentiable abc.1 abc.2.1 abc.2.2) w]
  exact foldrCompAbsDet_flatElemShear _ (schurCells_ne node rows cols) w

/-! ## PHASE-1 obligation statements (the `sorry` frontier) -/

/-- **(ii) α is det-1** (PHASE 2, banked-atom-shaped): each `alphaGauge g` has Fréchet-derivative
determinant of modulus 1 — `id` trivially; the d-family fold via `abs_det_fderiv_elemShear`
(`ShearReconcile`) + conjugation-invariance of `|det|` + chain rule over the composition. This keeps
t14's `geoAtlas_fold_det` g-det-1-TRANSPARENT (compass fork-15). -/
theorem alphaGauge_abs_det_one (g : GeoChart M) (w : Params M) :
    |(fderiv ℝ (alphaGauge (M := M) g) w).det| = 1 := by
  unfold alphaGauge
  split
  all_goals first
    | (rw [fderiv_id, show (ContinuousLinearMap.id ℝ (Params M)).det
          = LinearMap.det (ContinuousLinearMap.id ℝ (Params M)).toLinearMap from rfl]
       simp [LinearMap.det_id])
    | exact residualSchurShear_abs_det_one _ _ _ w

/-- **The interior-block Schur fold is R(1+R)-bounded in preimage** (per coordinate): if every flat
coordinate of `residualSchurShear … w` has modulus `≤ R`, then every flat coordinate of `w` has
modulus `≤ R·(1+R)`. Non-target coords are unchanged (`≤ R`); a target `a` satisfies `X a = (fold X)
a + (fold X) b · (fold X) c` (its ratios `b,c` unchanged), so `|X a| ≤ R + R·R`. -/
theorem residualSchurShear_srcBox (node : StepData M) (rows cols : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (w : Params M) (hw : ∀ k, |paramsEquivFlat M (residualSchurShear node rows cols w) k| ≤ R) :
    ∀ k, |paramsEquivFlat M w k| ≤ R * (1 + R) := by
  simp only [residualSchur_flat_read] at hw
  intro k
  by_cases hk : ∃ abc ∈ schurCells node rows cols, abc.1 = k
  · obtain ⟨abc, habc, rfl⟩ := hk
    have hbc := schurCells_snd_ne node rows cols abc habc
    have ha := elemShearFold_at_a (schurCells node rows cols) (paramsEquivFlat M w) abc habc
      (schurCells_pairwise node rows cols) (fun abc' h => (hbc abc' h).1)
      (fun abc' h => (hbc abc' h).2)
    have hb1 := hw abc.1
    have hbc_bd : |paramsEquivFlat M w abc.2.1 * paramsEquivFlat M w abc.2.2| ≤ R * R := by
      rw [abs_mul]
      refine mul_le_mul ?_ ?_ (abs_nonneg _) hR
      · rw [← elemShearFold_fixed (schurCells node rows cols) (paramsEquivFlat M w) abc.2.1
          (fun abc' h => (hbc abc' h).1)]; exact hw abc.2.1
      · rw [← elemShearFold_fixed (schurCells node rows cols) (paramsEquivFlat M w) abc.2.2
          (fun abc' h => (hbc abc' h).2)]; exact hw abc.2.2
    have hsub : |paramsEquivFlat M w abc.1
        - paramsEquivFlat M w abc.2.1 * paramsEquivFlat M w abc.2.2| ≤ R := by
      rw [← ha]; exact hb1
    have hsplit : paramsEquivFlat M w abc.1
        = (paramsEquivFlat M w abc.1
            - paramsEquivFlat M w abc.2.1 * paramsEquivFlat M w abc.2.2)
          + paramsEquivFlat M w abc.2.1 * paramsEquivFlat M w abc.2.2 := by ring
    calc |paramsEquivFlat M w abc.1|
        = |(paramsEquivFlat M w abc.1
              - paramsEquivFlat M w abc.2.1 * paramsEquivFlat M w abc.2.2)
            + paramsEquivFlat M w abc.2.1 * paramsEquivFlat M w abc.2.2| := by rw [← hsplit]
      _ ≤ _ + _ := abs_add_le _ _
      _ ≤ R + R * R := add_le_add hsub hbc_bd
      _ = R * (1 + R) := by ring
  · push_neg at hk
    have hbound := hw k
    rw [elemShearFold_fixed (schurCells node rows cols) (paramsEquivFlat M w) k hk] at hbound
    nlinarith [hbound, abs_nonneg (paramsEquivFlat M w k)]

/-- **(iii) The srcBox transform** (PHASE 2, the cert's boundedness): `alphaGauge g` pulls the flat
cube of radius `R` back inside the flat cube of radius `R·(1+R)`. `α` fixes the ratio coords `b,c`
and shifts `x_a ↦ x_a − x_b·x_c`, so `x_a` before `α` is `α(x)_a + x_b·x_c`, `|x_a| ≤ R + R² =
R(1+R)`; the interior cells are disjoint from the pivot row/col, so the fold does not compound the
bound. -/
theorem alphaGauge_srcBox_bounded (g : GeoChart M) {R : ℝ} (hR : 0 ≤ R) :
    alphaGauge (M := M) g ⁻¹' (⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R)
      ⊆ ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) (R * (1 + R)) := by
  intro w hw
  have hw' : ∀ k, |paramsEquivFlat M (alphaGauge (M := M) g w) k| ≤ R := by
    intro k
    have h1 := Set.mem_preimage.mp (Set.mem_preimage.mp hw)
    rw [cubeBox, Set.mem_pi] at h1
    exact abs_le.mpr (Set.mem_Icc.mp (h1 k (Set.mem_univ k)))
  rw [Set.mem_preimage, cubeBox, Set.mem_pi]
  suffices h : ∀ k, |paramsEquivFlat M w k| ≤ R * (1 + R) by
    intro k _; exact Set.mem_Icc.mpr (abs_le.mp (h k))
  cases hc : g.edge.case with
  | case11 =>
      simp only [alphaGauge, hc, id_eq] at hw'
      intro k; nlinarith [hw' k, mul_nonneg hR hR, abs_nonneg (paramsEquivFlat M w k)]
  | rollover =>
      simp only [alphaGauge, hc, id_eq] at hw'
      intro k; nlinarith [hw' k, mul_nonneg hR hR, abs_nonneg (paramsEquivFlat M w k)]
  | case12 =>
      simp only [alphaGauge, hc] at hw'
      exact residualSchurShear_srcBox _ _ _ hR w hw'
  | case2 =>
      simp only [alphaGauge, hc] at hw'
      exact residualSchurShear_srcBox _ _ _ hR w hw'

/-! ## Parametric templates for the α completion (Lg/Rg cross-cell folds)

The α-completion to Aoyagi's full Q,P adds pivot-column (`Lg`, ≤S-local) and pivot-row (`Rg`,
cross-layer into S+1) `flatElemShear` cells to the interior Schur fold; the exact cells come from
pnp-rg's completed-α achiever (thread 24 cell-write trace). These three lemmas are the
FORM-INDEPENDENT templates the completed gauge instantiates — generic over ANY valid `flatElemShear`
cell list (`a ≠ b`, `a ≠ c` per cell). The first two generalize the interior-only
`residualSchur_flat_read` / `residualSchurShear_abs_det_one` (the completed gauge is one fold over
`interior ++ Lg ++ Rg` cells). `elemShearFold_srcBox_bound` is the NEW compounding preimage bound
the cross-writing needs: once the pivot cross is WRITTEN, `schurCells_snd_ne`'s disjointness (tight
`R(1+R)`) no longer applies, so the bound compounds to a finite iterate of `g R = R(1+R)` — and
`∃ R' > 0` is all the ChartBridge `(B)` clause needs. -/

/-- Generic flat read of a `flatElemShear` fold (generalizes `residualSchur_flat_read` to any cell
list): the inner `paramsEquivFlat`/`.symm` pairs cancel to the bare `elemShear` fold. -/
theorem foldFlatElemShear_flat_read
    (cells : List (Fin (flatDim M) × Fin (flatDim M) × Fin (flatDim M))) (w : Params M) :
    paramsEquivFlat M
        ((cells.map fun abc => flatElemShear abc.1 abc.2.1 abc.2.2).foldr (· ∘ ·) id w)
      = (cells.map fun abc => elemShear abc.1 abc.2.1 abc.2.2).foldr (· ∘ ·) id
          (paramsEquivFlat M w) := by
  induction cells with
  | nil => rfl
  | cons abc rest ih =>
    rw [List.map_cons, List.map_cons, List.foldr_cons, List.foldr_cons, Function.comp_apply,
      Function.comp_apply, flatElemShear_flat_read, ih]

/-- Generic det-1 of a `flatElemShear` fold (generalizes `residualSchurShear_abs_det_one` to any
valid cell list): a composition of det-1 `flatElemShear`s is det-1. -/
theorem foldFlatElemShear_abs_det_one
    (cells : List (Fin (flatDim M) × Fin (flatDim M) × Fin (flatDim M)))
    (hne : ∀ abc ∈ cells, abc.1 ≠ abc.2.1 ∧ abc.1 ≠ abc.2.2) (w : Params M) :
    |(fderiv ℝ ((cells.map fun abc => flatElemShear abc.1 abc.2.1 abc.2.2).foldr (· ∘ ·) id)
        w).det| = 1 := by
  rw [abs_det_fderiv_foldr_comp _
      (by
        intro f hf
        rw [List.mem_map] at hf
        obtain ⟨abc, _, rfl⟩ := hf
        exact flatElemShear_differentiable abc.1 abc.2.1 abc.2.2) w]
  exact foldrCompAbsDet_flatElemShear _ hne w

/-- **The compounding preimage bound for an arbitrary `elemShear` fold** (the α-completion's new
srcBox lemma). For a fold of valid `elemShear` cells, if every output flat coordinate has modulus
`≤ R` then every input coordinate is bounded by a finite `R'`. Unlike `residualSchurShear_srcBox`,
this makes NO disjointness assumption (the completed fold WRITES the pivot cross), so it applies to
the full Q,P gauge; `∃ R' > 0` is exactly what the `(B)` clause needs. Proof: induction on the fold;
peeling one cell `(a,b,c)` (`a ≠ b`, `a ≠ c`) inflates the bound at most by `g R = R(1+R)` — the two
sources `b,c` pass through unchanged, so `|X a| ≤ |output a| + |X b|·|X c| ≤ R + R·R`. -/
theorem elemShearFold_srcBox_bound
    (cells : List (Fin (flatDim M) × Fin (flatDim M) × Fin (flatDim M))) :
    (∀ abc ∈ cells, abc.1 ≠ abc.2.1 ∧ abc.1 ≠ abc.2.2) → ∀ R : ℝ, 0 ≤ R →
      ∃ R' : ℝ, 0 ≤ R' ∧ ∀ X : Fin (flatDim M) → ℝ,
        (∀ k, |(cells.map fun abc => elemShear abc.1 abc.2.1 abc.2.2).foldr (· ∘ ·) id X k| ≤ R) →
          ∀ k, |X k| ≤ R' := by
  induction cells with
  | nil => intro _ R hR; exact ⟨R, hR, fun X hX k => hX k⟩
  | cons abc rest ih =>
    intro hne R hR
    obtain ⟨hb, hc⟩ := hne abc List.mem_cons_self
    have hrest : ∀ x ∈ rest, x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 :=
      fun x hx => hne x (List.mem_cons_of_mem abc hx)
    obtain ⟨R', hR'nonneg, hR'⟩ := ih hrest (R * (1 + R)) (mul_nonneg hR (by linarith))
    refine ⟨R', hR'nonneg, fun X hX => ?_⟩
    have hXe : ∀ k, |elemShear abc.1 abc.2.1 abc.2.2
        ((rest.map fun q => elemShear q.1 q.2.1 q.2.2).foldr (· ∘ ·) id X) k| ≤ R := by
      intro k
      have h := hX k
      rwa [List.map_cons, List.foldr_cons, Function.comp_apply] at h
    have hYbound : ∀ k, |(rest.map fun q => elemShear q.1 q.2.1 q.2.2).foldr (· ∘ ·) id X k|
        ≤ R * (1 + R) := by
      intro k
      by_cases hk : k = abc.1
      · subst hk
        have e := hXe abc.1
        rw [elemShear, Function.update_self] at e
        have s1 : |(rest.map fun q => elemShear q.1 q.2.1 q.2.2).foldr (· ∘ ·) id X abc.2.1|
            ≤ R := by
          have h := hXe abc.2.1
          rwa [elemShear, Function.update_of_ne (Ne.symm hb)] at h
        have s2 : |(rest.map fun q => elemShear q.1 q.2.1 q.2.2).foldr (· ∘ ·) id X abc.2.2|
            ≤ R := by
          have h := hXe abc.2.2
          rwa [elemShear, Function.update_of_ne (Ne.symm hc)] at h
        set Y := (rest.map fun q => elemShear q.1 q.2.1 q.2.2).foldr (· ∘ ·) id X with hYdef
        have habs : |Y abc.2.1 * Y abc.2.2| ≤ R * R := by
          rw [abs_mul]; exact mul_le_mul s1 s2 (abs_nonneg _) hR
        have hsplit : Y abc.1
            = (Y abc.1 - Y abc.2.1 * Y abc.2.2) + Y abc.2.1 * Y abc.2.2 := by ring
        calc |Y abc.1|
            = |(Y abc.1 - Y abc.2.1 * Y abc.2.2) + Y abc.2.1 * Y abc.2.2| := by rw [← hsplit]
          _ ≤ |Y abc.1 - Y abc.2.1 * Y abc.2.2| + |Y abc.2.1 * Y abc.2.2| := abs_add_le _ _
          _ ≤ R + R * R := add_le_add e habs
          _ = R * (1 + R) := by ring
      · have h := hXe k
        rw [elemShear, Function.update_of_ne hk] at h
        nlinarith [h, mul_nonneg hR hR]
    exact hR' X hYbound

/-! ## PHASE 3a — the loss-algebra reduction (the named `prod = diagonal` input) -/

/-- **The named geometric input** (PHASE 3b, routed to pnp-fold's shared state↔geometry invariant):
the loss-side reading of `prod ∘ chartMap = diagonal(monomial chain)`. It asserts, on `srcBox`, that
`frobSq(prod(chartMap w)) = Σᵢ (D · rᵢ)²` where `D = ∏_k z_{divCoord k}(w)` is the terminal-divisor
product and the `rᵢ` are the divisibility-chain **ratios** `bᵢ/b₁` (polynomials, by the `bChain`
monotone `b₁ | bᵢ`); one ratio is `1` (the `b₁ = D` diagonal entry itself); and the ratios are
uniformly bounded on the bounded `srcBox` (the leaf's flat cube). This is the diagonalization the α
gauge is designed to realize (`residualSchurShear` clears the residual so `prod` is diagonal);
supplied by the shared fold invariant, NOT proven here (the loss-VALUE analog of t14's Jacobian
`geoAtlas_fold_det`). -/
def LeafDiagFrob (l : LeafData (L := L) M) : Prop :=
  ∃ (m : ℕ) (r : Params M → Fin m → ℝ) (hi : ℝ),
    (∀ w ∈ l.srcBox,
      frobSq (prod M (l.chartMap w))
        = ∑ i : Fin m,
            ((∏ k : Fin l.numDiv, paramsEquivFlat M w (l.divCoord k)) * r w i) ^ 2) ∧
    (∀ w ∈ l.srcBox, ∃ i : Fin m, r w i = 1) ∧
    (∀ w ∈ l.srcBox, ∑ i : Fin m, (r w i) ^ 2 ≤ hi)

/-- **The loss-algebra reduction** (PHASE 3a, PROVEN): at a `resRank = 0` leaf, the named diagonal
input `LeafDiagFrob` yields `LeafPullback`. `residualCore := Σᵢ rᵢ²`, `lo := 1`, `hi` from the ratio
bound; `baseForm = 1` (resRank = 0). The factorization is `Σᵢ (D·rᵢ)² = (∏ z²)·(Σ rᵢ²)`
(`mul_pow` + `Finset.mul_sum` + `Finset.prod_pow`); `residualCore ≥ 1` because one ratio is `1` and
squares are nonnegative. This closes the loss-algebra layer hole-free — the only remaining input is
the geometric `LeafDiagFrob`. -/
theorem leafPullback_of_diagFrob (l : LeafData (L := L) M)
    (hd : LeafDiagFrob l) (hr : l.resRank = 0) : LeafPullback l := by
  obtain ⟨m, r, hi, hfrob, hone, hbd⟩ := hd
  refine ⟨fun w => ∑ i : Fin m, (r w i) ^ 2, 1, max hi 1, one_pos, fun w hw => ⟨?_, ?_, ?_⟩⟩
  · rw [hfrob w hw]
    rw [Finset.sum_congr rfl (fun i _ => mul_pow _ (r w i) 2), ← Finset.mul_sum,
      ← Finset.prod_pow]
  · rw [residualBaseForm, if_pos hr, mul_one]
    obtain ⟨i₀, hi₀⟩ := hone w hw
    calc (1 : ℝ) = (r w i₀) ^ 2 := by rw [hi₀]; norm_num
      _ ≤ ∑ i : Fin m, (r w i) ^ 2 :=
          Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ i₀)
  · rw [residualBaseForm, if_pos hr, mul_one]
    exact le_trans (hbd w hw) (le_max_left _ _)

/-- **The geometric crux (PHASE 3b), routed to pnp-fold's shared invariant** — NOT proven in this
seat. `prod ∘ chartMap` diagonalizes to the leaf's monomial `b`-chain at every α-atlas leaf: the
loss-VALUE analog of t14's Jacobian `geoAtlas_fold_det`. It is the SAME state↔geometry induction
through `buildTree`'s `stepUpdate` — the value version (the partial fold's `prod` equals the state's
partial monomial form) whose derivative shadow t14 proves. The α gauge (`residualSchurShear`, det-1
+ srcBox-bounded, PROVEN here) is exactly what makes the residual clear so `prod` is diagonal; this
lemma asserts the geometry realizes it. Supplied by the shared fold cert; the single remaining
`sorry` of the loss lane. -/
-- REFUTED-AS-STATED (#3a, cert-full-value-walk §6): the chart-CoV `LeafPullback` value half. The
-- goal-level no-go shows NO det-1 chart makes the residual core bounded below / diagonal on an
-- open set (it → 0; diagonalization needs a det-0 projection) — category-false for ALL charts,
-- not just this α gauge. So this `sorry` is NOT a fillable frontier: the honest lower bound is
-- IDEAL-LEVEL (Aoyagi Lemma 1 over the banked resolution), the follow-up's target. See
-- `aoyagi_learning_coefficient_gen` (the honest engine, on the box-finiteness Prop).
theorem leafDiagFrob_geoAtlasNorm (l : LeafData M)
    (hl : l ∈ geoAtlasNorm (alphaGauge (M := M)) (buildTree M (conOracle M) conRoot)) :
    LeafDiagFrob l := by
  sorry

/-- **(iv) LeafPullback over the α-atlas** (PHASE 3, the loss squeeze): every leaf of the
α-normalized built atlas satisfies the loss factorization `frobSq(prod(chartMap w)) =
∏ z_{divCoord}²·residualCore` with `0 < lo ≤ residualCore/baseForm ≤ hi`. On the spine `resRank = 0`
(`leaves_resRank_zero`, transferred through `tGeoG`), so `baseForm = 1` and `lo = 1` (the
constant-bound case; `l3_compose_and_diagb.py` §II).

STRUCTURE (design note §2 / elder ruling): the loss-algebra half is `leafPullback_of_diagFrob`
(PROVEN above) and the `resRank = 0` transfer is `geoAtlasNorm_resRank_zero` (PROVEN). The one
remaining input is the geometry half `leafDiagFrob_geoAtlasNorm` (the loss-VALUE analog of t14's
Jacobian `geoAtlas_fold_det`, strictly deeper — no `prod ∘ chart` infrastructure exists), routed to
pnp-fold's shared state↔geometry invariant. -/
theorem leafPullback_geoAtlasNorm (l : LeafData M)
    (hl : l ∈ geoAtlasNorm (alphaGauge (M := M)) (buildTree M (conOracle M) conRoot)) :
    LeafPullback l :=
  leafPullback_of_diagFrob l (leafDiagFrob_geoAtlasNorm l hl)
    (geoAtlasNorm_resRank_zero (alphaGauge (M := M)) conRoot l hl)

/- **(B)-discharge wiring — LANDED (t14 encore, atlas-seam ruling).** The pre-staged plan here is
SUPERSEDED: `chartBridgeFaithful_buildTree` now witnesses `geoAtlasNorm alphaGauge` DIRECTLY (the
faithful atlas), so its `(B)` `LeafPullback` slot consumes `leafPullback_geoAtlasNorm c hc` with NO
cover-transfer lemma needed — membership in the α atlas is definitional (the `(B)` quantifier ranges
over `geoAtlasNorm alphaGauge (buildTree …)`, exactly this lemma's hypothesis). The remaining loss-lane
`sorry` on the value path is `leafDiagFrob_geoAtlasNorm` (above); the ledger/ae-inj `(B)`/`(C)` props
transfer via `Engine.GeoAtlasTransfer`. -/

end DLNFibre.DLN.RLCT.Engine
