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

/-- **(iii) The srcBox transform** (PHASE 2, the cert's boundedness): `alphaGauge g` pulls the flat
cube of radius `R` back inside the flat cube of radius `R·(1+R)`. `α` fixes the ratio coords `b,c`
and shifts `x_a ↦ x_a − x_b·x_c`, so `x_a` before `α` is `α(x)_a + x_b·x_c`, `|x_a| ≤ R + R² =
R(1+R)`; the interior cells are disjoint from the pivot row/col, so the fold does not compound the
bound. -/
theorem alphaGauge_srcBox_bounded (g : GeoChart M) {R : ℝ} (hR : 0 ≤ R) :
    alphaGauge (M := M) g ⁻¹' (⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R)
      ⊆ ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) (R * (1 + R)) := by
  sorry

/-- **(iv) LeafPullback over the α-atlas** (PHASE 3, the loss squeeze): every leaf of the
α-normalized built atlas satisfies the loss factorization `frobSq(prod(chartMap w)) =
∏ z_{divCoord}²·residualCore` with `0 < lo ≤ residualCore/baseForm ≤ hi`. On the spine `resRank = 0`
(`leaves_resRank_zero`, transferred through `tGeoG`), so `baseForm = 1` and `lo = 1` (the
constant-bound case; `l3_compose_and_diagb.py` §II).

DECOMPOSITION (design note §2): the reachable half is the loss-algebra — given
`prod(chartMap w) = diagonal(monomial chain)`, the factorization `Σbᵢ² = b₁²·(1 + Σ(bᵢ/b₁)²)` and
`residualCore ≥ 1` are elementary. The crux is the geometry half `prod ∘ chartMap = diagonal` (the
loss-VALUE analog of t14's Jacobian `geoAtlas_fold_det`, strictly deeper — no `prod ∘ chart`
infrastructure exists), the coverage/clause-D fidelity content, surfaced as the seam. -/
theorem leafPullback_geoAtlasNorm (l : LeafData M)
    (hl : l ∈ geoAtlasNorm (alphaGauge (M := M)) (buildTree M (conOracle M) conRoot)) :
    LeafPullback l := by
  sorry

end DLNFibre.DLN.RLCT.Engine
