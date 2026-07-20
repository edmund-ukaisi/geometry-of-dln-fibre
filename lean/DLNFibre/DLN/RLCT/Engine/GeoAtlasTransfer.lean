-- ⛔ RETIRED CHART ROUTE — DO NOT FILL THE `sorry`s IN THIS MODULE. ⛔
-- The id→α atlas transfer of the abandoned chart route; `geoAtlasNorm_imageCover` (~:823, "transfer
-- owed / route pending") LOOKS like a fillable plumbing hole but belongs to the category-false chart
-- cover — closing it is not progress. See `expeditions/.../charter.md` §3. Replacement = charter
-- Object B (ideal-level). Off the deliverable path.
import DLNFibre.DLN.RLCT.Engine.GeoAlphaGauge
import DLNFibre.DLN.RLCT.Engine.GeoLeafLedger
import DLNFibre.DLN.RLCT.Engine.GeoInjFold
import DLNFibre.DLN.RLCT.Engine.GeoFoldRegroup
import DLNFibre.DLN.RLCT.Engine.GeoInvValWalk

/-!
# `DLNFibre.DLN.RLCT.Engine.GeoAtlasTransfer` — the id-atlas → α-atlas transfer batch (t14 encore)

The atlas-seam ruling (compass fork 15, third amendment + tick-341 addendum): the FAITHFUL witness of
`ChartBridgeFaithful` is `geoAtlasNorm alphaGauge t` — the α-normalized atlas that IS Aoyagi's
integration chart (normal crossings reached only after the regular Q,P normalization). t14's landed
`(B)`/`(C)` inventory (`geoAtlas_leaf_ledgerProps`, `geoAtlas_leaf_ae_injOn`) is over the id-gauge
atlas `geoAtlas t = leaves (tGeo id t)`; this module transfers it to
`geoAtlasNorm gauge t = leaves (tGeoG gauge id t)`.

The keystone: a `tGeoG` leaf is `{ l with chartMap := acc }` for an original `t`-leaf `l` (only
`chartMap` differs — the same as `tGeo`). So the LEDGER props (`(B)` measurable/bounded/inj/disjoint +
`(C)` exponents) transfer VERBATIM from the original leaf (they read no `chartMap`); only the two
`chartMap`-reading clauses (a.e.-injectivity here; `LeafPullback`/`LeafJacobian` elsewhere) need the
per-factor α argument.

* `tGeoG_leaf_update` / `geoAtlasNorm_leaf_update` — the ledger correspondence (mirror
  `GeoLeafLedger.tGeo_leaf_update`).
* `geoAtlasNorm_leaf_ledgerProps` — the `(B)`/`(C)` ledger props over any `gauge` (mirror
  `geoAtlas_leaf_ledgerProps`).
* `geoAtlasNorm_leaf_ae_injOn` — the a.e.-injectivity clause over `alphaGauge` (α is an injective
  homeomorph fixing `0`, QMP; compose through the id-factor argument).
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open MeasureTheory Set

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-! ## The ledger correspondence for the gauge-parametric tree `tGeoG` -/

mutual
/-- **The gauge-parametric ledger correspondence**: every `tGeoG gauge acc t` leaf is
`{ l with chartMap := f }` for an original `t`-leaf `l` — the ledger fields are inherited verbatim
(mirror of `GeoLeafLedger.tGeo_leaf_update`; `tGeoG` also only rewrites `chartMap`). -/
theorem tGeoG_leaf_update (gauge : GeoChart M → Params M → Params M) (acc : Params M → Params M) :
    ∀ t : ResolutionTree M, ∀ c ∈ ResolutionTree.leaves (tGeoG gauge acc t),
      ∃ l ∈ ResolutionTree.leaves t, ∃ f : Params M → Params M, c = { l with chartMap := f }
  | .leaf l => by
      intro c hc
      rw [tGeoG, ResolutionTree.leaves, List.mem_singleton] at hc
      subst hc
      exact ⟨l, by simp [ResolutionTree.leaves], acc, rfl⟩
  | .branch n edges => by
      intro c hc
      rw [tGeoG, ResolutionTree.leaves] at hc
      obtain ⟨l, hl, f, hf⟩ := fannedEdgesG_leaf_update gauge acc n 0 edges c hc
      exact ⟨l, by rw [ResolutionTree.leaves]; exact hl, f, hf⟩
/-- Companion of `tGeoG_leaf_update` over an edge list (per-edge fan-out). -/
theorem fannedEdgesG_leaf_update (gauge : GeoChart M → Params M → Params M)
    (acc : Params M → Params M) (n : StepData M) (offset : ℕ) :
    ∀ edges : List (Edge M),
      ∀ c ∈ ResolutionTree.edgesLeaves (fannedEdgesG gauge acc n offset edges),
        ∃ l ∈ ResolutionTree.edgesLeaves edges, ∃ f : Params M → Params M,
          c = { l with chartMap := f }
  | [] => by intro c hc; rw [fannedEdgesG] at hc; cases hc
  | .mk ec esub ch :: rest => by
      intro c hc
      rw [fannedEdgesG, edgesLeaves_append, List.mem_append] at hc
      rcases hc with hc | hc
      · -- `c` in the fanned copies of `ch`'s leaves — reduce to a `tGeoG gauge acc' ch` leaf via IH
        have hch : ∃ acc', c ∈ ResolutionTree.leaves (tGeoG gauge acc' ch) := by
          by_cases hz : dCenterOfEdge n (Edge.mk ec esub ch) = 0
          · rw [if_pos hz] at hc
            simp only [ResolutionTree.edgesLeaves, List.append_nil] at hc
            exact ⟨acc, hc⟩
          · rw [if_neg hz, edgesLeaves_mapMk, List.mem_flatMap] at hc
            obtain ⟨p, _, hcp⟩ := hc
            exact ⟨_, hcp⟩
        obtain ⟨acc', hcp⟩ := hch
        obtain ⟨l, hl, f, hf⟩ := tGeoG_leaf_update gauge acc' ch c hcp
        exact ⟨l, by rw [ResolutionTree.edgesLeaves]; exact List.mem_append_left _ hl, f, hf⟩
      · obtain ⟨l, hl, f, hf⟩ :=
          fannedEdgesG_leaf_update gauge acc n (offset + dCenterOfEdge n (Edge.mk ec esub ch))
            rest c hc
        exact ⟨l, by rw [ResolutionTree.edgesLeaves]; exact List.mem_append_right _ hl, f, hf⟩
end

/-- **The `geoAtlasNorm`-leaf correspondence** (`acc = id` specialization): every
`geoAtlasNorm gauge t` piece is `{ l with chartMap := f }` for an original `t`-leaf `l`. -/
theorem geoAtlasNorm_leaf_update (gauge : GeoChart M → Params M → Params M) (t : ResolutionTree M) :
    ∀ c ∈ geoAtlasNorm gauge t, ∃ l ∈ ResolutionTree.leaves t, ∃ f : Params M → Params M,
      c = { l with chartMap := f } := by
  rw [geoAtlasNorm]; exact tGeoG_leaf_update gauge id t

/-- **The `(B)` ledger props + `(C)` exponents transfer** to every `geoAtlasNorm gauge` piece via the
correspondence (mirror of `geoAtlas_leaf_ledgerProps`; the fields read are inherited verbatim from the
original leaf, so the gauge is irrelevant). The two `chartMap`-reading props (a.e.-inj,
`LeafPullback`/`LeafJacobian`) are elsewhere. -/
theorem geoAtlasNorm_leaf_ledgerProps (gauge : GeoChart M → Params M → Params M) (c : LeafData M)
    (hc : c ∈ geoAtlasNorm gauge (buildTree M (conOracle M) (conRoot : ConState L))) :
    MeasurableSet c.srcBox ∧
      (∃ R : ℝ, 0 < R ∧ c.srcBox ⊆ ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R) ∧
      Function.Injective c.divCoord ∧ Function.Injective c.resCoord ∧
      Disjoint (Set.range c.divCoord) (Set.range c.resCoord) ∧
      (∀ k : Fin c.numDiv,
          c.divExp k ∈ ResolutionTree.terminalExponents (buildTree M (conOracle M) conRoot)) ∧
      (0 < c.resRank →
          c.resRank ∈ ResolutionTree.terminalExponents (buildTree M (conOracle M) conRoot)) := by
  obtain ⟨l, hl, f, hf⟩ := geoAtlasNorm_leaf_update _ _ c hc
  obtain ⟨hdiv, hres, hdisj⟩ := leaves_chart_clauses_conRoot l hl
  have hsrc : l.srcBox = ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) 1 :=
    leaves_srcBox_flatCube conRoot l hl
  subst hf
  refine ⟨?_, ⟨1, one_pos, ?_⟩, hdiv, hres, hdisj, ?_, ?_⟩
  · show MeasurableSet l.srcBox; rw [hsrc]; exact flatCubeSrcBox_measurableSet 1
  · show l.srcBox ⊆ _; rw [hsrc]
  · exact fun k => divExp_mem_terminalExponents _ l hl k
  · exact fun hpos => resRank_mem_terminalExponents _ l hl hpos

/-! ## The α gauge is an injective homeomorph fixing `0`, quasi-measure-preserving

The a.e.-injectivity transfer: on the reachable cone `geoChartMapNorm alphaGauge g =
geoChartMapNorm (fun _ => id) g ∘ alphaGauge g` (the source gauge composed innermost), and `alphaGauge`
is a composition of elementary Schur shears — each an injective (`elemShearHomeomorph`) diffeomorphism,
QMP (its polynomial inverse `elemShearInv` is differentiable everywhere, so preimages of null sets are
null). So the id-factor's banked QMP + a.e.-inj (`GeoInjFold`) compose with the gauge's. -/

section ElemShear
variable {d : ℕ}

/-- **`elemShearInv` is differentiable everywhere** — a polynomial map (`x ↦ x + (x_b·x_c)·eₐ`), the
sign-flipped `elemShear`. -/
theorem elemShearInv_differentiable (a b c : Fin d) :
    Differentiable ℝ (elemShearInv a b c) := by
  have h : elemShearInv a b c
      = fun x : Fin d → ℝ => x + (x b * x c) • (Pi.single a 1 : Fin d → ℝ) := by
    funext x k
    simp only [elemShearInv, Function.update_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul]
    by_cases hk : k = a <;> simp [hk]
  rw [h]
  exact differentiable_id.add
    (((differentiable_apply b).mul (differentiable_apply c)).smul_const (Pi.single a 1 : Fin d → ℝ))

/-- **`elemShear` sends null sets to null preimages** (given the shear side conditions `a ≠ b`,
`a ≠ c`): `elemShear a b c` is a bijection with inverse `elemShearInv` (`elemShearHomeomorph`), so its
preimage is `elemShearInv '' Z`, null because `elemShearInv` is differentiable everywhere. -/
theorem elemShear_preimage_null (a b c : Fin d) (hab : a ≠ b) (hac : a ≠ c)
    {Z : Set (Fin d → ℝ)} (h0 : volume Z = 0) : volume (elemShear a b c ⁻¹' Z) = 0 := by
  have hsub : elemShear a b c ⁻¹' Z ⊆ elemShearInv a b c '' Z := by
    intro u hu
    rw [Set.mem_preimage] at hu
    exact ⟨elemShear a b c u, hu, (elemShearHomeomorph a b c hab hac).left_inv u⟩
  refine measure_mono_null hsub ?_
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (elemShearInv_differentiable a b c).differentiableOn h0

/-- **`elemShear a b c` is quasi-measure-preserving** (given `a ≠ b`, `a ≠ c`). -/
theorem elemShear_qmp (a b c : Fin d) (hab : a ≠ b) (hac : a ≠ c) :
    Measure.QuasiMeasurePreserving (elemShear a b c) (volume : Measure (Fin d → ℝ)) volume := by
  have hmeas : Measurable (elemShear a b c) :=
    (elemShearHomeomorph a b c hab hac).continuous.measurable
  refine ⟨hmeas, ?_⟩
  refine Measure.AbsolutelyContinuous.mk (fun s hs h0 => ?_)
  rw [Measure.map_apply hmeas hs]
  exact elemShear_preimage_null a b c hab hac h0

end ElemShear

/-- **`flatElemShear a b c` is QMP** (given `a ≠ b`, `a ≠ c`): conjugate `elemShear_qmp` by the
measure-preserving flattening CLE (whose forward/inverse coes agree with `paramsEquivFlat`'s). -/
theorem flatElemShear_qmp (a b c : Fin (flatDim M)) (hab : a ≠ b) (hac : a ≠ c) :
    Measure.QuasiMeasurePreserving (flatElemShear (M := M) a b c)
      (volume : Measure (Params M)) volume := by
  have hcomp := ((paramsEquivFlatCLE_symm_qmp M).comp (elemShear_qmp a b c hab hac)).comp
    (paramsEquivFlatCLE_qmp M)
  have hEq : (⇑(paramsEquivFlatCLE M).symm ∘ elemShear a b c) ∘ ⇑(paramsEquivFlatCLE M)
      = flatElemShear (M := M) a b c := by
    funext w
    simp only [Function.comp_apply, flatElemShear, paramsEquivFlatCLE_coe,
      paramsEquivFlatCLE_symm_coe]
  rwa [hEq] at hcomp

/-- **`flatElemShear a b c` is injective** (given `a ≠ b`, `a ≠ c`): a conjugate of the bijective
`elemShearHomeomorph`. -/
theorem flatElemShear_injective (a b c : Fin (flatDim M)) (hab : a ≠ b) (hac : a ≠ c) :
    Function.Injective (flatElemShear (M := M) a b c) := fun x y hxy => by
  have h1 := (paramsEquivFlat M).symm.injective hxy
  have h2 := (elemShearHomeomorph a b c hab hac).injective h1
  exact (paramsEquivFlat M).injective h2

/-- A `foldr (· ∘ ·) id` of QMP maps is QMP. -/
theorem foldrComp_qmp (maps : List (Params M → Params M))
    (hmaps : ∀ f ∈ maps, Measure.QuasiMeasurePreserving f (volume : Measure (Params M)) volume) :
    Measure.QuasiMeasurePreserving (maps.foldr (· ∘ ·) id) (volume : Measure (Params M)) volume := by
  induction maps with
  | nil => exact Measure.QuasiMeasurePreserving.id volume
  | cons f rest ih =>
    rw [List.foldr_cons]
    exact (hmaps f List.mem_cons_self).comp (ih fun g hg => hmaps g (List.mem_cons_of_mem f hg))

/-- A `foldr (· ∘ ·) id` of injective maps is injective. -/
theorem foldrComp_injective (maps : List (Params M → Params M))
    (hmaps : ∀ f ∈ maps, Function.Injective f) :
    Function.Injective (maps.foldr (· ∘ ·) id) := by
  induction maps with
  | nil => exact Function.injective_id
  | cons f rest ih =>
    rw [List.foldr_cons]
    exact (hmaps f List.mem_cons_self).comp (ih fun g hg => hmaps g (List.mem_cons_of_mem f hg))

/-- A `foldr (· ∘ ·) id` of differentiable maps is differentiable. -/
theorem foldrComp_differentiable (maps : List (Params M → Params M))
    (hmaps : ∀ f ∈ maps, Differentiable ℝ f) :
    Differentiable ℝ (maps.foldr (· ∘ ·) id) := by
  induction maps with
  | nil => exact differentiable_id
  | cons f rest ih =>
    rw [List.foldr_cons]
    exact (hmaps f List.mem_cons_self).comp (ih fun g hg => hmaps g (List.mem_cons_of_mem f hg))

/-- **The interior-block Schur fold is QMP** — a composition of QMP `flatElemShear`s
(`schurCells_ne` supplies the side conditions). -/
theorem residualSchurShear_qmp (node : StepData M) (rows cols : ℕ) :
    Measure.QuasiMeasurePreserving (residualSchurShear node rows cols)
      (volume : Measure (Params M)) volume := by
  rw [residualSchurShear, schurMaps]
  refine foldrComp_qmp _ (fun f hf => ?_)
  rw [List.mem_map] at hf
  obtain ⟨abc, hmem, rfl⟩ := hf
  obtain ⟨hab, hac⟩ := schurCells_ne node rows cols abc hmem
  exact flatElemShear_qmp abc.1 abc.2.1 abc.2.2 hab hac

/-- **The interior-block Schur fold is injective** — a composition of injective `flatElemShear`s. -/
theorem residualSchurShear_injective (node : StepData M) (rows cols : ℕ) :
    Function.Injective (residualSchurShear node rows cols) := by
  rw [residualSchurShear, schurMaps]
  refine foldrComp_injective _ (fun f hf => ?_)
  rw [List.mem_map] at hf
  obtain ⟨abc, hmem, rfl⟩ := hf
  obtain ⟨hab, hac⟩ := schurCells_ne node rows cols abc hmem
  exact flatElemShear_injective abc.1 abc.2.1 abc.2.2 hab hac

/-- **`alphaGauge g` is QMP** — `id` (case-1(1)/rollover) or the interior Schur fold. -/
theorem alphaGauge_qmp (g : GeoChart M) :
    Measure.QuasiMeasurePreserving (alphaGauge (M := M) g) (volume : Measure (Params M)) volume := by
  unfold alphaGauge
  split
  · exact Measure.QuasiMeasurePreserving.id volume
  · exact Measure.QuasiMeasurePreserving.id volume
  · exact residualSchurShear_qmp _ _ _
  · exact residualSchurShear_qmp _ _ _

/-- **`alphaGauge g` is injective** — `id` or the injective interior Schur fold. -/
theorem alphaGauge_injective (g : GeoChart M) :
    Function.Injective (alphaGauge (M := M) g) := by
  unfold alphaGauge
  split
  · exact Function.injective_id
  · exact Function.injective_id
  · exact residualSchurShear_injective _ _ _
  · exact residualSchurShear_injective _ _ _

/-! ## The per-factor properties of `geoChartMapNorm alphaGauge` and the fold -/

/-- **On the reachable cone, `geoChartMapNorm gauge = geoChartMapNorm (fun _ => id) ∘ gauge`** — the
composable source gauge is applied innermost, so post-composing the id-atlas factor with the gauge
recovers the gauge-atlas factor (both `dite`s discharge; `∘ id` collapses on the id side). -/
theorem geoChartMapNorm_eq_id_comp_gauge_on_cone (gauge : GeoChart M → Params M → Params M)
    (node : StepData M) (edge : Edge M) (pivot : ℕ)
    (hd : dCenterOfNode M node ≤ flatDim M) (hp : pivot < dCenterOfNode M node) :
    geoChartMapNorm gauge ⟨node, edge, pivot⟩
      = geoChartMapNorm (fun _ => id) ⟨node, edge, pivot⟩ ∘ gauge ⟨node, edge, pivot⟩ := by
  rw [geoChartMapNorm_id_on_cone node edge pivot hd hp]
  unfold geoChartMapNorm
  rw [dif_pos hd, dif_pos hp, geoChartMap_on_cone node edge pivot hd hp]
  rfl

/-- **Each α per-edge factor is QMP** — off-cone `id`; on-cone `(id-factor) ∘ alphaGauge`, both QMP. -/
theorem geoChartMapNorm_alpha_qmp (g : GeoChart M) :
    Measure.QuasiMeasurePreserving (geoChartMapNorm (alphaGauge (M := M)) g)
      (volume : Measure (Params M)) volume := by
  obtain ⟨node, edge, pivot⟩ := g
  by_cases hd : dCenterOfNode M node ≤ flatDim M
  · by_cases hp : pivot < dCenterOfNode M node
    · rw [geoChartMapNorm_eq_id_comp_gauge_on_cone alphaGauge node edge pivot hd hp]
      exact (geoChartMapNorm_id_qmp _).comp (alphaGauge_qmp _)
    · simp only [geoChartMapNorm, dif_pos hd, dif_neg hp]
      exact Measure.QuasiMeasurePreserving.id volume
  · simp only [geoChartMapNorm, dif_neg hd]
    exact Measure.QuasiMeasurePreserving.id volume

/-- **Each α per-edge factor is injective off a null set** — off-cone `id`; on-cone `(id-factor) ∘
alphaGauge` with `alphaGauge` injective (QMP) and the id-factor a.e.-injective (banked). -/
theorem geoChartMapNorm_alpha_ae_injOn (g : GeoChart M) :
    ∃ N : Set (Params M), volume N = 0 ∧
      Set.InjOn (geoChartMapNorm (alphaGauge (M := M)) g) (Set.univ \ N) := by
  obtain ⟨node, edge, pivot⟩ := g
  by_cases hd : dCenterOfNode M node ≤ flatDim M
  · by_cases hp : pivot < dCenterOfNode M node
    · rw [geoChartMapNorm_eq_id_comp_gauge_on_cone alphaGauge node edge pivot hd hp]
      exact comp_ae_injOn (alphaGauge_qmp _)
        (ae_injOn_of_injective (alphaGauge_injective _)) (geoChartMapNorm_id_ae_injOn _)
    · simp only [geoChartMapNorm, dif_pos hd, dif_neg hp]
      exact ae_injOn_of_injective Function.injective_id
  · simp only [geoChartMapNorm, dif_neg hd]
    exact ae_injOn_of_injective Function.injective_id

/-! ### The fold: every `geoAtlasNorm gauge` leaf `chartMap` is injective off a null set

A mutual induction over `tGeoG`/`fannedEdgesG` threading "`acc` is QMP and injective off a null set"
(mirror of `GeoInjFold.tGeo_ae_injOn`), generic in a gauge whose per-edge factor is QMP + a.e.-inj. -/

mutual
/-- Every `tGeoG gauge acc t` leaf `chartMap` is injective off a null set, given `acc` QMP + inj off a
null set and the gauge's per-edge factor QMP + inj off a null set. -/
theorem tGeoG_ae_injOn (gauge : GeoChart M → Params M → Params M)
    (hgQMP : ∀ g, Measure.QuasiMeasurePreserving (geoChartMapNorm gauge g)
      (volume : Measure (Params M)) volume)
    (hgInj : ∀ g, ∃ N : Set (Params M), volume N = 0 ∧
      Set.InjOn (geoChartMapNorm gauge g) (Set.univ \ N))
    (acc : Params M → Params M)
    (haccQMP : Measure.QuasiMeasurePreserving acc (volume : Measure (Params M)) volume)
    (haccInj : ∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn acc (Set.univ \ N)) :
    ∀ t : ResolutionTree M, ∀ c ∈ ResolutionTree.leaves (tGeoG gauge acc t),
      ∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn c.chartMap (Set.univ \ N)
  | .leaf l => by
      intro c hc
      rw [tGeoG, ResolutionTree.leaves, List.mem_singleton] at hc
      subst hc
      exact haccInj
  | .branch n edges => by
      intro c hc
      rw [tGeoG, ResolutionTree.leaves] at hc
      exact fannedEdgesG_ae_injOn gauge hgQMP hgInj acc haccQMP haccInj n 0 edges c hc
/-- Companion of `tGeoG_ae_injOn` over an edge list. -/
theorem fannedEdgesG_ae_injOn (gauge : GeoChart M → Params M → Params M)
    (hgQMP : ∀ g, Measure.QuasiMeasurePreserving (geoChartMapNorm gauge g)
      (volume : Measure (Params M)) volume)
    (hgInj : ∀ g, ∃ N : Set (Params M), volume N = 0 ∧
      Set.InjOn (geoChartMapNorm gauge g) (Set.univ \ N))
    (acc : Params M → Params M)
    (haccQMP : Measure.QuasiMeasurePreserving acc (volume : Measure (Params M)) volume)
    (haccInj : ∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn acc (Set.univ \ N))
    (n : StepData M) (offset : ℕ) :
    ∀ edges : List (Edge M),
      ∀ c ∈ ResolutionTree.edgesLeaves (fannedEdgesG gauge acc n offset edges),
        ∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn c.chartMap (Set.univ \ N)
  | [] => by intro c hc; rw [fannedEdgesG] at hc; cases hc
  | .mk ec esub ch :: rest => by
      intro c hc
      rw [fannedEdgesG, edgesLeaves_append, List.mem_append] at hc
      rcases hc with hc | hc
      · by_cases hz : dCenterOfEdge n (Edge.mk ec esub ch) = 0
        · rw [if_pos hz] at hc
          simp only [ResolutionTree.edgesLeaves, List.append_nil] at hc
          exact tGeoG_ae_injOn gauge hgQMP hgInj acc haccQMP haccInj ch c hc
        · rw [if_neg hz, edgesLeaves_mapMk, List.mem_flatMap] at hc
          obtain ⟨p, _, hcp⟩ := hc
          refine tGeoG_ae_injOn gauge hgQMP hgInj
            (acc ∘ geoChartMapNorm gauge ⟨n, Edge.mk ec esub ch, offset + (p : ℕ)⟩) ?_ ?_ ch c hcp
          · exact haccQMP.comp (hgQMP _)
          · exact comp_ae_injOn (hgQMP _) (hgInj _) haccInj
      · exact fannedEdgesG_ae_injOn gauge hgQMP hgInj acc haccQMP haccInj n
          (offset + dCenterOfEdge n (Edge.mk ec esub ch)) rest c hc
end

/-- **Every `geoAtlasNorm alphaGauge t` piece's `chartMap` is injective off a null set** (the `acc = id`
specialization of `tGeoG_ae_injOn` at the α gauge). -/
theorem geoAtlasNorm_alpha_ae_injOn (t : ResolutionTree M) (c : LeafData M)
    (hc : c ∈ geoAtlasNorm (alphaGauge (M := M)) t) :
    ∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn c.chartMap (Set.univ \ N) := by
  rw [geoAtlasNorm] at hc
  exact tGeoG_ae_injOn alphaGauge geoChartMapNorm_alpha_qmp geoChartMapNorm_alpha_ae_injOn
    id (Measure.QuasiMeasurePreserving.id volume)
    (ae_injOn_of_injective Function.injective_id) t c hc

/-- **The `ChartBridge` a.e.-injectivity clause for every built-tree `geoAtlasNorm alphaGauge` piece**
(restrict the `univ \ N` form to `srcBox \ N`). Transfers `geoAtlas_leaf_ae_injOn` to the α atlas. -/
theorem geoAtlasNorm_leaf_ae_injOn (c : LeafData M)
    (hc : c ∈ geoAtlasNorm (alphaGauge (M := M))
      (buildTree M (conOracle M) (conRoot : ConState L))) :
    ∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn c.chartMap (c.srcBox \ N) := by
  obtain ⟨N, hN0, hNInj⟩ := geoAtlasNorm_alpha_ae_injOn _ c hc
  exact ⟨N, hN0, hNInj.mono (Set.diff_subset_diff_left (Set.subset_univ c.srcBox))⟩

/-! ## The gauge-parametric fold-Jacobian cocycle (2d walk, tick-343 reads-based bundle)

The `LeafJacobian` transfer to the α atlas. The id-atlas cocycle (`GeoFoldRegroup.geoAtlas_cocycle`)
walks `tGeo acc`; the α atlas is `tGeoG alphaGauge id`. We build the GAUGE-PARAMETRIC cocycle
`geoAtlasNorm_cocycle` over `tGeoG gauge acc` for any gauge satisfying a three-part bundle
(differentiable · det-1 · reads-neutral), then instantiate at `alphaGauge` — the id maintenance atoms
(`ledger_det_maintenance_*`, generic in `acc`) are reused verbatim via a thin gauge wrapper; the one new
proof is reads-neutrality (α fixes the child's birth diagonals). The id atlas is untouched (one spine:
the maintenance mechanism is shared; the walk skeleton mirrors, since `tGeoG ≠ tGeo` as constants). -/

/-- **`alphaGauge g` is differentiable** — `id` (case-1(1)/rollover) or the interior Schur fold (each a
`flatElemShear`, differentiable everywhere). Needed for the chain-rule split in the gauge cocycle. -/
theorem alphaGauge_differentiable (g : GeoChart M) :
    Differentiable ℝ (alphaGauge (M := M) g) := by
  unfold alphaGauge
  split
  · exact differentiable_id
  · exact differentiable_id
  all_goals
    · rw [residualSchurShear, schurMaps]
      refine foldrComp_differentiable _ (fun f hf => ?_)
      rw [List.mem_map] at hf
      obtain ⟨abc, _, rfl⟩ := hf
      exact flatElemShear_differentiable abc.1 abc.2.1 abc.2.2

/-- **A flat coordinate not written by the interior Schur fold is fixed** (the reads-neutrality
workhorse): if `k` is never a `schurCells` target `a`, then `z_k(residualSchurShear w) = z_k(w)`
(`elemShearFold_fixed` via the conjugation flat read `residualSchur_flat_read`). -/
theorem residualSchurShear_fixes_of_not_mem (node : StepData M) (rows cols : ℕ)
    (k : Fin (flatDim M)) (hk : ∀ abc ∈ schurCells node rows cols, abc.1 ≠ k) (w : Params M) :
    paramsEquivFlat M (residualSchurShear node rows cols w) k = paramsEquivFlat M w k := by
  rw [residualSchur_flat_read]
  exact elemShearFold_fixed (schurCells node rows cols) (paramsEquivFlat M w) k hk

/-- **The reads-neutrality disjointness** (the ONE new proof of the 2d walk): at a step node whose
layer/cleared match a child state `child` (`node.layer = child.layer`, `child.cleared ≤ node.cleared + 1`
— true for the case-2 / case-1(2) births, `child.cleared = node.cleared + 1`), every interior Schur-shear
target `abc.1` (a cell at row `≥ node.cleared + 1` on the node's layer) is distinct from every child
divisor's birth diagonal `birthFlatCoord M child k h`. Direct from `birthFlatCoord_ne_diag_layer_cell`
(`DivBirthInv M child` freshness: a divisor at the current layer has cleared-coord `< child.cleared ≤
node.cleared + 1 ≤ row`). -/
theorem schurCells_fst_ne_birthFlatCoord (node : StepData M) (rows cols : ℕ) (child : ConState L)
    (h : 0 < flatDim M) (dinv : DivBirthInv M child) (k : Fin child.numDiv)
    (hlayer : node.layer = child.layer) (hcleared : child.cleared ≤ node.cleared + 1) :
    ∀ abc ∈ schurCells node rows cols, abc.1 ≠ birthFlatCoord M child k h := by
  intro abc hmem heq
  rw [schurCells] at hmem
  split at hmem
  · rename_i hguard
    rw [List.mem_flatMap] at hmem
    obtain ⟨i', -, hmem⟩ := hmem
    rw [List.mem_map] at hmem
    obtain ⟨j', -, rfl⟩ := hmem
    exact birthFlatCoord_ne_diag_layer_cell child dinv h k
      (sf := ⟨node.layer, hguard.choose⟩) hlayer
      (by have := i'.isLt; omega)
      (by have := i'.isLt; have := hguard.choose_spec.1; omega)
      (by have := j'.isLt; have := hguard.choose_spec.2; omega) heq.symm
  · exact (List.not_mem_nil hmem).elim

/-- **α reads-neutrality of the ledger monomial**: `alphaGauge g` fixes every child divisor's birth-
diagonal read, so the full-ledger monomial pulls back unchanged. `id` on the case-1(1) merge / rollover
(reads trivial); the interior Schur fold on case-1(2)/case-2 (`residualSchurShear_fixes_of_not_mem` +
`schurCells_fst_ne_birthFlatCoord`). Discharges the cocycle's `hgreads` bundle for `alphaGauge`. -/
theorem alphaGauge_ledgerMonomial_neutral (g : GeoChart M) (child : ConState L) (h : 0 < flatDim M)
    (dinv : DivBirthInv M child) (hlayer : g.node.layer = child.layer)
    (hcleared : child.cleared ≤ g.node.cleared + 1) (w : Params M) :
    ledgerMonomial M child h (alphaGauge (M := M) g w) = ledgerMonomial M child h w := by
  refine ledgerMonomial_eq_of_reads M child h (alphaGauge (M := M) g) w (fun k => ?_)
  rcases hce : g.edge.case with _ | _ | _ | _
  · simp only [alphaGauge, hce, id_eq]
  · simp only [alphaGauge, hce]
    exact residualSchurShear_fixes_of_not_mem g.node _ _ _
      (schurCells_fst_ne_birthFlatCoord g.node _ _ child h dinv k hlayer hcleared) w
  · simp only [alphaGauge, hce]
    exact residualSchurShear_fixes_of_not_mem g.node _ _ _
      (schurCells_fst_ne_birthFlatCoord g.node _ _ child h dinv k hlayer hcleared) w
  · simp only [alphaGauge, hce, id_eq]

/-- **`geoChartMapNorm gauge g` is differentiable** given `gauge g` differentiable — on-cone it is the
banked id-factor `∘ gauge g` (`geoChartMapNorm_eq_id_comp_gauge_on_cone`), off-cone / out-of-range it is
`id`. The gauge-parametric analog of `geoChartMapNorm_differentiable`. -/
theorem geoChartMapNorm_gauge_differentiable (gauge : GeoChart M → Params M → Params M) (g : GeoChart M)
    (hg : Differentiable ℝ (gauge g)) : Differentiable ℝ (geoChartMapNorm gauge g) := by
  obtain ⟨node, edge, pivot⟩ := g
  by_cases hd : dCenterOfNode M node ≤ flatDim M
  · by_cases hp : pivot < dCenterOfNode M node
    · rw [geoChartMapNorm_eq_id_comp_gauge_on_cone gauge node edge pivot hd hp]
      exact (geoChartMapNorm_differentiable _).comp hg
    · simp only [geoChartMapNorm, dif_pos hd, dif_neg hp]; exact differentiable_id
  · simp only [geoChartMapNorm, dif_neg hd]; exact differentiable_id

/-- **The gauge maintenance wrapper** (the 2d mechanism): lift an id-atlas maintenance conclusion
`|det D(acc ∘ B^id) w| = ledgerMonomial child w` to the gauge atlas
`|det D(acc ∘ B^gauge) w| = ledgerMonomial child w`. Via the on-cone factorization `B^gauge = B^id ∘
gauge g` (`geoChartMapNorm_eq_id_comp_gauge_on_cone`, associativity), the chain-rule det split
(`abs_det_fderiv_comp`), `|det D(gauge g)| = 1`, and reads-neutrality of the ledger. One spine: every case
reuses the (generic-in-`acc`) `ledger_det_maintenance_*` atom, wrapped identically. -/
theorem gauge_det_maintenance_wrapper (gauge : GeoChart M → Params M → Params M)
    (g : GeoChart M) (child : ConState L) (h : 0 < flatDim M) (acc : Params M → Params M)
    (hd : dCenterOfNode M g.node ≤ flatDim M) (hp : g.pivot < dCenterOfNode M g.node)
    (haccdiff : Differentiable ℝ acc) (hgaugediff : Differentiable ℝ (gauge g))
    (hgaugedet1 : ∀ w, |(fderiv ℝ (gauge g) w).det| = 1)
    (hreads : ∀ w, ledgerMonomial M child h (gauge g w) = ledgerMonomial M child h w)
    (hidmaint : ∀ w, |(fderiv ℝ (acc ∘ geoChartMapNorm (fun _ => id) g) w).det|
        = ledgerMonomial M child h w) :
    ∀ w, |(fderiv ℝ (acc ∘ geoChartMapNorm gauge g) w).det| = ledgerMonomial M child h w := by
  intro w
  rw [show acc ∘ geoChartMapNorm gauge g
        = (acc ∘ geoChartMapNorm (fun _ => id) g) ∘ gauge g from by
      obtain ⟨node, edge, pivot⟩ := g
      rw [geoChartMapNorm_eq_id_comp_gauge_on_cone gauge node edge pivot hd hp]; rfl,
    abs_det_fderiv_comp _ _ (haccdiff.comp (geoChartMapNorm_differentiable _)) hgaugediff w,
    hidmaint (gauge g w), hgaugedet1 w, mul_one, hreads w]

/-- **The gauge-parametric fold-Jacobian cocycle** (2d walk — the α-atlas analog of
`GeoFoldRegroup.geoAtlas_cocycle`, over `tGeoG gauge acc`). Given a gauge with the reads-based bundle
(`hgdiff` differentiable · `hgdet1` det-1 · `hgreads` reads-neutral), the incoming invariant
`|det D acc w| = ledgerMonomial s w` + `DivBirthInv`/`DivExpPos`, every `tGeoG gauge acc` leaf `p` of the
subtree from `s` is `leafOfState`-shaped at its own reachable terminal `s'` (exposed), with
`|det D p.chartMap w| = ledgerMonomial s' w`. `id` and `alphaGauge` both instantiate; the id maintenance
atoms are reused verbatim through `gauge_det_maintenance_wrapper` (rollover needs no gauge). -/
theorem geoAtlasNorm_cocycle (h : 0 < flatDim M)
    (gauge : GeoChart M → Params M → Params M)
    (hgdiff : ∀ g, Differentiable ℝ (gauge g))
    (hgdet1 : ∀ g w, |(fderiv ℝ (gauge g) w).det| = 1)
    (hgreads : ∀ (g : GeoChart M) (child : ConState L), DivBirthInv M child →
      g.node.layer = child.layer → child.cleared ≤ g.node.cleared + 1 →
      ∀ w, ledgerMonomial M child h (gauge g w) = ledgerMonomial M child h w) :
    ∀ (s : ConState L), DivBirthInv M s → DivExpPos s →
      ∀ (acc : Params M → Params M), Differentiable ℝ acc →
        (∀ w, |(fderiv ℝ acc w).det| = ledgerMonomial M s h w) →
        ∀ p ∈ ResolutionTree.leaves (tGeoG gauge acc (buildTree M (conOracle M) s)),
          ∃ s' : ConState L, DivBirthInv M s' ∧ DivExpPos s' ∧ Differentiable ℝ p.chartMap ∧
            p = { leafOfState M s' with chartMap := p.chartMap } ∧
            ∀ w, |(fderiv ℝ p.chartMap w).det| = ledgerMonomial M s' h w := by
  intro s
  induction s using (conRel_wf M).induction with
  | _ s ih =>
    intro inv expinv acc haccdiff haccdet p hp
    have close_terminal : conOracle M s = oracleTerminal M s →
        ∃ s' : ConState L, DivBirthInv M s' ∧ DivExpPos s' ∧ Differentiable ℝ p.chartMap ∧
          p = { leafOfState M s' with chartMap := p.chartMap } ∧
          ∀ w, |(fderiv ℝ p.chartMap w).det| = ledgerMonomial M s' h w := by
      intro hos
      rw [buildTree_terminal M (conOracle M) s (leafOfState M s) (leafOfState_rootLedger M s) hos,
        tGeoG] at hp
      simp only [ResolutionTree.leaves, List.mem_singleton] at hp
      subst hp
      exact ⟨s, inv, expinv, haccdiff, rfl, haccdet⟩
    by_cases h1 : L ≤ s.layer
    · exact close_terminal (by unfold conOracle; rw [dif_pos h1])
    · have hlive : s.layer < L := not_le.mp h1
      have hL1 : s.layer + 1 < L + 1 := by omega
      by_cases h2 : widthMinUpto M (s.layer + 1) ≤ s.cleared
      · -- ROLLOVER: chartless, ledger-neutral (no gauge — `acc` unchanged).
        have horacle : conOracle M s = rolloverDecision M s (le_of_lt hlive) h2 := by
          unfold conOracle; rw [dif_neg h1, dif_pos h2]
        rw [buildTree_step M (conOracle M) s (s.toStepData M 0 0)
            [⟨StepCase.rollover, ⟨id, 0, 0, 0, Fin.elim0⟩, s.stepRollover,
              conRel_stepRollover M s (le_of_lt hlive)⟩] horacle, tGeoG,
          ResolutionTree.leaves] at hp
        simp only [List.map_cons, List.map_nil] at hp
        have hpmem := mem_edgesLeaves_fannedG_chartless gauge acc (s.toStepData M 0 0) 0
          StepCase.rollover ⟨id, 0, 0, 0, Fin.elim0⟩ (buildTree M (conOracle M) s.stepRollover) p
          rfl hp
        exact ih s.stepRollover (conRel_stepRollover M s (le_of_lt hlive))
          (DivBirthInv_stepRollover s inv) (DivExpPos_stepRollover s expinv) acc haccdiff
          (ledger_det_maintenance_rollover M s h acc haccdet) p hpmem
      · have hlt : s.cleared < widthMinUpto M (s.layer + 1) := not_le.mp h2
        have hcap : s.cleared < layerCap M := lt_of_lt_of_le hlt (widthMinUpto_le_layerCap M _)
        have hrr1 : 1 ≤ widthMinUpto M s.layer - s.cleared := by
          have hmono : widthMinUpto M (s.layer + 1) ≤ widthMinUpto M s.layer :=
            widthMinUpto_mono M (Nat.le_succ _)
          omega
        have hrc1 : 1 ≤ M (⟨s.layer + 1, hL1⟩ : Fin (L + 1)) - s.cleared := by
          have hws : widthMinUpto M (s.layer + 1) ≤ M (⟨s.layer + 1, hL1⟩ : Fin (L + 1)) :=
            widthMinUpto_le _ (by simp)
          omega
        rcases hmin : ((List.finRange s.numDiv).filterMap (fun k =>
            if s.cleared + 1 ≤ s.divTilde k ∧ s.divTilde k + 1 ≤ widthMinUpto M s.layer
            then some (s.divTilde k) else none)).min? with _ | target
        · -- CASE-2: full residual block birth.
          have horacle : conOracle M s = case2Decision M s
              (widthMinUpto M s.layer - s.cleared) (M ⟨s.layer + 1, hL1⟩ - s.cleared) hcap := by
            unfold conOracle; rw [dif_neg h1, dif_neg h2]; split <;> simp_all only [reduceCtorEq]
          rw [buildTree_step M (conOracle M) s
              (s.toStepData M (widthMinUpto M s.layer - s.cleared)
                (M ⟨s.layer + 1, hL1⟩ - s.cleared))
              [⟨StepCase.case2, ⟨id, 0, 0, 0, Fin.elim0⟩,
                s.stepAppendAdvance ((widthMinUpto M s.layer - s.cleared)
                  * (M ⟨s.layer + 1, hL1⟩ - s.cleared)) (fun p => runMinWidth M p),
                conRel_stepAppendAdvance M s _ _ hcap⟩] horacle, tGeoG,
            ResolutionTree.leaves] at hp
          simp only [List.map_cons, List.map_nil] at hp
          set node := s.toStepData M (widthMinUpto M s.layer - s.cleared)
            (M ⟨s.layer + 1, hL1⟩ - s.cleared) with hnode_def
          set child2 := s.stepAppendAdvance ((widthMinUpto M s.layer - s.cleared)
            * (M ⟨s.layer + 1, hL1⟩ - s.cleared)) (fun p => runMinWidth M p) with hchild2_def
          have htree : buildTree M (conOracle M) s = ResolutionTree.branch node
              [Edge.mk StepCase.case2 ⟨id, 0, 0, 0, Fin.elim0⟩ (buildTree M (conOracle M) child2)] :=
            buildTree_step M (conOracle M) s node
              [⟨StepCase.case2, ⟨id, 0, 0, 0, Fin.elim0⟩, child2,
                conRel_stepAppendAdvance M s _ _ hcap⟩] horacle
          have hocc : nodeOccMin M node = none := by rw [nodeOccMin_toStepData]; exact hmin
          have hdim : dCenterOfNode M node = node.resRows * node.resCols :=
            dCenterOfNode_case2 M s _ _ hlive h2 hmin
          have hz : dCenterOfEdge node
              (Edge.mk StepCase.case2 ⟨id, 0, 0, 0, Fin.elim0⟩
                (buildTree M (conOracle M) child2)) ≠ 0 := by
            show node.resRows * node.resCols ≠ 0
            have : node.resRows * node.resCols = (widthMinUpto M s.layer - s.cleared)
              * (M ⟨s.layer + 1, hL1⟩ - s.cleared) := rfl
            rw [this]; exact Nat.mul_ne_zero (by omega) (by omega)
          obtain ⟨pp, hpplt, hpmem⟩ := mem_edgesLeaves_fannedG_charted gauge acc node 0
            StepCase.case2 ⟨id, 0, 0, 0, Fin.elim0⟩ (buildTree M (conOracle M) child2) p hz hp
          set g : GeoChart M := ⟨node, Edge.mk StepCase.case2 ⟨id, 0, 0, 0, Fin.elim0⟩
            (buildTree M (conOracle M) child2), 0 + pp⟩ with hg_def
          have hd : dCenterOfNode M g.node ≤ flatDim M := dCenterOfNode_le_flatDim s node _ htree
          have hpiv : g.pivot < dCenterOfNode M g.node := by
            show 0 + pp < dCenterOfNode M node
            have hde : dCenterOfEdge node (Edge.mk StepCase.case2 ⟨id, 0, 0, 0, Fin.elim0⟩
                (buildTree M (conOracle M) child2)) = node.resRows * node.resCols := rfl
            rw [Nat.zero_add, hdim, ← hde]; exact hpplt
          obtain ⟨hnl, hnc⟩ := step_node_layer_cleared s g.node _ htree
          have hc2l : child2.layer = s.layer := by simp only [hchild2_def, ConState.stepAppendAdvance]
          have hc2c : child2.cleared = s.cleared + 1 := by
            simp only [hchild2_def, ConState.stepAppendAdvance]
          exact ih child2 (conRel_stepAppendAdvance M s _ _ hcap)
            (DivBirthInv_stepAppendAdvance s _ _ hlive hlt inv)
            (DivExpPos_stepAppendAdvance s _ _
              (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))) expinv)
            (acc ∘ geoChartMapNorm gauge g)
            (haccdiff.comp (geoChartMapNorm_gauge_differentiable gauge g (hgdiff g)))
            (gauge_det_maintenance_wrapper gauge g child2 h acc hd hpiv haccdiff (hgdiff g)
              (fun w => hgdet1 g w)
              (hgreads g child2 (DivBirthInv_stepAppendAdvance s _ _ hlive hlt inv)
                (by omega) (by omega))
              (ledger_det_maintenance_case2 M s h inv g _ htree h2 hocc rfl hd hpiv
                (fun p => runMinWidth M p) acc haccdiff haccdet)) p hpmem
        · -- CASE-1 (or chooser fall-back terminal).
          rcases hf : chooseMin s target with _ | f
          · refine close_terminal ?_
            unfold conOracle
            rw [dif_neg h1, dif_neg h2]
            split <;> simp_all only [reduceCtorEq, Option.some.injEq]
            all_goals (try subst_vars)
            all_goals (try (split <;> simp_all only [reduceCtorEq]))
          · -- CASE-1 blow-up (merge + split children).
            have hgt : s.cleared < target := by
              obtain ⟨hmemtar, -⟩ := List.min?_eq_some_iff'.mp hmin
              rw [List.mem_filterMap] at hmemtar
              obtain ⟨k0, -, hk0⟩ := hmemtar
              by_cases hc0 : s.cleared + 1 ≤ s.divTilde k0 ∧
                  s.divTilde k0 + 1 ≤ widthMinUpto M s.layer
              · rw [if_pos hc0] at hk0
                have hdt : s.divTilde k0 = target := Option.some.inj hk0
                have := hc0.1; omega
              · rw [if_neg hc0] at hk0; exact absurd hk0 (by simp)
            set node := s.toStepData M (widthMinUpto M s.layer - s.cleared)
              (M ⟨s.layer + 1, hL1⟩ - s.cleared) with hnode_def
            set child11 : ConState L := ⟨s.layer, s.cleared, s.numDiv,
              (fun k => if (k : ℕ) = f.val
                then s.divExp k + (target - s.cleared) * (M ⟨s.layer + 1, hL1⟩ - s.cleared)
                else s.divExp k),
              Function.update s.divProfile f (setTail s.layer s.cleared (s.divProfile f)),
              s.numGen, s.genDivExp, s.divBirthCoord⟩ with hchild11_def
            set child12 := s.stepAppendAdvance
              (s.divExp f + (target - s.cleared) * (M ⟨s.layer + 1, hL1⟩ - s.cleared))
              (s.divProfile f) with hchild12_def
            have helig : s.divTilde f = s.cleared + (target - s.cleared) := by
              rw [(chooseMin_spec s target hf).1]; omega
            have hdesc11 : conRel M child11 s :=
              conRel_of_exp_change M (s.stepCase11 f) s _ s.numGen s.genDivExp
                (conRel_stepCase11 M s f hlive (by rw [(chooseMin_spec s target hf).1]; omega))
            have hdesc12 : conRel M child12 s :=
              conRel_stepAppendAdvance M s _ _ hcap
            have horacle : conOracle M s = case1Decision M s f (target - s.cleared)
                (widthMinUpto M s.layer - s.cleared) (M ⟨s.layer + 1, hL1⟩ - s.cleared)
                (not_le.mp h1) (by omega) helig hcap := by
              unfold conOracle
              rw [dif_neg h1, dif_neg h2]
              split
              · rename_i target' heq
                obtain rfl : target' = target := Option.some.inj (heq ▸ hmin)
                split
                · rename_i f' hf'
                  obtain rfl : f' = f := Option.some.inj (hf' ▸ hf)
                  rfl
                · rename_i hf'; exact absurd (hf' ▸ hf) (by simp)
              · rename_i heq; exact absurd (heq ▸ hmin) (by simp)
            have htree : buildTree M (conOracle M) s = ResolutionTree.branch node
                [Edge.mk StepCase.case11 ⟨id, target - s.cleared, f.val, 0, Fin.elim0⟩
                    (buildTree M (conOracle M) child11),
                  Edge.mk StepCase.case12 ⟨id, target - s.cleared, f.val, 0, Fin.elim0⟩
                    (buildTree M (conOracle M) child12)] :=
              buildTree_step M (conOracle M) s node
                [⟨StepCase.case11, ⟨id, target - s.cleared, f.val, 0, Fin.elim0⟩, child11, hdesc11⟩,
                  ⟨StepCase.case12, ⟨id, target - s.cleared, f.val, 0, Fin.elim0⟩, child12,
                    hdesc12⟩] horacle
            have hocc : nodeOccMin M node = some target := by
              rw [nodeOccMin_toStepData]; exact hmin
            have hd : dCenterOfNode M node ≤ flatDim M := dCenterOfNode_le_flatDim s node _ htree
            have hde1 : dCenterOfEdge node (Edge.mk StepCase.case11
                ⟨id, target - s.cleared, f.val, 0, Fin.elim0⟩
                (buildTree M (conOracle M) child11)) = 1 := rfl
            have hde2 : dCenterOfEdge node (Edge.mk StepCase.case12
                ⟨id, target - s.cleared, f.val, 0, Fin.elim0⟩
                (buildTree M (conOracle M) child12))
                = (target - s.cleared) * (M ⟨s.layer + 1, hL1⟩ - s.cleared) := rfl
            have hncol : node.resCols = M ⟨s.layer + 1, hL1⟩ - s.cleared := rfl
            have hsum : dCenterOfNode M node
                = 1 + (target - s.cleared) * (M ⟨s.layer + 1, hL1⟩ - s.cleared) :=
              dCenterOfNode_case1 M s _ _ target hlive h2 hmin
            have hsum2 : dCenterOfNode M node
                = dCenterOfEdge node (Edge.mk StepCase.case11
                    ⟨id, target - s.cleared, f.val, 0, Fin.elim0⟩ (buildTree M (conOracle M) child11))
                  + dCenterOfEdge node (Edge.mk StepCase.case12
                    ⟨id, target - s.cleared, f.val, 0, Fin.elim0⟩
                    (buildTree M (conOracle M) child12)) := by rw [hde1, hde2]; exact hsum
            have hb : dCenterOfNode M node
                = (target - s.cleared) * (M ⟨s.layer + 1, hL1⟩ - s.cleared) + 1 := by
              rw [hsum]; exact Nat.add_comm _ _
            have h0 : 0 < dCenterOfNode M node := by rw [hb]; exact Nat.succ_pos _
            have hcell0 : cNodeOf M node hd (⟨0, h0⟩ : Fin (dCenterOfNode M node))
                = birthFlatCoord M s f h :=
              cNode_index0_eq_birthFlatCoord M s inv node _ htree h2 target hocc h hd h0 f hf
            have hnl : node.layer = s.layer ∧ node.cleared = s.cleared :=
              step_node_layer_cleared s node _ htree
            rw [htree, tGeoG, ResolutionTree.leaves, fannedEdgesG, edgesLeaves_eq,
              List.flatMap_append, ← edgesLeaves_eq, ← edgesLeaves_eq, List.mem_append] at hp
            rcases hp with hp1 | hp2
            · -- the case-1(1) MERGE edge (pivot `0`).
              rw [if_neg (show dCenterOfEdge node (Edge.mk StepCase.case11
                    ⟨id, target - s.cleared, f.val, 0, Fin.elim0⟩
                    (buildTree M (conOracle M) child11)) ≠ 0 from one_ne_zero),
                edgesLeaves_mapMk, List.mem_flatMap] at hp1
              obtain ⟨pp, hppmem, hcp⟩ := hp1
              have hpp0 : pp = 0 := by
                rw [List.bind_eq_flatMap, List.mem_flatMap] at hppmem
                obtain ⟨a, -, ha⟩ := hppmem
                rw [List.mem_pure] at ha
                have hai : (a : ℕ) < 1 := a.isLt
                omega
              set g1 : GeoChart M := ⟨node, Edge.mk StepCase.case11
                ⟨id, target - s.cleared, f.val, 0, Fin.elim0⟩
                (buildTree M (conOracle M) child11), 0 + pp⟩ with hg1_def
              have hpiv1 : g1.pivot < dCenterOfNode M g1.node := by
                show 0 + pp < dCenterOfNode M node; rw [hpp0]; simpa using h0
              have hpivcell : cNodeOf M g1.node hd (⟨g1.pivot, hpiv1⟩ : Fin (dCenterOfNode M g1.node))
                  = birthFlatCoord M s f h := by
                rw [show (⟨g1.pivot, hpiv1⟩ : Fin (dCenterOfNode M node)) = ⟨0, h0⟩ from
                  Fin.ext (by show 0 + pp = 0; rw [hpp0])]
                exact hcell0
              exact ih child11 hdesc11 (DivBirthInv_stepCase11 s f inv)
                (DivExpPos_bumpedExp s f _ expinv)
                (acc ∘ geoChartMapNorm gauge g1)
                (haccdiff.comp (geoChartMapNorm_gauge_differentiable gauge g1 (hgdiff g1)))
                (gauge_det_maintenance_wrapper gauge g1 child11 h acc hd hpiv1 haccdiff (hgdiff g1)
                  (fun w => hgdet1 g1 w)
                  (hgreads g1 child11 (DivBirthInv_stepCase11 s f inv)
                    (by rw [hnl.1]) (by rw [hnl.2]; exact Nat.le_succ _))
                  (ledger_det_maintenance_case11 M s h inv g1 _ htree h2 rfl f (expinv f) rfl
                    target hocc hf _ hb hd hpiv1 hpivcell acc haccdiff haccdet)) p hcp
            · -- the case-1(2) SPLIT edge (pivot `≥ 1`).
              have hz2 : dCenterOfEdge node (Edge.mk StepCase.case12
                  ⟨id, target - s.cleared, f.val, 0, Fin.elim0⟩
                  (buildTree M (conOracle M) child12)) ≠ 0 := by
                rw [hde2]; exact Nat.mul_ne_zero (by omega) (by omega)
              obtain ⟨pp, hpplt, hcp⟩ := mem_edgesLeaves_fannedG_charted gauge acc node
                (0 + dCenterOfEdge node (Edge.mk StepCase.case11
                  ⟨id, target - s.cleared, f.val, 0, Fin.elim0⟩
                  (buildTree M (conOracle M) child11)))
                StepCase.case12 ⟨id, target - s.cleared, f.val, 0, Fin.elim0⟩
                (buildTree M (conOracle M) child12) p hz2 hp2
              set g2 : GeoChart M := ⟨node, Edge.mk StepCase.case12
                ⟨id, target - s.cleared, f.val, 0, Fin.elim0⟩
                (buildTree M (conOracle M) child12),
                (0 + dCenterOfEdge node (Edge.mk StepCase.case11
                  ⟨id, target - s.cleared, f.val, 0, Fin.elim0⟩
                  (buildTree M (conOracle M) child11))) + pp⟩ with hg2_def
              have hpiv2 : g2.pivot < dCenterOfNode M g2.node := by
                show (0 + dCenterOfEdge node (Edge.mk StepCase.case11
                    ⟨id, target - s.cleared, f.val, 0, Fin.elim0⟩
                    (buildTree M (conOracle M) child11))) + pp < dCenterOfNode M node
                rw [hsum2, hde1]; omega
              have hucell : ∃ i : Fin (dCenterOfNode M g2.node),
                  i ≠ (⟨g2.pivot, hpiv2⟩ : Fin (dCenterOfNode M g2.node))
                  ∧ cNodeOf M g2.node hd i = birthFlatCoord M s f h := by
                refine ⟨⟨0, h0⟩, ?_, hcell0⟩
                intro hcontra
                have hval : (0 : ℕ) = g2.pivot := congrArg Fin.val hcontra
                have hpv : g2.pivot = (0 + dCenterOfEdge node (Edge.mk StepCase.case11
                    ⟨id, target - s.cleared, f.val, 0, Fin.elim0⟩
                    (buildTree M (conOracle M) child11))) + pp := rfl
                rw [hpv, hde1] at hval; omega
              obtain ⟨hnl2, hnc2⟩ := step_node_layer_cleared s g2.node _ htree
              have hc12l : child12.layer = s.layer := by
                simp only [hchild12_def, ConState.stepAppendAdvance]
              have hc12c : child12.cleared = s.cleared + 1 := by
                simp only [hchild12_def, ConState.stepAppendAdvance]
              exact ih child12 hdesc12 (DivBirthInv_stepAppendAdvance s _ _ hlive hlt inv)
                (DivExpPos_stepAppendAdvance s _ _
                  (le_add_left (Nat.one_le_iff_ne_zero.mpr
                    (Nat.mul_ne_zero (by omega) (by omega)))) expinv)
                (acc ∘ geoChartMapNorm gauge g2)
                (haccdiff.comp (geoChartMapNorm_gauge_differentiable gauge g2 (hgdiff g2)))
                (gauge_det_maintenance_wrapper gauge g2 child12 h acc hd hpiv2 haccdiff (hgdiff g2)
                  (fun w => hgdet1 g2 w)
                  (hgreads g2 child12 (DivBirthInv_stepAppendAdvance s _ _ hlive hlt inv)
                    (by omega) (by omega))
                  (ledger_det_maintenance_case12 M s h inv g2 _ htree h2 rfl f (expinv f)
                    target hocc hf _ hb hd hpiv2 hucell (s.divProfile f) acc haccdiff haccdet)) p hcp

/-! ## The two owed transfers (frontier)

Two `(B)`/`(A)` conjuncts of the faithful discharge are NOT clean mirrors of their id-atlas forms and
are OWED here as transfer-owed sorries (each removed by the final batch when its route lands). Both are
surfaced to the controller/elder (t14 encore, this respawn). -/

/-- **CLAUSE (A) COVER over the α atlas — TRANSFER OWED** (surfaced: cover open-homeo route).
The id-atlas cover `geoAtlas_imageCover` covers the flat cube via the R = 1 pivot self-cover
(`node_selfCover`). The α atlas composes each per-edge chart with `alphaGauge` (innermost); `alphaGauge`
is an open homeomorphism fixing `0` but does NOT preserve the cube (`alphaGauge_srcBox_bounded`:
`α⁻¹'(cube R) ⊆ cube(R(1+R))`), so `α '' cube(1) ⊇ cube(ρ)` only for the golden `ρ = (√5−1)/2`. The
NAIVE quantitative shrink FAILS: the pivot self-cover at radius `ρ < 1` does NOT hold — `pivotChart`
needs the RATIOS at radius 1 (`pivotChartDom i R = {|u_i| ≤ R, |u_k| ≤ 1}`), and shrinking all
coordinates to `ρ` breaks coverage (`⋃_i pivotChart_i '' cube(ρ)` is not a `0`-neighbourhood). The
viable route is α-as-SPECTATOR (α's `schurCells` interior-residual target cells disjoint from the
node's blown-up center coords `cNodeOf`, so the center self-cover stays at R = 1 while the spectator
constraint stays a `0`-nbhd) — but that is a NEW geometric argument (needs `schurCells ⊥ cNodeOf`
through `centerSelCase`/the swap `S`), not a shrink of the existing proof. STOP-AND-SURFACEd per the
brief; route pending elder ruling. -/
theorem geoAtlasNorm_imageCover (t : ResolutionTree M) (s : ConState L)
    (htree : t = buildTree M (conOracle M) s) :
    ∃ U : Set (Params M), IsOpen U ∧ (0 : Params M) ∈ U ∧
      U ⊆ ⋃ c ∈ geoAtlasNorm (alphaGauge (M := M)) t, c.chartMap '' c.srcBox := by
  sorry -- transfer owed: geoAtlasNorm_imageCover (cover open-homeo route; SURFACED, route pending)

/-- **The R7 `LeafJacobian` discharge over the α atlas** (2d walk — the transfer, DISCHARGED). Every
`geoAtlasNorm alphaGauge` piece `c` (over `conRoot`) satisfies the full-ledger `LeafJacobian`, exactly as
the id-atlas `geoAtlas_leaf_leafJacobian` does — instantiate `geoAtlasNorm_cocycle` at `conRoot`/`id`
with the `alphaGauge` bundle (`alphaGauge_differentiable` · `alphaGauge_abs_det_one` ·
`alphaGauge_ledgerMonomial_neutral`). The witness (`β := c.chartMap`, `ψ := id`, `fc := birthFlatCoord s'`,
`emb := (t0Indices s').get`) and every conjunct are the id-atlas ones — the α gauge only reparametrizes
the source, leaving the full-ledger monomial identity intact. Fills the R7 `LeafJacobian` frontier of
`chartBridgeFaithful_buildTree` over the faithful (α-normalized) atlas. -/
theorem geoAtlasNorm_leaf_leafJacobian (h : 0 < flatDim M) (c : LeafData M)
    (hc : c ∈ geoAtlasNorm (alphaGauge (M := M))
      (buildTree M (conOracle M) (conRoot : ConState L))) :
    LeafJacobian c := by
  have id_det : ∀ w, |(fderiv ℝ (id : Params M → Params M) w).det|
      = ledgerMonomial M (conRoot : ConState L) h w := by
    intro w
    rw [ledgerMonomial_conRoot, fderiv_id, show (ContinuousLinearMap.id ℝ (Params M)).det
        = LinearMap.det (ContinuousLinearMap.id ℝ (Params M)).toLinearMap from rfl]
    simp [LinearMap.det_id]
  have abs_det_id : |(ContinuousLinearMap.id ℝ (Params M)).det| = 1 := by
    rw [show (ContinuousLinearMap.id ℝ (Params M)).det
        = LinearMap.det (ContinuousLinearMap.id ℝ (Params M)).toLinearMap from rfl]
    simp [LinearMap.det_id]
  rw [geoAtlasNorm] at hc
  obtain ⟨s', hinv', hexp', hdiff, hshape, hident⟩ :=
    geoAtlasNorm_cocycle h alphaGauge alphaGauge_differentiable
      (fun g w => alphaGauge_abs_det_one g w)
      (fun g child dinv hlayer hcleared w =>
        alphaGauge_ledgerMonomial_neutral g child h dinv hlayer hcleared w)
      conRoot DivBirthInv_conRoot DivExpPos_conRoot id differentiable_id id_det c hc
  have hget : Function.Injective (t0Indices s').get :=
    ((List.nodup_finRange s'.numDiv).filter _).injective_get
  rw [hshape, leafOfState, dif_pos h]
  refine ⟨c.chartMap, id, id, fun w => fderiv ℝ c.chartMap w,
    fun _ => ContinuousLinearMap.id ℝ (Params M), 1, 1,
    fun j => birthFlatCoord M s' j h, fun i => (t0Indices s').get i,
    one_pos, birthFlatCoord_injective hinv', hget, fun k => rfl, fun k => rfl, fun j => hexp' j,
    ?_, fun w _ => rfl, fun w _ => ⟨(hdiff w).hasFDerivAt, by rw [hident w, ledgerMonomial]⟩,
    fun v _ => ⟨rfl, rfl, hasFDerivAt_id v, abs_det_id.ge, abs_det_id.le⟩⟩
  rw [Set.range_eq_empty (f := (Fin.elim0 : Fin 0 → Fin (flatDim M)))]
  exact disjoint_bot_right

/-! ## 2a Phase-1 atoms: the ENLARGED-CUBE cover (radius thread ρ_{n+1} = ρ_n(1+ρ_n), root ρ_0 = 1)

Design record: compass fork 15 amendment 5 + the elder's round-3 ruling + cert §7
(`threads/24-alpha-cover/cert-alpha-cover-hunt.md`). The `srcBox=cube(1)` cover is FALSE (the gap
point `y=(t,t,t,t)`); the enlarged-cube route KEEPS the cube and only grows its radius — the α's are
NEVER composed (no `gAcc` pullback). Two Phase-1 atoms + the surjectivity/inverse-shear rearrangement;
the `tGeoG` radius thread + the reachability induction + the `2b` re-bank are Phase-2 (sequenced after
walk-t20 + loss-t15 land, to avoid re-typing their live lanes). -/

/-- **The pivot chart domain sits in the cube at radius `R ≥ 1`** (the ratios are `≤ 1 ≤ R`). -/
theorem pivotChartDom_subset_cubeBox {d : ℕ} (i : Fin d) {R : ℝ} (hR : 1 ≤ R) :
    pivotChartDom i R ⊆ cubeBox d R := by
  intro u hu
  obtain ⟨hui, hratio⟩ := hu
  rw [cubeBox, Set.mem_pi]
  intro k _
  rw [Set.mem_Icc, ← abs_le]
  by_cases hk : k = i
  · subst hk; exact hui
  · exact le_trans (hratio k hk) hR

/-- **The pivot charts self-cover the cube at radius `R ≥ 1`** — the `∀R` domain self-cover
(`cubeBox_subset_iUnion_pivotChart_image`) with the domains widened to the full cube (`R ≥ 1`, so the
ratio bound `≤ 1` is absorbed). -/
theorem cubeBox_subset_iUnion_pivotChart_image_cubeBox {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 1 ≤ R) :
    cubeBox d R ⊆ ⋃ i : Fin d, pivotChart i '' cubeBox d R :=
  (cubeBox_subset_iUnion_pivotChart_image hd (le_trans zero_le_one hR)).trans
    (Set.iUnion_mono fun i => Set.image_mono (pivotChartDom_subset_cubeBox i hR))

/-- **The center split preserves the cube at any radius `R`** (`qOfCenter_preimage_cubeBox`
generalized off `R = 1` — the split just reindexes flat coordinates by `centerPerm`, and the cube
`[-R,R]^N` is permutation-invariant). -/
theorem qOfCenter_preimage_cubeBox_R {d : ℕ} (c : Fin d → Fin (flatDim M))
    (hinj : Function.Injective c) {R : ℝ} :
    (qOfCenter M c hinj) ⁻¹' (cubeBox d R ×ˢ cubeBox (flatDim M - d) R)
      = ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R := by
  ext w
  simp only [Set.mem_preimage, Set.mem_prod, cubeBox, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Icc, ← abs_le, qOfCenter, Homeomorph.trans_apply,
    Homeomorph.sumArrowHomeomorphProdArrow_apply, Function.comp_apply,
    Homeomorph.piCongrLeft_apply, Equiv.piCongrLeft'_symm, Equiv.symm_symm,
    Equiv.piCongrLeft'_apply, ContinuousLinearEquiv.coe_toHomeomorph, paramsEquivFlatCLE_coe]
  set e := centerPerm M c hinj with he
  clear_value e
  rw [e.forall_congr_left (p := fun a => |(paramsEquivFlat M) w a| ≤ R), Sum.forall]

/-- **The R ≥ 1 node self-cover** (⊇ form): at a reachable node, the `dCenterOfNode`-many
`qNodeOf`-conjugated pivot charts, applied to the flat cube of radius `R`, cover it. Mirror of
`node_selfCover` at general `R ≥ 1` (the center coords tile by the `R ≥ 1` self-cover, the spectator
cube passes through, `qOfCenter_preimage_cubeBox_R` transports back). The radius-threaded tiling
induction (Phase-2) folds this at each node's own `ρ_n`. -/
theorem node_selfCover_ge (node : StepData M) (hd : dCenterOfNode M node ≤ flatDim M)
    (hdpos : 0 < dCenterOfNode M node) {R : ℝ} (hR : 1 ≤ R) :
    ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R ⊆
      ⋃ (i : Fin (dCenterOfNode M node)),
        (fun w => (qNodeOf M node hd).symm (Prod.map (pivotChart i) id (qNodeOf M node hd w)))
          '' (⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R) := by
  have hqc : (qNodeOf M node hd) ⁻¹'
      (cubeBox (dCenterOfNode M node) R ×ˢ cubeBox (flatDim M - dCenterOfNode M node) R)
      = ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R := by
    rw [qNodeOf]
    exact qOfCenter_preimage_cubeBox_R (cNodeOf M node hd) (cNodeOf_injective M node hd)
  rw [← hqc]
  have key : ∀ i : Fin (dCenterOfNode M node),
      (fun w => (qNodeOf M node hd).symm (Prod.map (pivotChart i) id (qNodeOf M node hd w)))
          '' ((qNodeOf M node hd) ⁻¹'
              (cubeBox (dCenterOfNode M node) R ×ˢ cubeBox (flatDim M - dCenterOfNode M node) R))
        = (qNodeOf M node hd).symm ''
            ((pivotChart i '' cubeBox (dCenterOfNode M node) R)
              ×ˢ cubeBox (flatDim M - dCenterOfNode M node) R) := by
    intro i
    rw [show (fun w => (qNodeOf M node hd).symm (Prod.map (pivotChart i) id (qNodeOf M node hd w)))
          = ⇑(qNodeOf M node hd).symm ∘ (Prod.map (pivotChart i) id) ∘ ⇑(qNodeOf M node hd) from rfl,
      Set.image_comp, Set.image_comp, (qNodeOf M node hd).image_preimage, Set.prodMap_image_prod,
      Set.image_id]
  simp_rw [key]
  rw [← Set.image_iUnion, ← Set.iUnion_prod_const, ← Homeomorph.image_symm]
  exact Set.image_mono (Set.prod_mono
    (cubeBox_subset_iUnion_pivotChart_image_cubeBox hdpos hR) (le_refl _))

/-! ### Surjectivity of the α gauge + the ⊇ inverse-shear rearrangement -/

/-- A `foldr (· ∘ ·) id` of surjective maps is surjective. -/
theorem foldrComp_surjective (maps : List (Params M → Params M))
    (hmaps : ∀ f ∈ maps, Function.Surjective f) :
    Function.Surjective (maps.foldr (· ∘ ·) id) := by
  induction maps with
  | nil => exact Function.surjective_id
  | cons f rest ih =>
    rw [List.foldr_cons]
    exact (hmaps f List.mem_cons_self).comp (ih fun g hg => hmaps g (List.mem_cons_of_mem f hg))

/-- **`flatElemShear a b c` is surjective** (given `a ≠ b`, `a ≠ c`): a conjugate of the bijective
`elemShearHomeomorph`. -/
theorem flatElemShear_surjective (a b c : Fin (flatDim M)) (hab : a ≠ b) (hac : a ≠ c) :
    Function.Surjective (flatElemShear (M := M) a b c) := fun y => by
  obtain ⟨z, hz⟩ := (elemShearHomeomorph a b c hab hac).surjective (paramsEquivFlat M y)
  have hz' : elemShear a b c z = paramsEquivFlat M y := hz
  exact ⟨(paramsEquivFlat M).symm z, by
    rw [flatElemShear, (paramsEquivFlat M).apply_symm_apply, hz',
      (paramsEquivFlat M).symm_apply_apply]⟩

/-- **The interior-block Schur fold is surjective** — a composition of surjective `flatElemShear`s. -/
theorem residualSchurShear_surjective (node : StepData M) (rows cols : ℕ) :
    Function.Surjective (residualSchurShear node rows cols) := by
  rw [residualSchurShear, schurMaps]
  refine foldrComp_surjective _ (fun f hf => ?_)
  rw [List.mem_map] at hf
  obtain ⟨abc, hmem, rfl⟩ := hf
  obtain ⟨hab, hac⟩ := schurCells_ne node rows cols abc hmem
  exact flatElemShear_surjective abc.1 abc.2.1 abc.2.2 hab hac

/-- **`alphaGauge g` is surjective** — `id` or the surjective interior Schur fold. -/
theorem alphaGauge_surjective (g : GeoChart M) :
    Function.Surjective (alphaGauge (M := M) g) := by
  unfold alphaGauge
  split
  · exact Function.surjective_id
  · exact Function.surjective_id
  · exact residualSchurShear_surjective _ _ _
  · exact residualSchurShear_surjective _ _ _

/-- **The ⊇ inverse-shear rearrangement** (the enlarged-cube cover's α step): the flat cube of radius
`R` sits inside the `alphaGauge g`-image of the cube of radius `R·(1+R)`. From
`alphaGauge_srcBox_bounded` (`α⁻¹'(cube R) ⊆ cube(R(1+R))`) + surjectivity: `cube R = α''(α⁻¹'(cube R))
⊆ α''(cube(R(1+R)))`. This is what lets a child covering `cube(ρ_{n+1})`, `ρ_{n+1}=ρ_n(1+ρ_n)`, cover
`cube(ρ_n)` through the innermost α. -/
theorem cubeBox_subset_alphaGauge_image (g : GeoChart M) {R : ℝ} (hR : 0 ≤ R) :
    ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R ⊆
      alphaGauge (M := M) g '' (⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) (R * (1 + R))) := by
  intro y hy
  obtain ⟨x, hx⟩ := alphaGauge_surjective g y
  refine ⟨x, alphaGauge_srcBox_bounded g hR ?_, hx⟩
  show alphaGauge (M := M) g x ∈ ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R
  rw [hx]; exact hy

/-! ### Phase 1.5: the leaf base-case monotonicity (Option C confirmation)

The reachability-induction leaf base case is `cube(ρ_leaf) ⊆ leafPathImages(…leaf…)`, and
`leafPathImages (.leaf l) = l.srcBox` (`PivotCoverFold`, NO `chartMap` applied — the fold's charts
enter only at branch `localSub`s). So the base case is `cube(ρ_leaf) ⊆ srcBox_leaf`, which under the
enlarged-cube leaf (`srcBox_leaf = cube(ρ_max)`, `ρ_leaf ≤ ρ_max`) closes by cube monotonicity below.
(Simpler than an `acc''srcBox` step — `acc` is never applied at the leaf.) -/

/-- **The cube is monotone in its radius** — the leaf base-case step. -/
theorem cubeBox_subset_cubeBox {d : ℕ} {R R' : ℝ} (hR : R ≤ R') :
    cubeBox d R ⊆ cubeBox d R' := by
  intro x hx
  rw [cubeBox, Set.mem_pi] at hx ⊢
  intro k hk
  have hxk := Set.mem_Icc.mp (hx k hk)
  exact Set.mem_Icc.mpr ⟨by linarith [hxk.1], by linarith [hxk.2]⟩

/-- **The flat cube is monotone in its radius** (the preimage form used at atlas leaves). -/
theorem flatCube_subset_flatCube {R R' : ℝ} (hR : R ≤ R') :
    ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R
      ⊆ ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R' :=
  Set.preimage_mono (cubeBox_subset_cubeBox hR)

end DLNFibre.DLN.RLCT.Engine
