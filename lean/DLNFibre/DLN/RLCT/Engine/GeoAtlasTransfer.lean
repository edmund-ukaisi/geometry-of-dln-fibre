import DLNFibre.DLN.RLCT.Engine.GeoAlphaGauge
import DLNFibre.DLN.RLCT.Engine.GeoLeafLedger
import DLNFibre.DLN.RLCT.Engine.GeoInjFold

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

/-- **The R7 `LeafJacobian` discharge over the α atlas — TRANSFER OWED** (mechanism pending elder
counter-sign, fork 15 (b)). t14's id-atlas `geoAtlas_leaf_leafJacobian` rides `geoAtlas_cocycle` (the
relative-Jacobian cocycle over `tGeo`, PROVEN concrete-at-id). The α fold threads `alphaGauge` PER-EDGE,
so the transfer is a per-edge det-1 commutation: the recommended mechanism GAUGE-GENERALIZES
`geoAtlas_cocycle` over an explicit "det-1 + divisor-diagonal-fixing gauge" hypothesis bundle (id and α
both instantiate — `alphaGauge_abs_det_one` is the det-1 side, and α fixes the divisor diagonal cells,
`GeoAlphaGauge` interior-only action). The bundle refactor + instantiation are HELD for the elder
counter-sign (the mechanism touches the banked cocycle arc); until then this is a signature pre-stage.
The fallback (if the atom refactor is not light): a standalone α-vs-id comparison lemma on top. -/
theorem geoAtlasNorm_leaf_leafJacobian (h : 0 < flatDim M) (c : LeafData M)
    (hc : c ∈ geoAtlasNorm (alphaGauge (M := M))
      (buildTree M (conOracle M) (conRoot : ConState L))) :
    LeafJacobian c := by
  sorry -- transfer owed: geoAtlasNorm_leaf_leafJacobian (gauge-generalized cocycle; walk in progress)

/-! ## 2d de-risking atoms (LeafJacobian gauge-generalization, tick-343 reads-based bundle)

The atoms-first probe (POSITIVE): the id maintenance atoms (`GeoFoldRegroup.ledger_det_maintenance_*`)
are generic in `acc`, so the gauge version is a THIN wrapper — `acc ∘ B^α = (acc ∘ B^id) ∘ α`
(`geoChartMapNorm_eq_id_comp_gauge_on_cone`), split by `abs_det_fderiv_comp`, `|det α| = 1`
(`alphaGauge_abs_det_one`), the id atom at point `α w`, then the reads-based neutrality
`ledgerMonomial child (α w) = ledgerMonomial child w` (α fixes the child's birth-diagonal read set;
the tick-343 correction — α writes interior FUTURE-pivot cells `> J`, fixes born diagonals `≤ J`). The
two reusable atoms below feed the wrapper + the neutrality. -/

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

end DLNFibre.DLN.RLCT.Engine
