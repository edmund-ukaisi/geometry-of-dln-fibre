import DLNFibre.Core.Aoyagi.PrincipalInv
import DLNFibre.Core.Aoyagi.ConjResolution
import DLNFibre.DLN.Aoyagi.LearningCoefficient

/-!
# `DLN.Aoyagi.MonumentAtlas` — the coupled monument: leaves L5–L8 + the composition driver

**BLUEPRINT (aoyagi-engine rung C; RESHAPED per the pnp-case1/pnp-cover verdicts + elder D1–D4).**
The DLN-side leaves of the coupled product-ideal resolution monument (charter §1.B) and the
composition **driver** that folds L1 + L3/L4 + `terminal_bezout` + L5 + L6 + L7 + L8 (+ the landed
leaf-2 `blowupResolution`) into `∃ res : Resolution (coreGen d e) 0, AtlasRealizesExponents d res` —
the residual goal of `exists_coreResolution` (`LearningCoefficient`) after
`exists_hlb_hattain_of_exists_atlasRealizesExponents`. The driver is sorried ONLY via the leaves
(`#print axioms` = `sorryAx` from exactly the leaf set).

## Wiring note for the controller (import cycle)

`exists_coreResolution` lives in `LearningCoefficient`; its residual goal speaks about `coreGen`/
`flatDim` (defined there), so a general-`d` driver that discharges it MUST sit DOWNSTREAM of
`LearningCoefficient` and cannot be called back into its in-place `sorry` without a cycle. This module
therefore provides both `exists_atlasRealizesExponents` (the residual goal, general `d`) and
`exists_coreResolution_via_monument` (the FULL `exists_coreResolution` statement, re-proved by
composition). The controller wires the canonical discharge (either promote this as canonical or reorg
`coreGen`/`flatDim` upstream) — see the report.

## Decorrelated-check gate (pnp-cover risk note; flagged at leaf 5)

The **pathwise coherence of the sheared tree fold** — the historically-masked `srcBox` seam: that the
per-branch step maps compose coherently along a root→leaf path, with each next center a coordinate
block in the accumulated sheared coordinates — is the gate for leaf 5's fold. It rides the explicit
`CenterCoordAligned` field of each `StepInvChild` (Core) and the two D3 named-gap hypotheses below; it is
the point to re-run the decorrelated check before striking leaf 5.
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-- The single monic dominant monomial `b₁(u) = ∏_d u_d^(E_d)` of an exponent vector `E`;
`(fun _ : Fin 1 ↦ monoOf E) = monomialFam (fun _ : Fin 1 ↦ E)` definitionally (the M'=1 compression).
-/
def monoOf {D : ℕ} (E : Fin D → ℕ) : (Fin D → ℝ) → ℝ := fun u ↦ ∏ i, (u i) ^ (E i)

/-! ## The geometric atlas carrier -/

/-- **One geometric recursion step** on `ℝᴰ` (shear-pin certificate): the step map `σ = sh ∘ blowupMap
p` bundled with its Jacobian exponent `jexp` and the shape certificates. `hσ_jac`: `|det Dσ|` is the
pure blow-up monomial `jacWeight jexp` (unit ≡ 1 — the shear is Jacobian-exactly-1). `hσ_inj`:
a.e.-injective off the exceptional monomial's zero set (the coordinate blocks). -/
structure GeoStep (D : ℕ) where
  /-- The step coordinate change (unipotent shear ∘ monomial blow-up). -/
  σ : (Fin D → ℝ) → (Fin D → ℝ)
  /-- The step's Jacobian monomial exponent. -/
  jexp : Fin D → ℕ
  /-- `σ` is analytic (a polynomial map). -/
  hσ_an : AnalyticOnNhd ℝ σ Set.univ
  /-- `σ` fixes the origin. -/
  hσ0 : σ 0 = 0
  /-- `|det Dσ| = jacWeight jexp` — a pure monomial, unit ≡ 1 (shear-pin §3). -/
  hσ_jac : ∀ u, |jacDet σ u| = jacWeight jexp u
  /-- `σ` is a.e.-injective off the exceptional monomial's zero set (coordinate blocks). -/
  hσ_inj : Set.InjOn σ (Set.univ \ {w : Fin D → ℝ | jacWeight jexp w = 0})

/-- **The geometric resolution atlas** produced by the fold (L5): `n` charts, each a root→leaf branch
of shear ∘ blow-up steps, with a compact source domain, an open certificate region, and the dominant
monomial / total Jacobian exponents. The path map of chart `c` is `pathMap` of its step σ's
(`gmap`). Well-formedness (topology, binding, unit-multiplicity/squarefreeness of `b₁`) is carried as
fields. -/
structure GeoAtlasData (d : Fin (N + 1) → ℕ) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) where
  /-- Number of geometric charts (root→leaf branches). -/
  n : ℕ
  /-- The atlas is nonempty. -/
  hn : 0 < n
  /-- Per-chart root→leaf step sequence (root = head, outermost). -/
  steps : Fin n → List (GeoStep (flatDim d))
  /-- Per-chart compact source domain (a closed box in resolved coordinates — pnp-cover). -/
  dom : Fin n → Set (Fin (flatDim d) → ℝ)
  /-- Per-chart open certificate region (the `nbhd`). -/
  region : Fin n → Set (Fin (flatDim d) → ℝ)
  /-- Per-chart dominant monomial `b₁` exponent. -/
  bexp : Fin n → (Fin (flatDim d) → ℕ)
  /-- Per-chart total Jacobian monomial exponent. -/
  jac : Fin n → (Fin (flatDim d) → ℕ)
  /-- Each region is open. -/
  hregion_open : ∀ c, IsOpen (region c)
  /-- Each region contains the origin. -/
  hzero_region : ∀ c, (0 : Fin (flatDim d) → ℝ) ∈ region c
  /-- Each source domain is compact. -/
  hdom_compact : ∀ c, IsCompact (dom c)
  /-- Each source domain contains the origin. -/
  hzero_dom : ∀ c, (0 : Fin (flatDim d) → ℝ) ∈ dom c
  /-- Each source domain sits inside its region. -/
  hdom_sub : ∀ c, dom c ⊆ region c
  /-- Each dominant monomial binds along some axis. -/
  hbind : ∀ c, (bindingAxes (bexp c)).Nonempty
  /-- **Squarefree `b₁`** — unit divisor multiplicity `k_d = 1` on binding axes (Aoyagi
  worked.tex:495; condition (4)'s squarefreeness). -/
  hsqfree : ∀ c, ∀ a ∈ bindingAxes (bexp c), bexp c a = 1

/-- The path map of chart `c`: the composition of its step σ's (`pathMap`, root outermost). -/
def GeoAtlasData.gmap {d : Fin (N + 1) → ℕ} {e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d}
    (a : GeoAtlasData d e) (c : Fin a.n) : (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ) :=
  pathMap ((a.steps c).map GeoStep.σ)

/-! ## D3 named gap hypotheses (elder D3) — carried at the leaf-5 fold, not silent -/

/-- **D3 gap (a) — the ∀-L structural divisibility chain**, graded STRIKE-ABLE (elder D3a; NOT
frontier). The dominant divisor exponent divides every divisor exponent at every leaf and all depths
`L` — the divisibility chain the terminal principality rides. Discharge route KNOWN: thread-31's
closed form `b_i = ∏_{t̃<i} u` / the salvaged ledger facts. Pricing this as open math would be false
timidity; it is named here so leaf 5 discharges it, not hides it. -/
def StructuralChainResidual (d : Fin (N + 1) → ℕ) : Prop :=
  ∀ l ∈ ResolutionTree.leaves (buildTree d (conOracle d) (conRoot : ConState N)),
    ∀ k k' : Fin l.numDiv, l.divExp k ∣ l.divExp k' ∨ l.divExp k' ∣ l.divExp k

/-- **D3 gap (b) — the pivot-ordering rendering for `k₀`** (elder D3): a dominant (divisibility-
minimal) divisor index exists at every nonempty leaf — the well-definedness of the `k₀` the M'=1
compression names. A named residual assumption (pnp §d), discharged/carried at the leaf-5 fold. -/
def PivotOrderingK0 (d : Fin (N + 1) → ℕ) : Prop :=
  ∀ l ∈ ResolutionTree.leaves (buildTree d (conOracle d) (conRoot : ConState N)),
    0 < l.numDiv → ∃ k₀ : Fin l.numDiv, ∀ k : Fin l.numDiv, l.divExp k₀ ≤ l.divExp k

/-! ## L5 — the path fold: `StepInv` folded to per-chart terminal `PrincipalInv` -/

/-- **L5 — the path fold produces the geometric atlas.** Folding the interior `StepInv` from the
trivial root state (`g = id`, `b = 1`, residual `= coreGen`) down each root→leaf branch of the built
tree, via the one-step preservations (`case2_preserves_stepInv`, `case1_preserves_stepInv`) at each
edge, reaching the terminal state where `terminal_bezout` upgrades divisibility to the terminal
`PrincipalInv` (both directions). Produces a `GeoAtlasData` whose every chart carries the terminal
`PrincipalInv` for its path map on its region.

Hypotheses (THE SEQUENCE GATE — elder D3b: the named gaps stop being deferrable HERE): the three
one-step obligations (L3/L4/`terminal_bezout`), and the two D3 named gaps
(`StructuralChainResidual` — strike-able; `PivotOrderingK0`). The `srcBox`-seam pathwise coherence
(module docstring) is the decorrelated-check gate riding the `CenterCoordAligned` fields. -/
@[blueprint]
theorem leaf_stepInv_of_path (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 0 < N)
    (hpos : ∀ k, 0 < d k) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he0 : e 0 = 0)
    (he_lin : IsLinearMap ℝ ⇑e)
    (hcase2 : Case2Preservation) (hcase1 : Case1Preservation) (hterm : TerminalBezout)
    (hchainR : StructuralChainResidual d) (hpivot : PivotOrderingK0 d) :
    ∃ atlas : GeoAtlasData d e,
      ∀ c : Fin atlas.n, ∃ q r : Fin (d (Fin.last N) * d 0) → (Fin (flatDim d) → ℝ) → ℝ,
        PrincipalInv (coreGen d e) (atlas.gmap c) (monoOf (atlas.bexp c)) q r (atlas.region c) := by
  -- map: B-L5-path-fold (fold StepInv via L3/L4 along tree branches; terminal_bezout at each leaf)
  sorry

/-! ## L6 — the chart geometry: assemble a certified `Chart` from a branch -/

/-- **L6 — the chart geometry.** For a chart `c` of the atlas, the path map `gmap c` (a composition of
shear ∘ blow-up steps) is analytic, origin-fixing, and a.e.-injective, with `|det D(gmap c)| =
jacWeight (jac c) · unit` (unit ≡ 1 — the shear-pin Jacobian, the shears Jacobian-exactly-1 and the
exceptional coordinates untouched by later shears) and squarefree dominant `b₁` (binding axes carry
exponent 1). Given the two region-ideal inclusions (from L1, on the region), it ASSEMBLES a certified
`Chart (coreGen d e) 0` whose map/domain/region/exponents are the atlas's. The GENUINE content is the
fold of the per-step geometry (`GeoStep` fields) into the path-map geometry. Region-quantified
(condition (1)): all certificates on `region c`. -/
@[blueprint]
theorem leafPath_chartGeometry (d : Fin (N + 1) → ℕ) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (atlas : GeoAtlasData d e) (c : Fin atlas.n)
    (hfwd : RegionRepresents (fun i ↦ coreGen d e i ∘ atlas.gmap c)
      (fun _ : Fin 1 ↦ monoOf (atlas.bexp c)) (atlas.region c))
    (hbwd : RegionRepresents (fun _ : Fin 1 ↦ monoOf (atlas.bexp c))
      (fun i ↦ coreGen d e i ∘ atlas.gmap c) (atlas.region c)) :
    ∃ chart : Chart (coreGen d e) 0,
      chart.g = atlas.gmap c ∧ chart.dom = atlas.dom c ∧ chart.nbhd = atlas.region c ∧
        chart.bexp chart.k₀ = atlas.bexp c ∧ chart.jac = atlas.jac c := by
  -- map: B-L6-chart-geometry (fold per-step analytic/inj/Jacobian into the path-map Chart; unit ≡ 1)
  sorry

/-! ## L7 — the compact cover (pnp-cover verdict: FULL cover, empty escape) -/

/-- **L7 — the compact cover (STRONGER inclusion form, pnp-cover thread 35).** A ball around the
origin is FULLY covered (empty escape) by the images of the charts' compact source domains:
`ball 0 ρ ⊆ ⋃ c, (gmap c) '' (dom c)`. Routing = top-down argmax lift `x ↦ (leaf, resolved w)`; the
shear inverses are polynomial; each atom is the landed `OriginBlowup.ball_subset_iUnion_blowup_image`,
generalized R = 1 → R-parametric (the no-inflation trick dies once shears give bound 2 — the
R-parametric atom + finite-depth box inflation) with bounded spectators (`cubeBox d × cubeBox (N−d)`,
never `pivotDomain × univ`). The driver closes the record `hcover` by
`Set.diff_eq_empty.2 hsub ▸ measure_empty` (the landed `OriginBlowup` idiom). -/
@[blueprint]
theorem leafPath_compactCover (d : Fin (N + 1) → ℕ) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (atlas : GeoAtlasData d e) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Metric.ball (0 : Fin (flatDim d) → ℝ) ρ ⊆ ⋃ c, (atlas.gmap c) '' (atlas.dom c) := by
  -- map: B-L7-compact-cover (top-down argmax lift; R-parametric OriginBlowup atom; empty escape)
  sorry

/-! ## L8 — the exponents ↔ ledger match (feeds `AtlasRealizesExponents`) -/

/-- **L8 — the atlas exponents realize the built tree's terminal spectrum.** The two clauses of
`AtlasRealizesExponents`, phrased on the atlas's own `bexp`/`jac`: (i) every chart binding-axis
exponent `jac a + 1` is a terminal exponent of `buildTree d (conOracle d) conRoot`; (ii) every
`minAdm`-attaining leaf divisor exponent is matched by some chart's binding-axis exponent. This is the
value-support match (NOT a structural chart↔leaf correspondence — RecursionAdapter). It rides the two
D3 named gaps (`StructuralChainResidual`, `PivotOrderingK0`) linking the geometric blow-up exponents
to the combinatorial divisor exponents. Generalizes the LANDED `exists_atlasRealizesExponents_d12`
match (`jac a + 1 = flatDim − 1 + 1 = 2 = minAdm ![1,2]`) to general `d`. -/
@[blueprint]
theorem leafPath_realizesExponents (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 0 < N)
    (hpos : ∀ k, 0 < d k) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (atlas : GeoAtlasData d e)
    (hchainR : StructuralChainResidual d) (hpivot : PivotOrderingK0 d) :
    (∀ (c : Fin atlas.n) (a : Fin (flatDim d)), a ∈ bindingAxes (atlas.bexp c) →
        (atlas.jac c a + 1) ∈
          ResolutionTree.terminalExponents (buildTree d (conOracle d) (conRoot : ConState N))) ∧
      (∀ l ∈ ResolutionTree.leaves (buildTree d (conOracle d) (conRoot : ConState N)),
        ∀ k : Fin l.numDiv, l.divExp k = minAdm d →
          ∃ (c : Fin atlas.n) (a : Fin (flatDim d)),
            a ∈ bindingAxes (atlas.bexp c) ∧ atlas.jac c a + 1 = l.divExp k) := by
  -- map: B-L8-exponents-ledger (geometric blow-up exponents = tree divExps; value-support match)
  sorry

/-! ## The composition driver — the residual goal of `exists_coreResolution` -/

/-- **The composition driver — general `d`.** Folds the leaves into
`∃ res : Resolution (coreGen d e) 0, AtlasRealizesExponents d res` (the residual goal of
`exists_coreResolution` after `exists_hlb_hattain_of_exists_atlasRealizesExponents`). Sorried ONLY via
the leaves: L5 (`leaf_stepInv_of_path`) supplies the atlas + per-chart terminal `PrincipalInv`
(itself folding L3/L4/`terminal_bezout` + the D3 gaps); L1 (`principalInv_regionRepresents`) turns each
into the two `RegionRepresents`; L6 (`leafPath_chartGeometry`) assembles each certified `Chart`; L7
(`leafPath_compactCover`) gives the full cover; L8 (`leafPath_realizesExponents`) gives the exponent
match. Generalizes the LANDED `exists_atlasRealizesExponents_d12` from `d = ![1,2]` to all `d`.
`@[blueprint]` — it rests on the (still-forecast) leaves; strikes to banked when they land. -/
@[blueprint]
theorem exists_atlasRealizesExponents (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 0 < N)
    (hpos : ∀ k, 0 < d k) (hne : (qipFeasible d).Nonempty)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he0 : e 0 = 0) (he_lin : IsLinearMap ℝ ⇑e)
    (hchainR : StructuralChainResidual d) (hpivot : PivotOrderingK0 d) :
    ∃ res : Resolution (coreGen d e) 0, AtlasRealizesExponents d res := by
  -- L5: the geometric atlas + per-chart terminal PrincipalInv (folds L3/L4/terminal_bezout).
  obtain ⟨atlas, hprin⟩ := leaf_stepInv_of_path d hd hN hpos e he0 he_lin
    case2_preserves_stepInv case1_preserves_stepInv terminal_bezout hchainR hpivot
  -- Per chart: L1 (ideal) then L6 (assemble the certified Chart), matching the atlas's data.
  have hchart : ∀ c : Fin atlas.n, ∃ chart : Chart (coreGen d e) 0,
      chart.g = atlas.gmap c ∧ chart.dom = atlas.dom c ∧ chart.nbhd = atlas.region c ∧
        chart.bexp chart.k₀ = atlas.bexp c ∧ chart.jac = atlas.jac c := by
    intro c
    obtain ⟨q, r, hpt⟩ := hprin c
    obtain ⟨hfwd, hbwd⟩ :=
      principalInv_regionRepresents (coreGen d e) (atlas.gmap c) (monoOf (atlas.bexp c)) q r
        (atlas.region c) hpt
    exact leafPath_chartGeometry d e atlas c hfwd hbwd
  choose charts hg hdom _hnbhd hbexp hjac using hchart
  -- L7: the full cover of a ball by the charts' domain images.
  obtain ⟨ρ, hρ, hcov⟩ := leafPath_compactCover d e atlas
  -- L8: the exponent match.
  obtain ⟨hspec_lb, hspec_attain⟩ :=
    leafPath_realizesExponents d hd hN hpos e atlas hchainR hpivot
  -- assemble the Resolution.
  haveI : Nonempty (Fin atlas.n) := ⟨⟨0, atlas.hn⟩⟩
  refine ⟨⟨atlas.n, charts, Finset.univ_nonempty, Metric.ball 0 ρ, Metric.ball_mem_nhds 0 hρ, ?_⟩,
    ?_, ?_⟩
  · -- hcover: the ball is fully covered by the charts' domain images (empty escape).
    have hsub : Metric.ball (0 : Fin (flatDim d) → ℝ) ρ ⊆ ⋃ c, (charts c).g '' (charts c).dom := by
      refine hcov.trans (Set.iUnion_mono (fun c ↦ ?_))
      rw [hg c, hdom c]
    rw [Set.diff_eq_empty.2 hsub]; exact measure_empty
  · -- AtlasRealizesExponents clause (i): transfer via the chart exponent equalities.
    intro c a ha
    rw [hjac c]
    refine hspec_lb c a ?_
    have : (charts c).bexp (charts c).k₀ = atlas.bexp c := hbexp c
    rwa [this] at ha
  · -- AtlasRealizesExponents clause (ii): transfer via the chart exponent equalities.
    intro l hl k hlk
    obtain ⟨c, a, ha, hval⟩ := hspec_attain l hl k hlk
    refine ⟨c, a, ?_, ?_⟩
    · rw [hbexp c]; exact ha
    · rw [hjac c]; exact hval

/-- **The FULL `exists_coreResolution` statement, re-proved by the monument composition.** Identical
to `LearningCoefficient.exists_coreResolution` but discharged via `exists_atlasRealizesExponents` +
the salvage adapter `exists_hlb_hattain_of_exists_atlasRealizesExponents` (NO `sorry` of its own; the
`sorryAx` cone is exactly the leaf set). The two D3 named gaps are surfaced as hypotheses (they are
the named residual assumptions of the fold). See the module docstring on the wiring.
`@[blueprint]` — rests on the forecast leaves; strikes to banked when they land. -/
@[blueprint]
theorem exists_coreResolution_via_monument (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 0 < N)
    (hpos : ∀ k, 0 < d k) (hne : (qipFeasible d).Nonempty)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he0 : e 0 = 0) (he_lin : IsLinearMap ℝ ⇑e)
    (hchainR : StructuralChainResidual d) (hpivot : PivotOrderingK0 d) :
    ∃ res : Resolution (coreGen d e) 0,
      (∀ (c : Fin res.numCharts) (a : Fin (flatDim d)),
        a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) →
        qipMin d hne ≤ ((res.charts c).jac a + 1 : ℤ)) ∧
      (∃ (c : Fin res.numCharts) (a : Fin (flatDim d)),
        a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) ∧
        ((res.charts c).jac a + 1 : ℤ) = qipMin d hne) := by
  refine exists_hlb_hattain_of_exists_atlasRealizesExponents d hd hN hpos hne ?_
  exact exists_atlasRealizesExponents d hd hN hpos hne e he0 he_lin hchainR hpivot

end DLNFibre.DLN.Aoyagi
