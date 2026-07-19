import DLNFibre.DLN.RLCT.Engine.EngineDefs
import DLNFibre.DLN.RLCT.Engine.EngineConstruction
import DLNFibre.DLN.RLCT.Engine.O5Realization
import DLNFibre.DLN.RLCT.Engine.RegionGlueAssembly
import DLNFibre.DLN.RLCT.Engine.ChartBridgeFaithful

/-!
# `DLNFibre.DLN.RLCT.Engine.EngineObligations` — the engine's obligations

**Blueprint spine: statements are forecasts; churn is normal; the blueprint consumption rules
apply.** The transform-only Aoyagi engine's obligation THEOREMS. `monomialization_terminates` is now
ASSEMBLED from the construction spine (`EngineConstruction`): its resolution tree is
`buildTree (conOracle M) conRoot`, and four of `CanonicalResolution`'s six conjuncts are PROVEN
clean-three (`isFullMonomialization_buildTree_conRoot`, `stepRel_all_of_buildTree`,
`base_of_buildTree`, `minAdm_le_terminalExponents`). The TWO remaining conjuncts are their OWN NAMED
sorried holes: `chartBridge_buildTree` (← T3 coverage lane) and `o5_realization` (← D§ii/iii, from
pnp-o5 cert §3–4). The rest are projections of `resolutionOf_spec`.

**`0 < L` is REQUIRED** (nondegenerate chain): at `L = 0` the root terminates immediately, so
`CanonicalResolution`'s base conjunct (a `branch`-rooted tree) is false — `monomialization_terminates`
is genuinely FALSE at `L = 0`. This is a statement CORRECTION (the third obligation-statement fix in
standing counsel), deliberately DISTINCT from width-positivity (which the spine proved unnecessary).
The DLN call site supplies it (`1 ≤ L`).

**Layer-B fence: only `region_glue` integrates.**
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped ENNReal

variable {L : ℕ}

/-! ## The two named holes (their own sorried declarations, attributed to their fill sources) -/

/-- **ChartBridge for the built tree** (map: `coverage-theorem`; the T3 coverage lane).
The CoV atlas over `buildTree (conOracle M) conRoot`, obtained as the drop-(D) PROJECTION of the
faithful discharge `chartBridgeFaithful_buildTree` (R-split, elder charge-4). So clause (D) — the
geometric-chart fidelity — is on THIS theorem's proof CONE (undroppable), not merely in a type: the
projection `.toChartBridge` forgets (D) for `region_glue`, but the discharge PROVED it.

FRONTIER: `chartBridgeFaithful_buildTree` proves (A) cover (`geoAtlas_imageCover`, green) + (D)
fidelity (`rfl` + the all-nodes lift `nodes_cNode_eq_realCNode`) outright; the remaining `(B)∧(C)`
per-piece props/exponents over `geoAtlas` are its two frontier sorries (ledger props + exponents via a
`geoAtlas`-leaf↔ledger bridge; a.e.-injectivity + `LeafPullback` geometric; `LeafJacobian` = t14's
`geoAtlas_fold_det`). The analytic hole of `monomialization_terminates` (`+sorryAx`) routes through
here (now via `chartBridgeFaithful_buildTree`) + `o5_realization`. -/
@[blueprint] theorem chartBridge_buildTree (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hMpos : ∀ i, 0 < M i) :
    ChartBridge M (buildTree M (conOracle M) (conRoot : ConState L)) :=
  (chartBridgeFaithful_buildTree M hL hMpos).toChartBridge

/-- **o5 realization** (map: `o5-realization`; D§ii/iii fills, from pnp-o5 cert §3–4). `minAdm M` is a
terminal exponent of the built tree (a clearable minimizer is realized — the ATTAINMENT half; the
lower bound is `minAdm_le_terminalExponents`) AND is attained at a leaf with a nonempty source box.
NOT `⊇ Adm` (that is false — stranding; ledger #4).

ASSEMBLED from two pieces: the plumbing is PROVEN here (the terminal-exponent membership follows from
the leaf's divisor-exponent list via `terminalExponents`' `flatMap`+`++`; `srcBox.Nonempty` is
`leaves_srcBox_nonempty`). The crux `o5_core_realized` (a realized `Mval`-minimizer — cert §3
envelope-splice + §4 steering/pull-ordering) is now PROVEN clean-three (`O5Realization`, t06 s4), so
`o5_realization` is clean-three too — the last analytic hole of `monomialization_terminates` is
`chartBridge_buildTree` alone.

**POSITIVE WIDTHS REQUIRED** (`hMpos : ∀ i, 0 < M i`; caveat next to the claim): the ATTAINMENT half is
FALSE at a zero width. Witness `M = ![2,2,0]`: `tStar M = (2,0)` (the minimizer) is never realized — the
zero last-width forces an immediate rollover, so no leaf carries `minAdm`. Found by t06 at the PROVE
step (obligation-statement instance (6); three-leg confirmed: sim + Lean `conOracle` trace + two
decorrelated Codex consults). The LOWER bound (`minAdm_le_terminalExponents`) stays width-free. -/
@[blueprint] theorem o5_realization (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hMpos : ∀ i, 0 < M i) :
    minAdm M ∈ ResolutionTree.terminalExponents (buildTree M (conOracle M) (conRoot : ConState L)) ∧
      (∃ l ∈ ResolutionTree.leaves (buildTree M (conOracle M) (conRoot : ConState L)),
        l.srcBox.Nonempty ∧
          minAdm M ∈ (List.finRange l.numDiv).map l.divExp) := by
  obtain ⟨l, hl, k, hk⟩ := o5_core_realized M hL hMpos
  have hmem : minAdm M ∈ (List.finRange l.numDiv).map l.divExp :=
    List.mem_map.mpr ⟨k, List.mem_finRange k, hk⟩
  refine ⟨?_, l, hl, leaves_srcBox_nonempty (M := M) conRoot l hl, hmem⟩
  rw [ResolutionTree.terminalExponents, List.mem_flatMap]
  exact ⟨l, hl, List.mem_append_left _ hmem⟩

/-! ## The construction hole + the canonical resolution -/

/-- **Monomialisation terminates into a canonical resolution** (map: `monomialization-termination`).
ASSEMBLED: `t = buildTree (conOracle M) conRoot`. Four conjuncts PROVEN clean-three (full
monomialisation, `StepRel` on every edge, the base peel, the `minAdm` lower bound); the two remaining
are the named holes `chartBridge_buildTree` (← T3) and `o5_realization` (← D§ii/iii) — caveats next to
the claim. Requires `0 < L` (base conjunct false at `L = 0`). -/
@[blueprint] theorem monomialization_terminates (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hMpos : ∀ i, 0 < M i) :
    ∃ t : ResolutionTree M, CanonicalResolution M t :=
  ⟨buildTree M (conOracle M) conRoot,
    isFullMonomialization_buildTree_conRoot M hL,
    stepRel_all_of_buildTree M (conOracle M) conRoot,
    base_of_buildTree M (conOracle M) conRoot rfl rfl (conRoot_steps hL),
    chartBridge_buildTree M hL hMpos,
    ⟨minAdm_le_terminalExponents M hL, (o5_realization M hL hMpos).1⟩,
    (o5_realization M hL hMpos).2⟩

/-- **The canonical resolution** of `M`. (`hMpos`: the attainment conjunct is false at a zero width.) -/
@[blueprint] noncomputable def resolutionOf (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hMpos : ∀ i, 0 < M i) :
    ResolutionTree M :=
  (monomialization_terminates M hL hMpos).choose

/-- The canonical resolution satisfies the full bundle. -/
@[blueprint] theorem resolutionOf_spec (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hMpos : ∀ i, 0 < M i) :
    CanonicalResolution M (resolutionOf M hL hMpos) :=
  (monomialization_terminates M hL hMpos).choose_spec

/-- The canonical resolution is a full monomialisation — the precondition of `region_glue`. -/
@[blueprint] theorem resolutionOf_isFullMonomialization (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hMpos : ∀ i, 0 < M i) :
    IsFullMonomialization (resolutionOf M hL hMpos) :=
  (resolutionOf_spec M hL hMpos).1

/-! ## The obligations (projections of the bundle) -/

/-- **Case-step invariant** (map: `case-step-lemmas`). A projection of `resolutionOf_spec`. -/
@[blueprint] theorem case_step_invariant (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hMpos : ∀ i, 0 < M i) :
    ∀ p ∈ ResolutionTree.stepEdges (resolutionOf M hL hMpos), StepRel p.1 p.2 :=
  (resolutionOf_spec M hL hMpos).2.1

/-- **Reduction layer** (map: `reduction-layer`). The regular peel: the resolution begins at the
base `S = J = 0`. STRUCTURAL (Layer-B fence). A projection of `resolutionOf_spec`. -/
@[blueprint] theorem reduction_layer (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hMpos : ∀ i, 0 < M i) :
    ∃ (n : StepData M) (edges : List (Edge M)),
      resolutionOf M hL hMpos = ResolutionTree.branch n edges ∧ n.layer = 0 ∧ n.cleared = 0 :=
  (resolutionOf_spec M hL hMpos).2.2.1

/-- **Coverage — THE HARD PART** (map: `coverage-theorem`, owned by coverage-design). A projection. -/
@[blueprint] theorem coverage_theorem (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hMpos : ∀ i, 0 < M i) :
    ChartBridge M (resolutionOf M hL hMpos) :=
  (resolutionOf_spec M hL hMpos).2.2.2.1

/-- **Exponent-ledger bridge** (map: `exponent-ledger-bridge`). `minAdm M` is a terminal exponent and
lower-bounds them all. A projection of `resolutionOf_spec`. -/
@[blueprint] theorem exponent_ledger_bridge (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hMpos : ∀ i, 0 < M i) :
    (∀ e ∈ ResolutionTree.terminalExponents (resolutionOf M hL hMpos), minAdm M ≤ e) ∧
      minAdm M ∈ ResolutionTree.terminalExponents (resolutionOf M hL hMpos) :=
  (resolutionOf_spec M hL hMpos).2.2.2.2.1

/-- **Live attainment** (finding 3): `minAdm M` is attained by a divisor exponent of a leaf with a
NONEMPTY source box. A projection of `resolutionOf_spec`. -/
@[blueprint] theorem exponent_ledger_liveAttainment (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hMpos : ∀ i, 0 < M i) :
    ∃ l ∈ ResolutionTree.leaves (resolutionOf M hL hMpos), l.srcBox.Nonempty ∧
      minAdm M ∈ (List.finRange l.numDiv).map l.divExp :=
  (resolutionOf_spec M hL hMpos).2.2.2.2.2

/-- **Region glue** (map: `region-glue`). ASSEMBLY ONLY: given the CoV bridge, the box integral is
finite whenever `c'` is below half every terminal exponent. Precondition `IsFullMonomialization`. -/
@[blueprint] theorem region_glue (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hMpos : ∀ i, 0 < M i)
    (hbridge : ChartBridge M (resolutionOf M hL hMpos)) (c' : ℝ)
    (hrat : ∀ e ∈ ResolutionTree.terminalExponents (resolutionOf M hL hMpos), c' < (e : ℝ) / 2) :
    routeMLayerBoxIntegral M c' 1 < ⊤ :=
  region_glue_of_chartBridge (resolutionOf M hL hMpos) hbridge c' hrat

end DLNFibre.DLN.RLCT.Engine
