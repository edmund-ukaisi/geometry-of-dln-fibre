import DLNFibre.DLN.RLCT.Engine.GeoFoldRegroup
import DLNFibre.DLN.RLCT.Engine.GeoInvVal

/-!
# `DLNFibre.DLN.RLCT.Engine.GeoInvValWalk` — the value walk `Inv_val` (loss-t15, PHASE 3b build)

The value instance of t14's fold walk (`GeoFoldRegroup.geoAtlas_cocycle`): threading the
prod-diagonalization invariant `Inv_val(acc, s)` down `buildTree`, mirroring t14's skeleton
(`conOracle` re-dispatch, `mem_edgesLeaves_fanned_*`, the four per-case maintenance) with the VALUE
payload. The terminal case gives `prod = diagonal(b)` and plugs into the PROVEN
`GeoInvVal.leafDiagFrob_of_prodDiag`, closing `leafDiagFrob_geoAtlasNorm`.

**Encoding = PREFIX-based, THREE-STATE** (elder-ratified 2026-07-20, `clearedof_walk_trace.py`,
`prefix_rebase_gate.py`, `width_drop_leg.py`). The invariant reads `prodPrefix s (acc w)` — Aoyagi's
FRONT block `diag(b)·[[E_J,O],[O,D_J]]` (layers `0..s.layer`), NOT the full `prod` (whose cleared
rows carry the raw trailing factor `∏_{s>S}C`, FALSE at intermediate states). Per prod-prefix-entry,
each diagonal position `i` is in one of THREE states: CLEARED (`clearedOf`, carries its `b`-monomial
`bmonOf`), DROPPED (`droppedOf`, zero — rank drop, `i ≥` the running-min width), or UNRESOLVED (no
constraint — its value is first-class EXPOSED for the clearing step to read). At a terminal
`prodPrefix = prod` and every position is cleared-or-dropped ⟹ `prod = diagonal(bmon)` ⟹
`leafDiagFrob_of_prodDiag`.

**STAGING (t14 discipline):** the payload defs + base + leaf-discharge (this file's banked unit) →
the four matrix-maintenance cases as SEPARATE banked greens → the walk instantiation mirroring
`geoAtlas_cocycle` over `tGeoG alphaGauge` (using the fan-decomposition lemmas below).
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-! ## The prodAux↔flat-coords bridge (value-maintenance foundation, gate shape 1) -/

/-- **Shape 1 — atomic layer read**: a layer-matrix entry IS its flat coordinate,
`A s i j = z_{flatCoordOf s i j}(A)`. The `paramsEquivFlat` decode (mirrors the Validate
`paramsEquivFlat_apply_equivFin`, re-proved here to keep the value-walk chain's deps in Foundations,
not Validate). The foundation the maintenance uses to read prod entries as flat coords. -/
theorem layerEntry_eq_flat (A : Params M) (s : Fin L)
    (i : Fin (M s.castSucc)) (j : Fin (M s.succ)) :
    A s i j = paramsEquivFlat M A (flatCoordOf M s i j) := by
  rw [flatCoordOf]
  symm
  unfold paramsEquivFlat
  erw [MeasurableEquiv.trans_apply, MeasurableEquiv.trans_apply]
  simp only [MeasurableEquiv.coe_piCurry_symm]
  erw [Equiv.arrowCongr_apply]
  simp only [Function.comp_apply]
  erw [Equiv.symm_apply_apply]
  rfl

/-! ## The prefix object (prefix re-base, elder-ratified) -/

/-- **The prefix column index** `min (s.layer+1) L`: `prodPrefix` covers layers `0..s.layer` (capped
at all `L` layers). At a terminal (`layer = L`) it is `Fin.last L`. -/
def prefixColFin (s : ConState L) : Fin (L + 1) := ⟨min (s.layer + 1) L, by omega⟩

/-- At a live (branch) state (`s.layer < L`) the prefix boundary is exactly `s.layer + 1` — so
`prodPrefix` covers layers `0..s.layer` inclusive, the last being layer `s.layer` (the step's chart
layer). A transport tool for the four-case maintenance. -/
theorem prefixColFin_val_of_live (s : ConState L) (hlive : s.layer < L) :
    (prefixColFin s : ℕ) = s.layer + 1 := by
  show min (s.layer + 1) L = s.layer + 1
  omega

/-- **The prefix product** `prodAux M A (prefixColFin s)` — Aoyagi's front block
`diag(b)·[[E_J,O],[O,D_J]]` (layers `0..s.layer` at the transformed params). The full `prod`'s
trailing factor is cut off (elder: the full product's cleared rows are contaminated by it; the
prefix's are not). -/
noncomputable def prodPrefix (s : ConState L) (A : Params M) :
    Matrix (Fin (M 0)) (Fin (M (prefixColFin s))) ℝ :=
  prodAux M A (prefixColFin s) (prefixColFin s).isLt

/-- `prodAux` at the last index IS `prod` (generalize-index → subst → rfl). -/
theorem prodAux_last_eq_prod {k : Fin (L + 1)} (A : Params M) (hk : k = Fin.last L) :
    prodAux M A (k : ℕ) k.isLt = hk ▸ prod M A := by subst hk; rfl

/-- **Prefix = full at a terminal** (`prefixColFin s = Fin.last L`): the trailing is empty, so
`prodPrefix s = prod` (associativity realized — the leaf discharge composes unchanged). -/
theorem prodPrefix_eq_prod (s : ConState L) (A : Params M) (hlast : prefixColFin s = Fin.last L) :
    prodPrefix s A = hlast ▸ prod M A := by
  unfold prodPrefix; exact prodAux_last_eq_prod A hlast

/-! ## The three-state row classification + `b`-monomial (battery `clearedof_walk_trace.py`) -/

/-- **resolvedRows** (candidate A): the count of cleared diagonal rows — the current layer's
`cleared` mid-walk (resets per layer; the incoming raw layer contaminates the earlier rows), the
full running-min `widthMinUpto M L` at a terminal (final-layer clearing persists). -/
def resolvedRows (s : ConState L) : ℕ := if s.layer = L then widthMinUpto M L else s.cleared

/-- **CLEARED**: diagonal row `i < resolvedRows` carries its `b`-monomial. -/
def clearedOf (s : ConState L) (i : Fin (M 0)) : Prop := (i : ℕ) < resolvedRows (M := M) s

/-- **The dropped threshold** (ROLLOVER-AWARE): the rank ceiling exposed so far —
`widthMinUpto M (s.layer+1)` once the rollover guard `widthMinUpto M (s.layer+1) ≤ s.cleared` fires
(the narrow layer's bottleneck is reached), else the persisted `widthMinUpto M s.layer`. Fires the
drop at the rollover NODE (rollover maintenance then propagates `row = 0`). -/
def dropThreshold (s : ConState L) : ℕ :=
  if widthMinUpto M (s.layer + 1) ≤ s.cleared then widthMinUpto M (s.layer + 1)
  else widthMinUpto M s.layer

/-- **DROPPED**: row `i` beyond the rank ceiling is zero (rank drop; accumulates, never undrops). -/
def droppedOf (s : ConState L) (i : Fin (M 0)) : Prop := dropThreshold (M := M) s ≤ (i : ℕ)

instance clearedOf_decidable (s : ConState L) (i : Fin (M 0)) :
    Decidable (clearedOf (M := M) s i) := by unfold clearedOf; infer_instance
instance droppedOf_decidable (s : ConState L) (i : Fin (M 0)) :
    Decidable (droppedOf (M := M) s i) := by unfold droppedOf; infer_instance

/-- **bmon** (ledger-closed A-scaling; battery-fixed filter `≤`): 0-based position `p` = 1-based
chain index `p+1`, so `b_{p+1} = ∏_{t̃ ≤ p} z_{birthFlatCoord}`. -/
noncomputable def bmonOf (h : 0 < flatDim M) (s : ConState L) (w : Params M) (p : Fin (M 0)) : ℝ :=
  ∏ k ∈ Finset.univ.filter (fun k : Fin s.numDiv => s.divTilde k ≤ (p : ℕ)),
    paramsEquivFlat M w (birthFlatCoord M s k h)

/-- **The value invariant `InvVal3`** (prefix-based, THREE-STATE; option C). CLEARED rows are
diagonal `= bmon`; DROPPED rows are zero; UNRESOLVED rows are first-class EXPOSED (no constraint —
their values `prodPrefix i j` are read directly by the clearing step). Parametric in
`cleared`/`dropped`/`bmon` (instantiated with `clearedOf`/`droppedOf`/`bmonOf` at the headline). -/
def InvVal3 (cleared dropped : ConState L → Fin (M 0) → Prop)
    [∀ s i, Decidable (cleared s i)] [∀ s i, Decidable (dropped s i)]
    (bmon : ConState L → Params M → Fin (M 0) → ℝ)
    (acc : Params M → Params M) (s : ConState L) : Prop :=
  ∀ (w : Params M) (i : Fin (M 0)) (j : Fin (M (prefixColFin s))),
    (cleared s i → prodPrefix s (acc w) i j = if (i : ℕ) = (j : ℕ) then bmon s w i else 0) ∧
    (dropped s i → prodPrefix s (acc w) i j = 0)

/-- **Vacuous base at `conRoot`** (option C base is trivially true — nothing cleared or dropped). -/
theorem invVal3_conRoot (cleared dropped : ConState L → Fin (M 0) → Prop)
    [∀ s i, Decidable (cleared s i)] [∀ s i, Decidable (dropped s i)]
    (bmon : ConState L → Params M → Fin (M 0) → ℝ)
    (hcl : ∀ i : Fin (M 0), ¬ cleared (conRoot : ConState L) i)
    (hdr : ∀ i : Fin (M 0), ¬ dropped (conRoot : ConState L) i) :
    InvVal3 cleared dropped bmon id (conRoot : ConState L) :=
  fun _ i _ => ⟨fun hc => absurd hc (hcl i), fun hd => absurd hd (hdr i)⟩

/-! ## The three-state leaf discharge (`InvVal3` at a terminal → `LeafDiagFrob`) -/

/-- **`prodAux` entry = `prod` entry at the last index** (bound index `k`, cast on the column;
subst → rfl). -/
theorem prodAux_last_entry (A : Params M) {k : Fin (L + 1)} (hk : k = Fin.last L)
    (i : Fin (M 0)) (j : Fin (M k)) :
    prodAux M A (k : ℕ) k.isLt i j = prod M A i (Fin.cast (congrArg M hk) j) := by
  subst hk; rfl

/-- **`prodPrefix` entry = `prod` entry at a terminal** (`prefixColFin s = Fin.last L`, cast on the
column index). The cast bridge the leaf discharge uses. -/
theorem prodPrefix_entry_eq_prod (s : ConState L) (A : Params M)
    (hlast : prefixColFin s = Fin.last L)
    (i : Fin (M 0)) (j : Fin (M (prefixColFin s))) :
    prodPrefix s A i j = prod M A i (Fin.cast (congrArg M hlast) j) := by
  unfold prodPrefix; exact prodAux_last_entry A hlast i j

/-- **The three-state leaf discharge**: at a terminal leaf (`hlast`), `InvVal3` (every row cleared
or dropped `hcov`; disjoint `hdisj`) collapses `prod` to the diagonal `dvec := if cleared then bmon
else 0`: CLEARED rows carry `bmon`, DROPPED rows are `0` (width-drop fix; the `M(last)` cutoff extra
terms vanish). Feeds the PROVEN `leafDiagFrob_of_prodDiag`. -/
theorem leafDiagFrob_of_invVal3_leaf
    (cleared dropped : ConState L → Fin (M 0) → Prop)
    [∀ s i, Decidable (cleared s i)] [∀ s i, Decidable (dropped s i)]
    (bmon : ConState L → Params M → Fin (M 0) → ℝ)
    (l : LeafData M) (s_leaf : ConState L)
    (hlast : prefixColFin s_leaf = Fin.last L)
    (hinv : InvVal3 cleared dropped bmon l.chartMap s_leaf)
    (hcov : ∀ i : Fin (M 0), cleared s_leaf i ∨ dropped s_leaf i)
    (hdisj : ∀ i : Fin (M 0), dropped s_leaf i → ¬ cleared s_leaf i)
    (ρ : Params M → Fin (M 0) → ℝ) (hi : ℝ)
    (hbmon : ∀ w ∈ l.srcBox, ∀ i : Fin (M 0),
      (if (i : ℕ) < M (Fin.last L) then (if cleared s_leaf i then bmon s_leaf w i else 0) else 0)
        = (∏ k : Fin l.numDiv, paramsEquivFlat M w (l.divCoord k)) * ρ w i)
    (hone : ∀ w ∈ l.srcBox, ∃ i : Fin (M 0), ρ w i = 1)
    (hbd : ∀ w ∈ l.srcBox, ∑ i : Fin (M 0), (ρ w i) ^ 2 ≤ hi) :
    LeafDiagFrob l := by
  refine leafDiagFrob_of_prodDiag l
    (fun w i => if cleared s_leaf i then bmon s_leaf w i else 0) ρ hi ?_ hbmon hone hbd
  intro w _ i j
  simp only []                                    -- beta-reduce the dvec lambda
  -- move to the prefix frame: j ↦ j' : Fin (M (prefixColFin s_leaf)), via prodPrefix_entry_eq_prod
  set j' : Fin (M (prefixColFin s_leaf)) := Fin.cast (congrArg M hlast.symm) j with hj'
  have hval : (j' : ℕ) = (j : ℕ) := by rw [hj', Fin.coe_cast]
  have hcast : Fin.cast (congrArg M hlast) j' = j := by apply Fin.ext; rw [Fin.coe_cast]; exact hval
  have hpp : prodPrefix s_leaf (l.chartMap w) i j' = prod M (l.chartMap w) i j := by
    rw [prodPrefix_entry_eq_prod s_leaf (l.chartMap w) hlast i j', hcast]
  rw [← hpp]
  rcases hcov i with hc | hd
  · rw [(hinv w i j').1 hc, hval, if_pos hc]
  · rw [(hinv w i j').2 hd, if_neg (hdisj i hd)]; simp

/-! ## The α-atlas walk infrastructure (`tGeoG` fan-decomposition, resid-independent)

The value walk threads `InvVal` down `buildTree` over the α-normalized atlas `tGeoG alphaGauge`, so
it needs the `tGeoG`/`fannedEdgesG` analogs of t14's `tGeo`/`fannedEdges` fan-decomposition lemmas
(`GeoFoldRegroup.mem_edgesLeaves_fanned_{charted,chartless}`, hardcoded to gauge `fun _ => id`).
These are pure tree-structure plumbing — independent of the `InvVal` payload
(`cleared`/`bmon`/`resid`) — so they land regardless of the resid encoding ruling. They mirror t14's
proofs with the `gauge` threaded (`geoChartMapNorm gauge` / `tGeoG gauge` for the id forms). -/

/-- **Charted single-edge fan decomposition** (α-atlas): the `tGeoG` analog of
`mem_edgesLeaves_fanned_charted`. A leaf of the fan of ONE charted edge (`dCenterOfEdge ≠ 0`) sits
under one pivot chart `acc ∘ geoChartMapNorm gauge ⟨n, e, offset + pp⟩`. -/
theorem mem_edgesLeaves_fannedG_charted (gauge : GeoChart M → Params M → Params M)
    (acc : Params M → Params M) (n : StepData M) (offset : ℕ)
    (ec : StepCase) (esub : ChartSubst M) (ch : ResolutionTree M) (c : LeafData M)
    (hz : dCenterOfEdge n (Edge.mk ec esub ch) ≠ 0)
    (hc : c ∈ ResolutionTree.edgesLeaves (fannedEdgesG gauge acc n offset [Edge.mk ec esub ch])) :
    ∃ pp : ℕ, pp < dCenterOfEdge n (Edge.mk ec esub ch) ∧
      c ∈ ResolutionTree.leaves
        (tGeoG gauge (acc ∘ geoChartMapNorm gauge ⟨n, Edge.mk ec esub ch, offset + pp⟩) ch) := by
  rw [fannedEdgesG, edgesLeaves_eq, List.flatMap_append, ← edgesLeaves_eq, ← edgesLeaves_eq,
    List.mem_append] at hc
  rcases hc with hc | hc
  · rw [if_neg hz, edgesLeaves_mapMk, List.mem_flatMap] at hc
    obtain ⟨pp, hppmem, hcp⟩ := hc
    refine ⟨pp, ?_, hcp⟩
    rw [List.bind_eq_flatMap, List.mem_flatMap] at hppmem
    obtain ⟨a, -, ha⟩ := hppmem
    rw [List.mem_pure] at ha
    have hai := a.isLt
    omega
  · rw [show fannedEdgesG gauge acc n (offset + dCenterOfEdge n (Edge.mk ec esub ch))
        ([] : List (Edge M)) = [] from rfl] at hc
    simp [ResolutionTree.edgesLeaves] at hc

/-- **Chartless single-edge fan decomposition** (α-atlas, rollover): the `tGeoG` analog of
`mem_edgesLeaves_fanned_chartless`. The ONE identity edge (`dCenterOfEdge = 0`) forwards `acc`. -/
theorem mem_edgesLeaves_fannedG_chartless (gauge : GeoChart M → Params M → Params M)
    (acc : Params M → Params M) (n : StepData M) (offset : ℕ)
    (ec : StepCase) (esub : ChartSubst M) (ch : ResolutionTree M) (c : LeafData M)
    (hz : dCenterOfEdge n (Edge.mk ec esub ch) = 0)
    (hc : c ∈ ResolutionTree.edgesLeaves (fannedEdgesG gauge acc n offset [Edge.mk ec esub ch])) :
    c ∈ ResolutionTree.leaves (tGeoG gauge acc ch) := by
  rw [fannedEdgesG, edgesLeaves_eq, List.flatMap_append, ← edgesLeaves_eq, ← edgesLeaves_eq,
    List.mem_append] at hc
  rcases hc with hc | hc
  · rw [if_pos hz] at hc
    simpa [ResolutionTree.edgesLeaves] using hc
  · rw [show fannedEdgesG gauge acc n (offset + dCenterOfEdge n (Edge.mk ec esub ch))
        ([] : List (Edge M)) = [] from rfl] at hc
    simp [ResolutionTree.edgesLeaves] at hc

end DLNFibre.DLN.RLCT.Engine
