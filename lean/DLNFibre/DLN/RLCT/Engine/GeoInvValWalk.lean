import DLNFibre.DLN.RLCT.Engine.GeoFoldRegroup
import DLNFibre.DLN.RLCT.Engine.GeoInvVal

/-!
# `DLNFibre.DLN.RLCT.Engine.GeoInvValWalk` — the value walk `Inv_val` (loss-t15, PHASE 3b build)

The value instance of t14's fold walk (`GeoFoldRegroup.geoAtlas_cocycle`): threading the
prod-diagonalization invariant `Inv_val(acc, s)` down `buildTree`, mirroring t14's skeleton
(`conOracle` re-dispatch, `mem_edgesLeaves_fanned_*`, the four per-case maintenance) with the VALUE
payload. The terminal case gives `prod = diagonal(b)` and plugs into the PROVEN
`GeoInvVal.leafDiagFrob_of_prodDiag`, closing `leafDiagFrob_geoAtlasNorm`.

**Encoding = ENTRY-WISE** (team-lead steer (b), 2026-07-20): the invariant is per prod-entry,
matching the per-entry (α) reads (`geoChartMap_flat_*`) and the cert's entry-wise value battery, and
sidestepping matrix-block instance friction. A `cleared s i` diagonal position carries its
`b`-monomial `bmon s w i` (the `z_{birthFlatCoord}` product per chain level); a cleared off-diagonal
cell is `0`; an uncleared cell is the residual read `resid s w i j`. At terminal `s` every position
is cleared ⟹ `prod = diagonal(bmon)` ⟹ `leafDiagFrob_of_prodDiag` (the block form
`diag(b)·[[E,O],[O,D]]` is a presentational corollary, not built — the bridge is the only consumer).

**STAGING (t14 discipline):** scaffold (elaborating, sorried) → the ends (base + leaf-discharge) +
reused reads → the four matrix-maintenance cases as SEPARATE banked greens, pushed each. Reusable
t14 reads + fan helpers + this seat's `leafDiagFrob_of_prodDiag`/`frobSq_of_diagonal` compose
(import foundation confirmed).
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- **The value invariant `Inv_val`** (ENTRY-WISE, team-lead steer (b)): the acc-threaded
prod-diagonalization, per prod-entry. `cleared s i` marks the diagonal positions the fold to `s` has
resolved; a cleared diagonal cell carries its `b`-monomial `bmon s w i`, a cleared off-diagonal cell
is `0`, an uncleared cell is the residual read `resid s w i j`. The three payload fields
(`cleared`/`bmon`/`resid`) are pinned during the build (`bmon` = the `z_{birthFlatCoord}` chain
product; `cleared`/`resid` from the ledger + the residual-coord reads). Base (`conRoot`): nothing
cleared, `resid = prod M w` (raw); maintenance: each step clears one diagonal position (α Schur);
terminal: all cleared ⟹ `prod = diagonal(bmon)`. -/
def InvVal (cleared : ConState L → Fin (M 0) → Prop) [∀ s i, Decidable (cleared s i)]
    (bmon : ConState L → Params M → Fin (M 0) → ℝ)
    (resid : ConState L → Params M → Fin (M 0) → Fin (M (Fin.last L)) → ℝ)
    (acc : Params M → Params M) (s : ConState L) : Prop :=
  ∀ (w : Params M) (i : Fin (M 0)) (j : Fin (M (Fin.last L))),
    prod M (acc w) i j
      = if cleared s i then (if (i : ℕ) = (j : ℕ) then bmon s w i else 0) else resid s w i j

/-- **Leaf discharge** (the terminal case → `LeafDiagFrob`, PROVEN structure): at a leaf `l` whose
state `s_leaf` has EVERY diagonal position cleared (`hall`), `InvVal` collapses to
`prod M (l.chartMap w) i j = if (i:ℕ)=(j:ℕ) then bmon s_leaf w i else 0` — the exact input of PROVEN
`leafDiagFrob_of_prodDiag`. Given the `b`-monomial factorization (`hbmon`: `bmon = (∏ divCoord)·ρ`,
counted) and the ratio properties (`hone`/`hbd`), this yields `LeafDiagFrob l`. The residual `resid`
is unused here (vacuous once all cleared), matching team-lead's leaf-assembly reason (iv). -/
theorem leafDiagFrob_of_invVal_leaf
    (cleared : ConState L → Fin (M 0) → Prop) [∀ s i, Decidable (cleared s i)]
    (bmon : ConState L → Params M → Fin (M 0) → ℝ)
    (resid : ConState L → Params M → Fin (M 0) → Fin (M (Fin.last L)) → ℝ)
    (l : LeafData M) (s_leaf : ConState L)
    (hinv : InvVal cleared bmon resid l.chartMap s_leaf)
    (hall : ∀ i : Fin (M 0), cleared s_leaf i)
    (ρ : Params M → Fin (M 0) → ℝ) (hi : ℝ)
    (hbmon : ∀ w ∈ l.srcBox, ∀ i : Fin (M 0),
      (if (i : ℕ) < M (Fin.last L) then bmon s_leaf w i else 0)
        = (∏ k : Fin l.numDiv, paramsEquivFlat M w (l.divCoord k)) * ρ w i)
    (hone : ∀ w ∈ l.srcBox, ∃ i : Fin (M 0), ρ w i = 1)
    (hbd : ∀ w ∈ l.srcBox, ∑ i : Fin (M 0), (ρ w i) ^ 2 ≤ hi) :
    LeafDiagFrob l := by
  refine leafDiagFrob_of_prodDiag l (fun w i => bmon s_leaf w i) ρ hi ?_ hbmon hone hbd
  intro w _ i j
  have := hinv w i j
  rwa [if_pos (hall i)] at this

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
